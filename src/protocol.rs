//! Serial core7 implementation with native suffix folding and a certified index.
//! Fixed classical proof interface; no runtime or side-channel privacy claim.
use crate::{
    codec::{g1_bytes, scalar_bytes, Reader},
    index::{Gate, ValidatedIndex},
    native::{self, Binding, Expr, NativeRelation, NativeSumcheck},
    pcs::{self, Commitment, Opening, OpeningProof, PublicSrs, SourceKind, VerificationKey},
    profile::ValidatedProfile,
    random::sample_fr,
    tables::{DenseMle, StructuredPolynomial},
    transcript::{canonical_context, ContextValue as C, Domain, Transcript},
    Result,
};
use crate::{
    gates,
    lookup::{self, LookupWitness},
};
use ark_bls12_381::{Fr, G1Affine, G2Affine};
use ark_ff::{Field, One, Zero};
use rand::RngCore;
use serde::Serialize;
use std::collections::BTreeMap;
use std::time::Instant;

pub const HEADER: &[u8; 5] = b"HP7\0\x01";
pub const TOTAL_HEADER: &[u8; 5] = b"HPT\0\x01";

#[derive(Clone, Copy, PartialEq, Eq)]
enum HelperConstraint {
    BothHalves,
    TotalOnly,
}

impl HelperConstraint {
    fn header(self) -> &'static [u8; 5] {
        match self {
            Self::BothHalves => HEADER,
            Self::TotalOnly => TOTAL_HEADER,
        }
    }

    fn fixes_endpoints(self, round: usize) -> bool {
        round == 0 && self == Self::BothHalves
    }

    fn round_scalars(self, p: &ValidatedProfile) -> usize {
        p.round_scalar_count() + usize::from(self == Self::TotalOnly)
    }
}
fn fixed(v: bool) -> Binding {
    Binding::Fixed(v)
}
fn variables(n: usize) -> Vec<Binding> {
    (0..n).map(Binding::Variable).collect()
}
fn chain(a: Vec<Binding>, b: Vec<Binding>) -> Vec<Binding> {
    a.into_iter().chain(b).collect()
}
fn padded(p: &ValidatedProfile, map: Vec<Binding>) -> Vec<Binding> {
    chain(vec![fixed(false); p.l() - map.len()], map)
}

pub fn context_bytes(
    p: &ValidatedProfile,
    index: &ValidatedIndex,
    public: &[Fr],
) -> Result<Vec<u8>> {
    global_context(p, index, public, HelperConstraint::BothHalves)
}

pub fn total_context_bytes(
    p: &ValidatedProfile,
    index: &ValidatedIndex,
    public: &[Fr],
) -> Result<Vec<u8>> {
    global_context(p, index, public, HelperConstraint::TotalOnly)
}

fn global_context(
    p: &ValidatedProfile,
    index: &ValidatedIndex,
    public: &[Fr],
    helper: HelperConstraint,
) -> Result<Vec<u8>> {
    if public.len() != 1 << p.public_log() {
        return Err("public input length".into());
    }
    let mut context = BTreeMap::new();
    context.insert(
        "protocol".into(),
        C::Text(
            if helper == HelperConstraint::TotalOnly {
                "global-total-sum-helper-rust-1"
            } else if p.flags() == crate::general_mask::PROFILE_FLAG {
                "core7-projected-universal-global-rust-1"
            } else if p.flags() < 2 && p.c() > 0 && p.nu() > 0 {
                "native-core7-geometric-global-rust-1"
            } else {
                "core-lookup-geometric-global-rust-2"
            }
            .into(),
        ),
    );
    context.insert("curve".into(), C::Text("BLS12-381".into()));
    context.insert("profile_id".into(), C::Text(p.profile_id().into()));
    context.insert(
        "E".into(),
        C::List(p.e().iter().map(|x| C::from(*x)).collect()),
    );
    context.insert(
        "D".into(),
        C::List(p.d().iter().map(|x| C::from(*x)).collect()),
    );
    context.insert("anchor".into(), C::from(p.anchor()));
    context.insert(
        "dimensions".into(),
        C::List(
            [p.nu(), p.c(), p.public_log(), p.degree(), p.l()]
                .into_iter()
                .map(C::from)
                .collect(),
        ),
    );
    context.insert(
        "public_index_commitments".into(),
        C::Map(
            index
                .commitments()
                .iter()
                .map(|(n, c)| (n.clone(), C::Bytes(crate::codec::g2_bytes(c).to_vec())))
                .collect(),
        ),
    );
    context.insert(
        "certified_index_digest".into(),
        C::Bytes(index.digest().to_vec()),
    );
    context.insert("gate".into(), C::Text(index.gate().name().into()));
    if let Some(lk) = index.lookup() {
        context.insert("lookup_function".into(), C::Text(lk.function.name().into()));
        context.insert("table_cycle".into(), C::from(lk.table_cycle.polynomial()));
        context.insert("h_cycle".into(), C::from(lk.h_cycle.polynomial()));
    }
    context.insert(
        "public_input".into(),
        C::List(public.iter().copied().map(C::from).collect()),
    );
    context.insert("srs_id".into(), C::Bytes(index.srs_id().to_vec()));
    context.insert(
        "root_observation".into(),
        C::Text(
            if p.lookup() {
                "AminusB-and-CminusE-only"
            } else if p.m() == 0 {
                "no-product-root"
            } else {
                "AminusB-only"
            }
            .into(),
        ),
    );
    context.insert(
        "pairing_stage".into(),
        C::Text("complete-proof-after-all-openings".into()),
    );
    canonical_context(&context)
}

pub fn relations(p: &ValidatedProfile, gate: Gate, beta: Fr, gamma: Fr) -> Vec<NativeRelation> {
    let (l, m, nu, c, k) = (p.l(), p.m(), p.nu(), p.c(), p.k());
    let mut result = vec![];
    let mut gate_rel = NativeRelation::new(nu + 1);
    let mut gate_expr = Expr::constant(0);
    let mut w = vec![];
    let qmap = chain(
        vec![fixed(false); l - nu],
        (1..=nu).map(Binding::Variable).collect(),
    );
    for a in 0..k {
        let q = gate_rel.source(&format!("q{a}"), qmap.clone());
        let map = padded(
            p,
            std::iter::once(Binding::Variable(0))
                .chain((0..c).map(|i| fixed(((a >> (c - 1 - i)) & 1) != 0)))
                .chain((1..=nu).map(Binding::Variable))
                .collect(),
        );
        let v = gate_rel.source("W", map);
        w.push(v.clone());
        gate_expr = gate_expr.plus(q.times(v.power(p.degree() as u64)));
    }
    gate_expr = gate_expr.minus(gate_rel.source("qout", qmap.clone()));
    if gate == Gate::FixedThirteen {
        for (i, (a, b)) in [(0, 1), (2, 3), (4, 5), (0, 6)].iter().enumerate() {
            gate_expr = gate_expr.plus(
                gate_rel
                    .source(&format!("q{}", 8 + i), qmap.clone())
                    .times(w[*a].clone())
                    .times(w[*b].clone()),
            );
        }
    }
    gate_rel.expression = Expr::constant(1).minus(Expr::Variable(0)).times(gate_expr);
    if let Some(descriptor) = gate.descriptor(p).expect("certified gate descriptor") {
        gate_rel = descriptor
            .native_relation(l, nu, c)
            .expect("certified gate layout");
    }
    result.push(gate_rel);
    if !p.virtual_public() {
        let mut r = NativeRelation::new(p.ell());
        let w = r.source("W", padded(p, variables(p.ell())));
        let pi = r.source("__public", padded(p, variables(p.ell())));
        r.expression = w
            .minus(pi)
            .times(native::eq_zero(0..p.ell() - p.public_log()));
        result.push(r);
    }
    if m > 0 {
        for name in ["A", "B"] {
            let mut r = NativeRelation::new(m);
            let tree = r.source(name, padded(p, chain(vec![fixed(true)], variables(m))));
            let witness = r.source("W", padded(p, chain(vec![fixed(false)], variables(m))));
            let labels = if name == "A" {
                (0..m).fold(Expr::constant(0), |a, i| {
                    a.plus(Expr::Constant(Fr::from((1u64) << (m - 1 - i))).times(Expr::Variable(i)))
                })
            } else {
                r.source("sigma", padded(p, chain(vec![fixed(false)], variables(m))))
            };
            r.expression = tree
                .minus(witness)
                .minus(Expr::Constant(beta).times(labels))
                .minus(Expr::Constant(gamma));
            result.push(r);
        }
        for name in ["A", "B"] {
            let mut r = NativeRelation::new(m);
            let parent = r.source(name, padded(p, chain(vec![fixed(false)], variables(m))));
            let left = r.source(name, padded(p, chain(variables(m), vec![fixed(false)])));
            let right = r.source(name, padded(p, chain(variables(m), vec![fixed(true)])));
            r.expression = Expr::constant(1)
                .minus(native::eq_zero(0..m))
                .times(parent.minus(left.times(right)));
            result.push(r);
        }
        let mut root = NativeRelation::new(p.ell());
        root.expression = root
            .source("AminusB", padded(p, variables(p.ell())))
            .times(native::eq_zero(0..m))
            .times(Expr::Variable(m));
        result.push(root);
    }
    if p.virtual_public() {
        gates::virtualize_witness_uses(&mut result, p.l(), p.public_log())
            .expect("validated public slice");
    }
    result
}

fn all_relations(
    p: &ValidatedProfile,
    index: &ValidatedIndex,
    beta: Fr,
    gamma: Fr,
    lookup_beta: Fr,
    lookup_gamma: Fr,
) -> Result<Vec<NativeRelation>> {
    let mut result = relations(p, index.gate(), beta, gamma);
    if let Some(lk) = index.lookup() {
        result.extend(lookup::relations(
            p,
            lk.function,
            &lk.table_cycle,
            &lk.h_cycle,
            lookup_beta,
            lookup_gamma,
        )?);
    }
    Ok(result)
}
fn joint_root(r: &NativeRelation) -> bool {
    r.sources
        .iter()
        .any(|s| s.handle == "AminusB" || s.handle == "CminusE")
}
fn commitment_bytes(p: &ValidatedProfile) -> usize {
    336 + if p.lookup() { 288 } else { 0 }
}

fn packet(tx: &mut Transcript, relations: &mut [NativeRelation]) -> Result<Fr> {
    let count = relations
        .iter()
        .filter(|r| !joint_root(r))
        .map(|r| r.dimension)
        .sum::<usize>()
        + relations.len()
        - 1;
    let mut domains = vec![Domain::Field; count];
    domains.push(Domain::Nonzero);
    let values = tx.challenge_mixed("global_packet", &domains)?;
    let mut it = values.into_iter();
    for r in relations.iter_mut() {
        if !joint_root(r) {
            r.tau = Some((0..r.dimension).map(|_| it.next().unwrap()).collect());
        }
    }
    for (i, r) in relations.iter_mut().enumerate() {
        r.weight = if i == 0 {
            Fr::one()
        } else {
            it.next().unwrap()
        };
    }
    Ok(it.next().unwrap())
}
fn combined(
    path: &[Fr],
    rels: &[NativeRelation],
    get: &mut impl FnMut(&str, &[Fr]) -> Result<Fr>,
) -> Result<Fr> {
    let mut total = Fr::zero();
    for r in rels {
        let off = path.len() - r.dimension;
        let pad = path[..off].iter().map(|v| Fr::one() - v).product::<Fr>();
        total += pad * r.evaluate(&path[off..], get)?;
    }
    Ok(total)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Query {
    pub(crate) handle: String,
    pub(crate) point: Vec<Fr>,
}
pub(crate) fn queries(path: &[Fr], rels: &[NativeRelation]) -> Vec<Query> {
    let mut out = vec![];
    for r in rels {
        for s in &r.sources {
            if s.handle == "__public" {
                continue;
            }
            let q = Query {
                handle: s.handle.clone(),
                point: s.point(&path[path.len() - r.dimension..]),
            };
            if !out.contains(&q) {
                out.push(q);
            }
        }
    }
    out
}
pub(crate) struct Bucket {
    pub(crate) kind: SourceKind,
    pub(crate) point: Vec<Fr>,
    pub(crate) queries: Vec<usize>,
}
pub(crate) fn buckets(queries: &[Query]) -> Vec<Bucket> {
    let mut out: Vec<Bucket> = vec![];
    for (i, q) in queries.iter().enumerate() {
        let kind = if q.handle == "helper" || q.handle.starts_with("multi_helper/") {
            SourceKind::Helper
        } else {
            SourceKind::Source
        };
        if let Some(b) = out
            .iter_mut()
            .find(|b| b.kind == kind && b.point == q.point)
        {
            b.queries.push(i)
        } else {
            out.push(Bucket {
                kind,
                point: q.point.clone(),
                queries: vec![i],
            });
        }
    }
    out
}
pub(crate) fn bucket_weights(tx: &mut Transcript, buckets: &[Bucket]) -> Result<Vec<Vec<Fr>>> {
    let count = buckets.iter().map(|b| b.queries.len() - 1).sum::<usize>();
    let mut it = tx
        .challenge("same_point_batch", count.max(1), Domain::Field)?
        .into_iter();
    Ok(buckets
        .iter()
        .map(|b| {
            std::iter::once(Fr::one())
                .chain((1..b.queries.len()).map(|_| it.next().unwrap()))
                .collect()
        })
        .collect())
}

fn add_extra(extras: &mut BTreeMap<Vec<usize>, Fr>, e: Vec<usize>, c: Fr) {
    *extras.entry(e).or_default() += c;
}
fn axis(l: usize, a: usize, e: usize) -> Vec<usize> {
    let mut v = vec![0; l];
    v[a] = e;
    v
}
pub(crate) fn witness_poly(
    p: &ValidatedProfile,
    witness: &[Fr],
    rng: &mut impl RngCore,
) -> Result<StructuredPolynomial> {
    if witness.len() != p.n_total() {
        return Err("witness length mismatch".into());
    }
    let mut table = witness.to_vec();
    table.resize(2 * witness.len(), Fr::zero());
    if p.flags() == crate::general_mask::PROFILE_FLAG {
        return projected_source(p, table, crate::general_mask::Source::Witness, rng);
    }
    let mut extras = BTreeMap::new();
    let start = p.core_offset();
    for i in 0..p.k() {
        let coin = sample_fr(rng)?;
        let mut a = vec![0; p.l()];
        for j in 0..p.c() {
            a[start + 1 + j] = (i >> (p.c() - 1 - j)) & 1;
        }
        a[start] = 2;
        add_extra(&mut extras, a.clone(), coin);
        a[start] = 1;
        add_extra(&mut extras, a, -coin);
    }
    if p.c() > 0 {
        for z in 0..=usize::from(!p.virtual_public()) {
            let coin = sample_fr(rng)?;
            let mut a = axis(p.l(), start + p.anchor(), 2);
            a[start] = z;
            add_extra(&mut extras, a.clone(), coin);
            a[start + p.anchor()] = 1;
            add_extra(&mut extras, a, -coin);
        }
    } else if p.nu() > 0 {
        let coin = sample_fr(rng)?;
        add_extra(&mut extras, axis(p.l(), p.l() - 1, 2), coin);
        add_extra(&mut extras, axis(p.l(), p.l() - 1, 1), -coin);
    }
    let source = StructuredPolynomial::new(
        p.l(),
        StructuredPolynomial::from_table(p.l(), start, DenseMle::new(table)?)?
            .terms()
            .to_vec(),
        extras,
    )?;
    if p.lookup() {
        source.add(&lookup::witness_mask(p, rng)?)
    } else {
        Ok(source)
    }
}
pub(crate) fn tree_poly(
    p: &ValidatedProfile,
    leaves: Vec<Fr>,
    root_noise: bool,
    rng: &mut impl RngCore,
) -> Result<StructuredPolynomial> {
    let n = leaves.len();
    let mut heap = vec![Fr::zero(); 2 * n];
    heap[n..].copy_from_slice(&leaves);
    for i in (1..n).rev() {
        heap[i] = heap[2 * i] * heap[2 * i + 1];
    }
    if p.flags() == crate::general_mask::PROFILE_FLAG {
        return projected_source(p, heap, crate::general_mask::Source::Tree, rng);
    }
    let mut extras = BTreeMap::new();
    let start = p.core_offset();
    let last = p.l() - 1;
    for (z, y) in [(0, 2), (1, 2), (2, 0), (2, 1)] {
        let coin = sample_fr(rng)?;
        let mut e = vec![0; p.l()];
        e[start] = z;
        e[last] = y;
        add_extra(&mut extras, e.clone(), coin);
        if y == 2 {
            e[last] = 1
        } else {
            e[start] = 1
        }
        add_extra(&mut extras, e, -coin);
    }
    if root_noise {
        let coin = sample_fr(rng)?;
        for (z, y, sign) in [(2, 2, 1i32), (2, 1, -1), (1, 2, -1), (1, 1, 1)] {
            let mut e = vec![0; p.l()];
            e[start] = z;
            e[last] = y;
            add_extra(&mut extras, e, if sign == 1 { coin } else { -coin });
        }
    }
    StructuredPolynomial::new(
        p.l(),
        StructuredPolynomial::from_table(p.l(), start, DenseMle::new(heap)?)?
            .terms()
            .to_vec(),
        extras,
    )
}
fn projected_source(
    p: &ValidatedProfile,
    table: Vec<Fr>,
    role: crate::general_mask::Source,
    rng: &mut impl RngCore,
) -> Result<StructuredPolynomial> {
    let dense = StructuredPolynomial::from_table(p.l(), p.core_offset(), DenseMle::new(table)?)?;
    StructuredPolynomial::new(
        p.l(),
        dense.terms().to_vec(),
        crate::general_mask::sample(p, role, rng)?,
    )
}
fn helper_poly(
    p: &ValidatedProfile,
    rng: &mut impl RngCore,
    constraint: HelperConstraint,
) -> Result<StructuredPolynomial> {
    let mut extras = BTreeMap::new();
    let inv2 = Fr::from(2u64).inverse().unwrap();
    for (a, cap) in p.e().iter().enumerate() {
        for e in if a == 0 { 2 } else { 1 }..=*cap {
            let coin = sample_fr(rng)?;
            add_extra(&mut extras, axis(p.l(), a, e), coin);
            add_extra(
                &mut extras,
                if a == 0 {
                    axis(p.l(), 0, 1)
                } else {
                    vec![0; p.l()]
                },
                -coin * if a == 0 { Fr::one() } else { inv2 },
            );
        }
    }
    if constraint == HelperConstraint::TotalOnly {
        let coin = sample_fr(rng)?;
        add_extra(&mut extras, axis(p.l(), 0, 1), coin);
        add_extra(&mut extras, vec![0; p.l()], -coin * inv2);
    }
    StructuredPolynomial::new(p.l(), vec![], extras)
}

#[derive(Clone, Debug, Serialize)]
pub struct Metrics {
    pub seconds: f64,
    pub proof_bytes: usize,
    pub round_scalars: usize,
    pub source_values: usize,
    pub opening_count: usize,
    pub hash_packets: u64,
    pub fold_pairs: usize,
    pub sample_points: usize,
    pub offsets: BTreeMap<String, usize>,
    /// Disjoint wall-clock intervals. These add to the measured operation time
    /// up to final bookkeeping; nested diagnostic timers are never added here.
    pub stages: BTreeMap<String, f64>,
    pub opening_cache: BTreeMap<String, usize>,
}
fn stage(stages: &mut BTreeMap<String, f64>, checkpoint: &mut Instant, name: &str) {
    let now = Instant::now();
    stages.insert(name.into(), now.duration_since(*checkpoint).as_secs_f64());
    *checkpoint = now;
}
pub fn prove(
    srs: &PublicSrs,
    index: &ValidatedIndex,
    public: &[Fr],
    witness: &[Fr],
    rng: &mut impl RngCore,
) -> Result<(Vec<u8>, Metrics)> {
    prove_with_options(srs, index, public, witness, rng, ProverOptions::default())
}
#[derive(Clone, Copy, Debug)]
pub struct ProverOptions {
    pub cache_openings: bool,
}
impl Default for ProverOptions {
    fn default() -> Self {
        Self {
            cache_openings: true,
        }
    }
}
pub fn prove_with_options(
    srs: &PublicSrs,
    index: &ValidatedIndex,
    public: &[Fr],
    witness: &[Fr],
    rng: &mut impl RngCore,
    options: ProverOptions,
) -> Result<(Vec<u8>, Metrics)> {
    prove_global(
        srs,
        index,
        public,
        witness,
        rng,
        options,
        HelperConstraint::BothHalves,
    )
}

pub fn prove_total(
    srs: &PublicSrs,
    index: &ValidatedIndex,
    public: &[Fr],
    witness: &[Fr],
    rng: &mut impl RngCore,
    options: ProverOptions,
) -> Result<(Vec<u8>, Metrics)> {
    prove_global(
        srs,
        index,
        public,
        witness,
        rng,
        options,
        HelperConstraint::TotalOnly,
    )
}

fn prove_global(
    srs: &PublicSrs,
    index: &ValidatedIndex,
    public: &[Fr],
    witness: &[Fr],
    rng: &mut impl RngCore,
    options: ProverOptions,
    constraint: HelperConstraint,
) -> Result<(Vec<u8>, Metrics)> {
    let start = Instant::now();
    let mut checkpoint = start;
    let mut stages = BTreeMap::new();
    let p = srs.profile();
    if !index.matches(p, &srs.vk().srs_digest) {
        return Err("index/SRS/profile mismatch".into());
    }
    if !p.virtual_public() && witness.get(..public.len()) != Some(public) {
        return Err("witness differs from public prefix".into());
    }
    let semantic = gates::semantic_witness(witness, public)?;
    let mut salt = [0; 32];
    rng.try_fill_bytes(&mut salt).map_err(|e| e.to_string())?;
    let mut tx = Transcript::new(&global_context(p, index, public, constraint)?, salt);
    let mut wire = constraint.header().to_vec();
    wire.extend(salt);
    let mut offsets = BTreeMap::new();
    let mut polys = index.polynomials().clone();
    let mut blinds: BTreeMap<String, Fr> = index
        .commitments()
        .keys()
        .map(|n| (n.clone(), Fr::zero()))
        .collect();
    let mut commits: BTreeMap<String, Commitment> = index
        .commitments()
        .iter()
        .map(|(n, c)| (n.clone(), Commitment::Source(*c)))
        .collect();
    polys.insert("W".into(), witness_poly(p, witness, rng)?);
    let blind = sample_fr(rng)?;
    blinds.insert("W".into(), blind);
    let cw = pcs::commit(srs, &polys["W"], SourceKind::Source, blind)?;
    commits.insert("W".into(), cw);
    offsets.insert("witness".into(), wire.len());
    let block = cw.bytes();
    wire.extend(&block);
    tx.absorb("witness", &block)?;
    stage(&mut stages, &mut checkpoint, "witness_context_commitment");
    let lookup_witness = if let Some(lk) = index.lookup() {
        let data = LookupWitness::new(p, &lk.physical_table, &semantic, lk.function, rng)?;
        let blind = sample_fr(rng)?;
        let ch = pcs::commit(srs, &data.h_source, SourceKind::Source, blind)?;
        offsets.insert("lookup_helper".into(), wire.len());
        let block = ch.bytes();
        wire.extend(&block);
        tx.absorb("lookup_helper", &block)?;
        polys.insert("H".into(), data.h_source.clone());
        blinds.insert("H".into(), blind);
        commits.insert("H".into(), ch);
        stage(
            &mut stages,
            &mut checkpoint,
            "lookup_addresses_h_commitment",
        );
        Some(data)
    } else {
        None
    };
    let fingerprint = if p.lookup() {
        tx.challenge_mixed(
            "joint_fingerprints",
            &[
                Domain::Nonzero,
                Domain::Field,
                Domain::Field,
                Domain::Nonzero,
            ],
        )?
    } else {
        tx.challenge_mixed("copy_fingerprint", &[Domain::Nonzero, Domain::Field])?
    };
    let (beta, gamma) = (fingerprint[0], fingerprint[1]);
    let (lookup_beta, lookup_gamma) = if p.lookup() {
        (fingerprint[2], fingerprint[3])
    } else {
        (Fr::zero(), Fr::one())
    };
    stage(&mut stages, &mut checkpoint, "fingerprints");
    offsets.insert("trees".into(), wire.len());
    let mut block = vec![];
    for name in ["A", "B"] {
        let leaves = semantic
            .iter()
            .enumerate()
            .map(|(i, w)| {
                *w + beta * Fr::from(if name == "A" { i } else { index.wiring()[i] } as u64) + gamma
            })
            .collect();
        let poly = if p.m() > 0 {
            tree_poly(p, leaves, name == "A", rng)?
        } else {
            StructuredPolynomial::zero(p.l())?
        };
        let blind = if p.m() > 0 {
            sample_fr(rng)?
        } else {
            Fr::zero()
        };
        let commit = pcs::commit(srs, &poly, SourceKind::Source, blind)?;
        block.extend(commit.bytes());
        polys.insert(name.into(), poly);
        blinds.insert(name.into(), blind);
        commits.insert(name.into(), commit);
    }
    wire.extend(&block);
    tx.absorb("trees", &block)?;
    polys.insert(
        "AminusB".into(),
        polys["A"].add(&polys["B"].scaled(-Fr::one()))?,
    );
    blinds.insert("AminusB".into(), blinds["A"] - blinds["B"]);
    commits.insert(
        "AminusB".into(),
        commits["A"].add(&commits["B"].scale(-Fr::one()))?,
    );
    if let Some(lk) = lookup_witness {
        let (left, right) = lk.leaves(lookup_beta, lookup_gamma)?;
        let mut block = vec![];
        offsets.insert("lookup_trees".into(), wire.len());
        for (name, leaves, root_noise) in [("C", left, true), ("E", right, false)] {
            let poly = lookup::masked_tree(p, &leaves, root_noise, rng)?;
            let blind = sample_fr(rng)?;
            let commit = pcs::commit(srs, &poly, SourceKind::Source, blind)?;
            block.extend(commit.bytes());
            polys.insert(name.into(), poly);
            blinds.insert(name.into(), blind);
            commits.insert(name.into(), commit);
        }
        wire.extend(&block);
        tx.absorb("lookup_trees", &block)?;
        polys.insert(
            "CminusE".into(),
            polys["C"].add(&polys["E"].scaled(-Fr::one()))?,
        );
        blinds.insert("CminusE".into(), blinds["C"] - blinds["E"]);
        commits.insert(
            "CminusE".into(),
            commits["C"].add(&commits["E"].scale(-Fr::one()))?,
        );
    }
    let helper = helper_poly(p, rng, constraint)?;
    let blind = sample_fr(rng)?;
    let ch = pcs::commit(srs, &helper, SourceKind::Helper, blind)?;
    blinds.insert("helper".into(), blind);
    polys.insert("helper".into(), helper.clone());
    commits.insert("helper".into(), ch);
    offsets.insert("helper".into(), wire.len());
    let block = ch.bytes();
    wire.extend(&block);
    tx.absorb("helper", &block)?;
    let mut rels = all_relations(p, index, beta, gamma, lookup_beta, lookup_gamma)?;
    let rho = packet(&mut tx, &mut rels)?;
    stage(&mut stages, &mut checkpoint, "trees_helper_commitments");
    polys.insert(
        "__public".into(),
        StructuredPolynomial::from_table(
            p.l(),
            p.l() - p.public_log(),
            DenseMle::new(public.to_vec())?,
        )?,
    );
    let mut engine = NativeSumcheck::new(p.l(), rels.clone(), &polys, helper, rho)?;
    stage(&mut stages, &mut checkpoint, "native_compile_and_precheck");
    let mut path = vec![];
    let mut current = Fr::zero();
    offsets.insert("rounds".into(), wire.len());
    for (a, cap) in p.e().iter().enumerate() {
        let samples = (0..=*cap)
            .map(|i| engine.round_value(Fr::from(i as u64)))
            .collect::<Vec<_>>();
        let coeffs = native::interpolate(&samples)?;
        for x in [
            Fr::from((*cap + 1) as u64),
            Fr::from((*cap + 2) as u64),
            -Fr::one(),
        ] {
            if native::univariate(&coeffs, x) != engine.round_value(x) {
                return Err("honest expression exceeds sending cap".into());
            }
        }
        let fixed_ends = constraint.fixes_endpoints(a);
        if fixed_ends {
            if !coeffs[0].is_zero() || !native::univariate(&coeffs, Fr::one()).is_zero() {
                return Err("first half sum is nonzero".into());
            }
        } else if coeffs[0] + native::univariate(&coeffs, Fr::one()) != current {
            return Err("sumcheck recurrence".into());
        }
        let block = coeffs[if fixed_ends { 2 } else { 1 }..]
            .iter()
            .flat_map(scalar_bytes)
            .collect::<Vec<_>>();
        wire.extend(&block);
        tx.absorb(&format!("round_{a}"), &block)?;
        let r = tx.challenge(&format!("round_challenge_{a}"), 1, Domain::Nonboolean)?[0];
        current = native::univariate(&coeffs, r);
        path.push(r);
        engine.fold(r);
    }
    stage(&mut stages, &mut checkpoint, "sumcheck_rounds");
    let fold_pairs = engine.fold_pairs;
    let sample_points = engine.sample_points;
    drop(engine);
    let mut ordered = queries(&path, &rels);
    let mut values = ordered
        .iter()
        .map(|q| polys[&q.handle].evaluate(&q.point))
        .collect::<Result<Vec<_>>>()?;
    offsets.insert("values".into(), wire.len());
    let block = values.iter().flat_map(scalar_bytes).collect::<Vec<_>>();
    wire.extend(&block);
    tx.absorb("endpoint_values", &block)?;
    let terminal = combined(&path, &rels, &mut |h, z| polys[h].evaluate(z))?;
    let derived = (current - terminal) * rho.inverse().unwrap();
    if derived != polys["helper"].evaluate(&path)? {
        return Err("helper endpoint mismatch".into());
    }
    ordered.push(Query {
        handle: "helper".into(),
        point: path,
    });
    values.push(derived);
    let buckets = buckets(&ordered);
    let alphas = bucket_weights(&mut tx, &buckets)?;
    stage(&mut stages, &mut checkpoint, "endpoint_and_batching");
    offsets.insert("openings".into(), wire.len());
    let mut opening_cache = pcs::OpeningCache::new(srs);
    for (b, weights) in buckets.iter().zip(&alphas) {
        let mut poly = StructuredPolynomial::zero(p.l())?;
        let mut blind = Fr::zero();
        for (i, alpha) in b.queries.iter().zip(weights) {
            poly = poly.add(&polys[&ordered[*i].handle].scaled(*alpha))?;
            blind += blinds[&ordered[*i].handle] * *alpha;
        }
        let opening = if options.cache_openings {
            pcs::open_cached(srs, &poly, b.kind, &b.point, blind, rng, &mut opening_cache)?
        } else {
            pcs::open_polynomial(srs, &poly, b.kind, &b.point, blind, rng)?
        };
        for point in opening.points {
            wire.extend(g1_bytes(&point));
        }
    }
    stage(
        &mut stages,
        &mut checkpoint,
        "opening_quotients_msm_encoding",
    );
    tx.absorb("all_openings", &wire[offsets["openings"]..])?;
    tx.challenge("pairing_batch", buckets.len(), Domain::Field)?;
    let source_values = ordered.len() - 1;
    let expected = 37
        + commitment_bytes(p)
        + 32 * (constraint.round_scalars(p) + source_values)
        + 48 * buckets.len() * (p.l() + 1);
    if wire.len() != expected {
        return Err("communication ledger mismatch".into());
    }
    stage(&mut stages, &mut checkpoint, "final_transcript_and_ledger");
    let metrics = Metrics {
        seconds: start.elapsed().as_secs_f64(),
        proof_bytes: wire.len(),
        round_scalars: constraint.round_scalars(p),
        source_values,
        opening_count: buckets.len(),
        hash_packets: tx.query_count() as u64,
        fold_pairs,
        sample_points,
        offsets,
        stages,
        opening_cache: BTreeMap::from([
            ("hits".into(), opening_cache.hits),
            ("misses".into(), opening_cache.misses),
            ("msm_cells".into(), opening_cache.msm_cells),
        ]),
    };
    Ok((wire, metrics))
}

pub fn verify(
    vk: &VerificationKey,
    p: &ValidatedProfile,
    index: &ValidatedIndex,
    public: &[Fr],
    proof: &[u8],
    aggregate: bool,
) -> Result<Metrics> {
    verify_global(
        vk,
        p,
        index,
        public,
        proof,
        aggregate,
        HelperConstraint::BothHalves,
    )
}

pub fn verify_total(
    vk: &VerificationKey,
    p: &ValidatedProfile,
    index: &ValidatedIndex,
    public: &[Fr],
    proof: &[u8],
    aggregate: bool,
) -> Result<Metrics> {
    verify_global(
        vk,
        p,
        index,
        public,
        proof,
        aggregate,
        HelperConstraint::TotalOnly,
    )
}

fn verify_global(
    vk: &VerificationKey,
    p: &ValidatedProfile,
    index: &ValidatedIndex,
    public: &[Fr],
    proof: &[u8],
    aggregate: bool,
    constraint: HelperConstraint,
) -> Result<Metrics> {
    let start = Instant::now();
    let mut checkpoint = start;
    let mut stages = BTreeMap::new();
    if vk.dimension != p.l() || !index.matches(p, &vk.srs_digest) {
        return Err("index/SRS/profile mismatch".into());
    }
    let templates = all_relations(p, index, Fr::one(), Fr::zero(), Fr::one(), Fr::one())?;
    let max_values = templates
        .iter()
        .map(|r| r.sources.iter().filter(|s| s.handle != "__public").count())
        .sum::<usize>();
    let max_bytes = 37
        + commitment_bytes(p)
        + 32 * (constraint.round_scalars(p) + max_values)
        + 48 * (max_values + 1) * (p.l() + 1);
    if proof.len() > max_bytes {
        return Err("proof exceeds format bound".into());
    }
    let mut rd = Reader::new(proof);
    if rd.bytes(5)? != constraint.header() {
        return Err("proof header".into());
    }
    let salt: [u8; 32] = rd.bytes(32)?.try_into().unwrap();
    let mut tx = Transcript::new(&global_context(p, index, public, constraint)?, salt);
    let mut commits: BTreeMap<String, Commitment> = index
        .commitments()
        .iter()
        .map(|(n, c)| (n.clone(), Commitment::Source(*c)))
        .collect();
    let off = rd.position();
    commits.insert("W".into(), Commitment::Source(rd.g2()?));
    tx.absorb("witness", &proof[off..rd.position()])?;
    if p.lookup() {
        let off = rd.position();
        commits.insert("H".into(), Commitment::Source(rd.g2()?));
        tx.absorb("lookup_helper", &proof[off..rd.position()])?;
    }
    let fingerprint = if p.lookup() {
        tx.challenge_mixed(
            "joint_fingerprints",
            &[
                Domain::Nonzero,
                Domain::Field,
                Domain::Field,
                Domain::Nonzero,
            ],
        )?
    } else {
        tx.challenge_mixed("copy_fingerprint", &[Domain::Nonzero, Domain::Field])?
    };
    let (beta, gamma) = (fingerprint[0], fingerprint[1]);
    let (lookup_beta, lookup_gamma) = if p.lookup() {
        (fingerprint[2], fingerprint[3])
    } else {
        (Fr::zero(), Fr::one())
    };
    let off = rd.position();
    for name in ["A", "B"] {
        commits.insert(name.into(), Commitment::Source(rd.g2()?));
    }
    if p.m() == 0
        && (commits["A"] != Commitment::Source(G2Affine::identity())
            || commits["B"] != Commitment::Source(G2Affine::identity()))
    {
        return Err("N=1 dummy tree commitments must be identity".into());
    }
    tx.absorb("trees", &proof[off..rd.position()])?;
    commits.insert(
        "AminusB".into(),
        commits["A"].add(&commits["B"].scale(-Fr::one()))?,
    );
    if p.lookup() {
        let off = rd.position();
        for name in ["C", "E"] {
            commits.insert(name.into(), Commitment::Source(rd.g2()?));
        }
        tx.absorb("lookup_trees", &proof[off..rd.position()])?;
        commits.insert(
            "CminusE".into(),
            commits["C"].add(&commits["E"].scale(-Fr::one()))?,
        );
    }
    let off = rd.position();
    commits.insert("helper".into(), Commitment::Helper(rd.g1()?));
    tx.absorb("helper", &proof[off..rd.position()])?;
    let mut rels = all_relations(p, index, beta, gamma, lookup_beta, lookup_gamma)?;
    let rho = packet(&mut tx, &mut rels)?;
    stage(
        &mut stages,
        &mut checkpoint,
        "context_commitment_decode_and_transcript",
    );
    let (mut path, mut current) = (vec![], Fr::zero());
    let inv2 = Fr::from(2u64).inverse().unwrap();
    for (a, cap) in p.e().iter().enumerate() {
        let off = rd.position();
        let fixed_ends = constraint.fixes_endpoints(a);
        let payload = (0..if fixed_ends { cap - 1 } else { *cap })
            .map(|_| rd.scalar())
            .collect::<Result<Vec<_>>>()?;
        let sum: Fr = payload.iter().sum();
        let mut coeffs = if fixed_ends {
            vec![Fr::zero(), -sum]
        } else {
            vec![(current - sum) * inv2]
        };
        coeffs.extend(payload);
        tx.absorb(&format!("round_{a}"), &proof[off..rd.position()])?;
        let r = tx.challenge(&format!("round_challenge_{a}"), 1, Domain::Nonboolean)?[0];
        path.push(r);
        current = native::univariate(&coeffs, r);
    }
    stage(&mut stages, &mut checkpoint, "sumcheck_transcript");
    let mut ordered = queries(&path, &rels);
    let off = rd.position();
    let mut values = (0..ordered.len())
        .map(|_| rd.scalar())
        .collect::<Result<Vec<_>>>()?;
    tx.absorb("endpoint_values", &proof[off..rd.position()])?;
    let public_poly = DenseMle::new(public.to_vec())?;
    let terminal = combined(&path, &rels, &mut |h, z| {
        if h == "__public" {
            public_poly.evaluate(&z[p.l() - p.public_log()..])
        } else {
            let i = ordered
                .iter()
                .position(|q| q.handle == h && q.point == z)
                .ok_or("unregistered endpoint query")?;
            Ok(values[i])
        }
    })?;
    ordered.push(Query {
        handle: "helper".into(),
        point: path,
    });
    values.push((current - terminal) * rho.inverse().unwrap());
    let buckets = buckets(&ordered);
    let alphas = bucket_weights(&mut tx, &buckets)?;
    stage(
        &mut stages,
        &mut checkpoint,
        "endpoint_relation_and_batching",
    );
    let off = rd.position();
    let mut openings = vec![];
    for (b, weights) in buckets.iter().zip(&alphas) {
        let mut commit = if b.kind == SourceKind::Source {
            Commitment::Source(G2Affine::identity())
        } else {
            Commitment::Helper(G1Affine::identity())
        };
        let mut y = Fr::zero();
        for (i, alpha) in b.queries.iter().zip(weights) {
            commit = commit.add(&commits[&ordered[*i].handle].scale(*alpha))?;
            y += values[*i] * *alpha;
        }
        let points = (0..=p.l()).map(|_| rd.g1()).collect::<Result<Vec<_>>>()?;
        openings.push(Opening {
            commitment: commit,
            point: b.point.clone(),
            value: y,
            proof: OpeningProof { points },
        });
    }
    rd.finish()?;
    tx.absorb("all_openings", &proof[off..])?;
    let weights = tx.challenge("pairing_batch", openings.len(), Domain::Field)?;
    stage(
        &mut stages,
        &mut checkpoint,
        "opening_decode_msm_and_transcript",
    );
    let accepted = if aggregate {
        pcs::cross_bucket_verify(vk, &openings, &weights)
    } else {
        openings.iter().all(|o| pcs::verify_opening(vk, o))
    };
    if !accepted {
        return Err("PCS verification failed".into());
    }
    stage(&mut stages, &mut checkpoint, "pcs_equations");
    Ok(Metrics {
        seconds: start.elapsed().as_secs_f64(),
        proof_bytes: proof.len(),
        round_scalars: constraint.round_scalars(p),
        source_values: ordered.len() - 1,
        opening_count: openings.len(),
        hash_packets: tx.query_count() as u64,
        fold_pairs: 0,
        sample_points: 0,
        offsets: BTreeMap::new(),
        stages,
        opening_cache: BTreeMap::new(),
    })
}
