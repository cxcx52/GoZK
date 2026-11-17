//! B1-seven-trace: genuine historical repair with seven independent helpers,
//! shared prefix challenges, complete round coefficients and same-point PCS
//! aggregation. The gate descriptor and transcript codec are versioned ports;
//! this is not a claim of byte compatibility with the archived Python HP6.
use crate::{
    codec::{g1_bytes, g2_bytes, scalar_bytes, Reader},
    index::{Gate, IndexSpec},
    native::{self, Binding, Expr, NativeRelation},
    pcs::{self, Commitment, Opening, OpeningProof, SourceKind, VerificationKey},
    random::sample_fr,
    tables::{DenseMle, StructuredPolynomial},
    trace::{ExtensionField, TraceMask},
    trace_native::TraceSumcheck,
    trace_pcs::{self, TraceParameters, TraceSource, ValidatedTraceSrs},
    transcript::{canonical_context, ContextValue as C, Domain, Transcript},
    Result,
};
use ark_bls12_381::{Fr, G2Affine};
use ark_ff::{Field, One, Zero};
use rand::RngCore;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
    time::Instant,
};

pub const HEADER: &[u8; 5] = b"HB1\0\x01";
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceProfile {
    nu: usize,
    c: usize,
    public_log: usize,
    degree: usize,
    pcs: TraceParameters,
}
impl TraceProfile {
    pub fn new(nu: usize, c: usize, public_log: usize, degree: usize) -> Result<Self> {
        let m = nu.checked_add(c).ok_or("trace dimension overflow")?;
        if m >= 25 || c > 11 || public_log > m || !(2..=64).contains(&degree) {
            return Err("trace profile bounds".into());
        }
        let t = ((1usize << c) + 3).max(5);
        let s = t + 1;
        let pcs = TraceParameters::new(m + 1, t, (degree * s + 2).max(2 * s + 2))?;
        Ok(Self {
            nu,
            c,
            public_log,
            degree,
            pcs,
        })
    }
    pub fn nu(&self) -> usize {
        self.nu
    }
    pub fn c(&self) -> usize {
        self.c
    }
    pub fn public_log(&self) -> usize {
        self.public_log
    }
    pub fn degree(&self) -> usize {
        self.degree
    }
    pub fn l(&self) -> usize {
        self.pcs.l()
    }
    pub fn m(&self) -> usize {
        self.nu + self.c
    }
    pub fn n(&self) -> usize {
        1usize << self.nu
    }
    pub fn k(&self) -> usize {
        1usize << self.c
    }
    pub fn n_total(&self) -> usize {
        1usize << self.m()
    }
    pub fn parameters(&self) -> &TraceParameters {
        &self.pcs
    }
    pub fn setup(
        &self,
        rng: &mut impl RngCore,
        max_primary_points: usize,
    ) -> Result<ValidatedTraceSrs> {
        ValidatedTraceSrs::setup(
            self.pcs.clone(),
            Arc::new(ExtensionField::new(self.l())?),
            rng,
            max_primary_points,
        )
    }
    fn schedule(&self) -> Vec<(&'static str, usize, usize)> {
        let s = self.pcs.t() + 1;
        let mut out = vec![
            ("gate", self.nu + 1, self.degree * s + 2),
            ("public", self.l(), s + 2),
        ];
        if self.m() > 0 {
            out.extend([
                ("leaf_A", self.m(), s + 1),
                ("leaf_B", self.m(), s + 1),
                ("internal_A", self.m(), 2 * s + 2),
                ("internal_B", self.m(), 2 * s + 2),
                ("root", self.l(), s + 1),
            ]);
        }
        out
    }
    pub fn round_scalars(&self) -> usize {
        self.schedule().iter().map(|(_, d, c)| d * (c + 1)).sum()
    }
}

pub struct TraceIndex {
    profile: TraceProfile,
    gate: Gate,
    srs_id: [u8; 32],
    digest: [u8; 32],
    polynomials: BTreeMap<String, TraceSource>,
    commitments: BTreeMap<String, G2Affine>,
    wiring: Vec<usize>,
}
impl TraceIndex {
    pub fn certify(srs: &ValidatedTraceSrs, p: TraceProfile, spec: IndexSpec) -> Result<Self> {
        if srs.parameters() != p.parameters() || spec.lookup.is_some() {
            return Err("trace index/SRS profile or unsupported lookup".into());
        }
        let count = match spec.gate {
            Gate::ReferencePower => p.k(),
            Gate::FixedThirteen if p.k() == 8 && p.degree == 5 => 12,
            _ => {
                return Err("B1 currently supports reference-power and fixed-thirteen gates".into())
            }
        };
        let expected = (0..count)
            .map(|i| format!("q{i}"))
            .chain(std::iter::once("qout".into()))
            .collect::<BTreeSet<_>>();
        if spec.selectors.keys().cloned().collect::<BTreeSet<_>>() != expected
            || spec.selectors.values().any(|v| v.len() != p.n())
        {
            return Err("trace selector registry/shape".into());
        }
        if spec.wiring.len() != p.n_total() {
            return Err("trace wiring length".into());
        }
        let mut seen = vec![false; p.n_total()];
        for i in &spec.wiring {
            if *i >= seen.len() || seen[*i] {
                return Err("trace wiring is not a permutation".into());
            }
            seen[*i] = true;
        }
        let mut polys = BTreeMap::new();
        for (name, row) in &spec.selectors {
            polys.insert(
                name.clone(),
                TraceSource::new(
                    StructuredPolynomial::from_table(
                        p.l(),
                        p.l() - p.nu,
                        DenseMle::new(row.clone())?,
                    )?,
                    None,
                )?,
            );
        }
        polys.insert(
            "sigma".into(),
            TraceSource::new(
                StructuredPolynomial::from_table(
                    p.l(),
                    1,
                    DenseMle::new(spec.wiring.iter().map(|i| Fr::from(*i as u64)).collect())?,
                )?,
                None,
            )?,
        );
        let mut commitments = BTreeMap::new();
        for (name, poly) in &polys {
            commitments.insert(
                name.clone(),
                trace_pcs::commit_source(srs, poly, Fr::zero())?,
            );
        }
        let mut h = Sha256::new();
        h.update(b"B1-seven-trace-certified-index/v1\0");
        h.update(srs.vk().srs_digest());
        for n in [p.nu, p.c, p.public_log, p.degree] {
            h.update((n as u64).to_be_bytes());
        }
        h.update(spec.gate.name());
        for (name, row) in &spec.selectors {
            h.update((name.len() as u64).to_be_bytes());
            h.update(name);
            for x in row {
                h.update(scalar_bytes(x));
            }
        }
        for i in &spec.wiring {
            h.update((*i as u64).to_be_bytes());
        }
        for (name, c) in &commitments {
            h.update(name);
            h.update(g2_bytes(c));
        }
        Ok(Self {
            profile: p,
            gate: spec.gate,
            srs_id: srs.vk().srs_digest(),
            digest: h.finalize().into(),
            polynomials: polys,
            commitments,
            wiring: spec.wiring,
        })
    }
    pub fn profile(&self) -> &TraceProfile {
        &self.profile
    }
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }
    pub fn srs_id(&self) -> [u8; 32] {
        self.srs_id
    }
    pub fn gate(&self) -> Gate {
        self.gate
    }
    pub fn commitments(&self) -> &BTreeMap<String, G2Affine> {
        &self.commitments
    }
}
fn context(index: &TraceIndex, public: &[Fr]) -> Result<Vec<u8>> {
    let p = &index.profile;
    if public.len() != 1usize << p.public_log {
        return Err("trace public-input length".into());
    }
    let mut map = BTreeMap::new();
    map.insert(
        "protocol".into(),
        C::Text("B1-seven-trace-prefix-full-round-coefficients-rust-v1".into()),
    );
    map.insert("curve".into(), C::Text("BLS12-381".into()));
    map.insert(
        "E".into(),
        C::List(p.schedule().iter().map(|(_, _, c)| C::from(*c)).collect()),
    );
    map.insert("D".into(), C::from(p.pcs.d()));
    map.insert("anchor".into(), C::Null);
    map.insert(
        "dimensions".into(),
        C::List(
            [p.nu, p.c, p.public_log, p.degree, p.l(), p.pcs.t()]
                .into_iter()
                .map(C::from)
                .collect(),
        ),
    );
    map.insert(
        "public_index_commitments".into(),
        C::Map(
            index
                .commitments
                .iter()
                .map(|(h, c)| (h.clone(), C::Bytes(g2_bytes(c).to_vec())))
                .collect(),
        ),
    );
    map.insert(
        "public_input".into(),
        C::List(public.iter().copied().map(C::from).collect()),
    );
    map.insert(
        "certified_index_digest".into(),
        C::Bytes(index.digest.to_vec()),
    );
    map.insert("srs_id".into(), C::Bytes(index.srs_id.to_vec()));
    map.insert("gate".into(), C::Text(index.gate.name()));
    map.insert(
        "roots".into(),
        C::Text("independent-A-B-trace-budget-five".into()),
    );
    canonical_context(&map)
}
fn vars(n: usize) -> Vec<Binding> {
    (0..n).map(Binding::Variable).collect()
}
fn cat(mut a: Vec<Binding>, b: Vec<Binding>) -> Vec<Binding> {
    a.extend(b);
    a
}
fn fixed(b: bool) -> Binding {
    Binding::Fixed(b)
}
fn relations(p: &TraceProfile, gate: Gate, beta: Fr, gamma: Fr) -> Vec<NativeRelation> {
    let (l, m, nu, c, k) = (p.l(), p.m(), p.nu, p.c, p.k());
    let mut out = vec![];
    let mut g = NativeRelation::new(nu + 1);
    let qmap = cat(
        vec![fixed(false); l - nu],
        (1..=nu).map(Binding::Variable).collect(),
    );
    let mut expression = Expr::constant(0);
    let mut w = vec![];
    for a in 0..k {
        let q = g.source(&format!("q{a}"), qmap.clone());
        let map = std::iter::once(Binding::Variable(0))
            .chain((0..c).map(|i| fixed((a >> (c - 1 - i)) & 1 != 0)))
            .chain((1..=nu).map(Binding::Variable))
            .collect();
        let v = g.source("W", map);
        expression = expression.plus(q.times(v.clone().power(p.degree as u64)));
        w.push(v);
    }
    if gate == Gate::FixedThirteen {
        for (i, (a, b)) in [(0, 1), (2, 3), (4, 5), (0, 6)].iter().enumerate() {
            let q = g.source(&format!("q{}", 8 + i), qmap.clone());
            expression = expression.plus(q.times(w[*a].clone()).times(w[*b].clone()));
        }
    }
    g.expression = Expr::constant(1)
        .minus(Expr::Variable(0))
        .times(expression.minus(g.source("qout", qmap)));
    out.push(g);
    let mut public = NativeRelation::new(l);
    let w = public.source("W", vars(l));
    let pi = public.source("__public", vars(l));
    public.expression = w.minus(pi).times(native::eq_zero(0..l - p.public_log));
    out.push(public);
    if m > 0 {
        for name in ["A", "B"] {
            let mut r = NativeRelation::new(m);
            let tree = r.source(name, cat(vec![fixed(true)], vars(m)));
            let witness = r.source("W", cat(vec![fixed(false)], vars(m)));
            let labels = if name == "A" {
                (0..m).fold(Expr::constant(0), |a, i| {
                    a.plus(Expr::Constant(Fr::from(1u64 << (m - 1 - i))).times(Expr::Variable(i)))
                })
            } else {
                r.source("sigma", cat(vec![fixed(false)], vars(m)))
            };
            r.expression = tree
                .minus(witness)
                .minus(Expr::Constant(beta).times(labels))
                .minus(Expr::Constant(gamma));
            out.push(r);
        }
        for name in ["A", "B"] {
            let mut r = NativeRelation::new(m);
            let parent = r.source(name, cat(vec![fixed(false)], vars(m)));
            let left = r.source(name, cat(vars(m), vec![fixed(false)]));
            let right = r.source(name, cat(vars(m), vec![fixed(true)]));
            r.expression = Expr::constant(1)
                .minus(native::eq_zero(0..m))
                .times(parent.minus(left.times(right)));
            out.push(r);
        }
        let mut root = NativeRelation::new(l);
        let a = root.source("A", vars(l));
        let b = root.source("B", vars(l));
        root.expression = a
            .minus(b)
            .times(native::eq_zero(0..m))
            .times(Expr::Variable(m));
        out.push(root);
    }
    out
}
fn packet(
    tx: &mut Transcript,
    relations: &mut [NativeRelation],
    schedule: &[(&str, usize, usize)],
) -> Result<Vec<Fr>> {
    let count = schedule
        .iter()
        .filter(|(n, _, _)| *n != "root")
        .map(|(_, d, _)| *d)
        .sum::<usize>();
    let mut domains = vec![Domain::Field; count];
    domains.extend(vec![Domain::Nonzero; relations.len()]);
    let mut values = tx
        .challenge_mixed("compression_packet", &domains)?
        .into_iter();
    for (r, (name, d, _)) in relations.iter_mut().zip(schedule) {
        if *name != "root" {
            r.tau = Some((0..*d).map(|_| values.next().unwrap()).collect());
        }
    }
    Ok(values.collect())
}
fn helper(
    p: &TraceProfile,
    d: usize,
    cap: usize,
    rng: &mut impl RngCore,
) -> Result<(StructuredPolynomial, Fr)> {
    let mut extras = BTreeMap::new();
    let c0 = sample_fr(rng)?;
    extras.insert(vec![0; p.l()], c0);
    let mut sum = Fr::from(2u64).pow([d as u64]) * c0;
    let factor = Fr::from(2u64).pow([(d - 1) as u64]);
    for a in p.l() - d..p.l() {
        for e in 1..=cap {
            let mut exponent = vec![0; p.l()];
            exponent[a] = e;
            let c = sample_fr(rng)?;
            sum += factor * c;
            extras.insert(exponent, c);
        }
    }
    Ok((StructuredPolynomial::new(p.l(), vec![], extras)?, sum))
}
fn masked(srs: &ValidatedTraceSrs, table: Vec<Fr>, rng: &mut impl RngCore) -> Result<TraceSource> {
    TraceSource::new(
        StructuredPolynomial::from_table(srs.parameters().l(), 0, DenseMle::new(table)?)?,
        Some(TraceMask::sample(
            srs.field().clone(),
            srs.parameters().t(),
            rng,
        )?),
    )
}
fn public_source(p: &TraceProfile, public: &[Fr]) -> Result<TraceSource> {
    TraceSource::new(
        StructuredPolynomial::from_table(
            p.l(),
            p.l() - p.public_log,
            DenseMle::new(public.to_vec())?,
        )?,
        None,
    )
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Query {
    handle: String,
    point: Vec<Fr>,
}
fn queries(
    rels: &[NativeRelation],
    schedule: &[(&str, usize, usize)],
    path: &[Fr],
    l: usize,
) -> Vec<Query> {
    let mut out = vec![];
    for (r, (name, d, _)) in rels.iter().zip(schedule) {
        for s in &r.sources {
            if s.handle != "__public" {
                out.push(Query {
                    handle: s.handle.clone(),
                    point: s.point(&path[..*d]),
                });
            }
        }
        out.push(Query {
            handle: format!("g/{name}"),
            point: vec![Fr::zero(); l - d]
                .into_iter()
                .chain(path[..*d].iter().copied())
                .collect(),
        });
    }
    out
}
struct Bucket {
    kind: SourceKind,
    point: Vec<Fr>,
    indices: Vec<usize>,
}
fn buckets(q: &[Query]) -> Vec<Bucket> {
    let mut out: Vec<Bucket> = vec![];
    for (i, q) in q.iter().enumerate() {
        let kind = if q.handle.starts_with("g/") {
            SourceKind::Helper
        } else {
            SourceKind::Source
        };
        if let Some(b) = out
            .iter_mut()
            .find(|b| b.kind == kind && b.point == q.point)
        {
            b.indices.push(i);
        } else {
            out.push(Bucket {
                kind,
                point: q.point.clone(),
                indices: vec![i],
            });
        }
    }
    out
}
fn freeze(tx: &mut Transcript, queries: &[Query], values: &[Fr]) -> Result<()> {
    for (i, (q, v)) in queries.iter().zip(values).enumerate() {
        let mut block = vec![if q.handle.starts_with("g/") { 1 } else { 2 }];
        for z in &q.point {
            block.extend(scalar_bytes(z));
        }
        block.extend(scalar_bytes(v));
        tx.absorb(&format!("endpoint/{i}/{}", q.handle), &block)?;
    }
    Ok(())
}
fn weights(tx: &mut Transcript, buckets: &[Bucket]) -> Result<Vec<Vec<Fr>>> {
    let count = buckets.iter().map(|b| b.indices.len() - 1).sum::<usize>();
    let mut values = tx
        .challenge("same_point_batch", count.max(1), Domain::Field)?
        .into_iter();
    Ok(buckets
        .iter()
        .map(|b| {
            std::iter::once(Fr::one())
                .chain((1..b.indices.len()).map(|_| values.next().unwrap()))
                .collect()
        })
        .collect())
}
fn query_budget(p: &TraceProfile, queries: &[Query]) -> Result<BTreeMap<String, usize>> {
    let mut counts = BTreeMap::new();
    for name in ["W", "A", "B"] {
        let unique = queries
            .iter()
            .filter(|q| q.handle == name)
            .map(|q| q.point.clone())
            .collect::<Vec<_>>();
        let mut dedup: Vec<Vec<Fr>> = vec![];
        for point in unique {
            if point.iter().all(|x| x.is_zero() || x.is_one()) {
                return Err("private Boolean endpoint".into());
            }
            if !dedup.contains(&point) {
                dedup.push(point);
            }
        }
        let cap = if name == "W" { p.k() + 2 } else { 5 };
        if dedup.len() > cap || dedup.len() > p.pcs.t() {
            return Err("trace distinct-source query budget exceeded".into());
        }
        counts.insert(name.into(), dedup.len());
    }
    Ok(counts)
}

#[derive(Clone, Debug, Serialize)]
pub struct TraceMetrics {
    pub seconds: f64,
    pub proof_bytes: usize,
    pub round_scalars: usize,
    pub endpoint_claims: usize,
    pub opening_count: usize,
    pub hash_packets: u64,
    pub fold_pairs: usize,
    pub line_points: usize,
    pub private_queries: BTreeMap<String, usize>,
    pub offsets: BTreeMap<String, usize>,
    pub stages: BTreeMap<String, f64>,
}
fn stage(stages: &mut BTreeMap<String, f64>, clock: &mut Instant, name: &str) {
    let now = Instant::now();
    stages.insert(name.into(), now.duration_since(*clock).as_secs_f64());
    *clock = now;
}

pub fn prove(
    srs: &ValidatedTraceSrs,
    index: &TraceIndex,
    public: &[Fr],
    witness: &[Fr],
    rng: &mut impl RngCore,
) -> Result<(Vec<u8>, TraceMetrics)> {
    let start = Instant::now();
    let mut checkpoint = start;
    let mut stages = BTreeMap::new();
    let p = &index.profile;
    if srs.parameters() != p.parameters()
        || srs.vk().srs_digest() != index.srs_id
        || witness.len() != p.n_total()
        || witness.get(..public.len()) != Some(public)
    {
        return Err("trace index/SRS/witness/public mismatch".into());
    }
    let mut salt = [0; 32];
    rng.try_fill_bytes(&mut salt).map_err(|e| e.to_string())?;
    let mut tx = Transcript::new(&context(index, public)?, salt);
    let mut wire = HEADER.to_vec();
    wire.extend(salt);
    let mut offsets = BTreeMap::new();
    let mut sources = index.polynomials.clone();
    let mut blinds = index
        .commitments
        .keys()
        .map(|n| (n.clone(), Fr::zero()))
        .collect::<BTreeMap<_, _>>();
    let mut w = witness.to_vec();
    w.resize(2 * w.len(), Fr::zero());
    let poly = masked(srs, w, rng)?;
    let blind = sample_fr(rng)?;
    let c = trace_pcs::commit_source(srs, &poly, blind)?;
    offsets.insert("witness".into(), wire.len());
    let block = g2_bytes(&c);
    wire.extend(block);
    tx.absorb("witness", &block)?;
    sources.insert("W".into(), poly);
    blinds.insert("W".into(), blind);
    stage(&mut stages, &mut checkpoint, "witness_context_commitment");
    let (beta, gamma) = if p.m() > 0 {
        let v = tx.challenge_mixed("copy", &[Domain::Nonzero, Domain::Field])?;
        (v[0], v[1])
    } else {
        (Fr::zero(), Fr::zero())
    };
    if p.m() > 0 {
        for name in ["A", "B"] {
            let mut heap = vec![Fr::zero(); 2 * witness.len()];
            for (i, w) in witness.iter().enumerate() {
                heap[witness.len() + i] = *w
                    + beta * Fr::from(if name == "A" { i } else { index.wiring[i] } as u64)
                    + gamma;
            }
            for i in (1..witness.len()).rev() {
                heap[i] = heap[2 * i] * heap[2 * i + 1];
            }
            let poly = masked(srs, heap, rng)?;
            let blind = sample_fr(rng)?;
            let c = trace_pcs::commit_source(srs, &poly, blind)?;
            let block = g2_bytes(&c);
            wire.extend(block);
            tx.absorb(&format!("tree/{name}"), &block)?;
            sources.insert(name.into(), poly);
            blinds.insert(name.into(), blind);
        }
    }
    let schedule = p.schedule();
    let mut helpers = BTreeMap::new();
    let mut sums = vec![];
    offsets.insert("helpers".into(), wire.len());
    for (name, d, cap) in &schedule {
        let (g, sum) = helper(p, *d, *cap, rng)?;
        let blind = sample_fr(rng)?;
        let c = trace_pcs::commit_helper(srs, &g, blind)?;
        let handle = format!("g/{name}");
        let mut block = g1_bytes(&c).to_vec();
        block.extend(scalar_bytes(&sum));
        wire.extend(&block);
        tx.absorb(&format!("helper/{name}"), &block)?;
        helpers.insert(handle.clone(), g);
        blinds.insert(handle, blind);
        sums.push(sum);
    }
    let mut rels = relations(p, index.gate, beta, gamma);
    let rhos = packet(&mut tx, &mut rels, &schedule)?;
    sources.insert("__public".into(), public_source(p, public)?);
    stage(&mut stages, &mut checkpoint, "trees_helpers_commitments");
    let mut engines = rels
        .iter()
        .zip(&schedule)
        .zip(&rhos)
        .map(|((r, (name, _, cap)), rho)| {
            TraceSumcheck::new(
                r.clone(),
                *cap,
                &sources,
                helpers[&format!("g/{name}")].clone(),
                *rho,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    stage(&mut stages, &mut checkpoint, "native_compile_and_precheck");
    let mut current = sums
        .iter()
        .zip(&rhos)
        .map(|(g, r)| *g * r)
        .collect::<Vec<_>>();
    let mut path = vec![];
    offsets.insert("rounds".into(), wire.len());
    for depth in 0..p.l() {
        let mut rows = vec![];
        for (j, (name, d, _)) in schedule.iter().enumerate() {
            if depth >= *d {
                continue;
            }
            let row = engines[j].round_coefficients()?;
            if row[0] + native::univariate(&row, Fr::one()) != current[j] {
                return Err("historical sumcheck recurrence".into());
            }
            let block = row.iter().flat_map(scalar_bytes).collect::<Vec<_>>();
            wire.extend(&block);
            tx.absorb(&format!("round/{name}/{depth}"), &block)?;
            rows.push((j, row));
        }
        let challenge = tx.challenge(&format!("sumcheck_depth/{depth}"), 1, Domain::Nonboolean)?[0];
        for (j, row) in rows {
            current[j] = native::univariate(&row, challenge);
            engines[j].fold(challenge)?;
        }
        path.push(challenge);
    }
    let fold_pairs = engines.iter().map(|e| e.fold_pairs).sum();
    let line_points = engines.iter().map(|e| e.line_points).sum();
    drop(engines);
    stage(&mut stages, &mut checkpoint, "sumcheck_rounds");
    for (j, (r, (name, d, _))) in rels.iter().zip(&schedule).enumerate() {
        let point = vec![Fr::zero(); p.l() - d]
            .into_iter()
            .chain(path[..*d].iter().copied())
            .collect::<Vec<_>>();
        let terminal = r.evaluate(&path[..*d], &mut |h, z| sources[h].evaluate(z))?
            + rhos[j] * helpers[&format!("g/{name}")].evaluate(&point)?;
        if terminal != current[j] {
            return Err("historical terminal relation".into());
        }
    }
    let ordered = queries(&rels, &schedule, &path, p.l());
    let private_queries = query_budget(p, &ordered)?;
    let values = ordered
        .iter()
        .map(|q| {
            if q.handle.starts_with("g/") {
                helpers[&q.handle].evaluate(&q.point)
            } else {
                sources[&q.handle].evaluate(&q.point)
            }
        })
        .collect::<Result<Vec<_>>>()?;
    offsets.insert("values".into(), wire.len());
    wire.extend(values.iter().flat_map(scalar_bytes));
    freeze(&mut tx, &ordered, &values)?;
    let buckets = buckets(&ordered);
    let alphas = weights(&mut tx, &buckets)?;
    stage(&mut stages, &mut checkpoint, "endpoints_and_batching");
    offsets.insert("openings".into(), wire.len());
    for (b, weights) in buckets.iter().zip(&alphas) {
        let mut blind = Fr::zero();
        let proof = if b.kind == SourceKind::Source {
            let mut poly = TraceSource::new(StructuredPolynomial::zero(p.l())?, None)?;
            for (i, a) in b.indices.iter().zip(weights) {
                poly = poly.add(&sources[&ordered[*i].handle].scaled(*a)?)?;
                blind += blinds[&ordered[*i].handle] * *a;
            }
            trace_pcs::open_source(srs, &poly, &b.point, blind, rng)?
        } else {
            let mut poly = StructuredPolynomial::zero(p.l())?;
            for (i, a) in b.indices.iter().zip(weights) {
                poly = poly.add(&helpers[&ordered[*i].handle].scaled(*a))?;
                blind += blinds[&ordered[*i].handle] * *a;
            }
            trace_pcs::open_helper(srs, &poly, &b.point, blind, rng)?
        };
        for point in proof.points {
            wire.extend(g1_bytes(&point));
        }
    }
    stage(
        &mut stages,
        &mut checkpoint,
        "opening_quotients_msm_encoding",
    );
    let expected = 37
        + 96 * (1 + 2 * usize::from(p.m() > 0))
        + 80 * schedule.len()
        + 32 * (p.round_scalars() + ordered.len())
        + 48 * buckets.len() * (p.l() + 1);
    if wire.len() != expected {
        return Err("trace communication ledger mismatch".into());
    }
    Ok((
        wire.clone(),
        TraceMetrics {
            seconds: start.elapsed().as_secs_f64(),
            proof_bytes: wire.len(),
            round_scalars: p.round_scalars(),
            endpoint_claims: ordered.len(),
            opening_count: buckets.len(),
            hash_packets: tx.query_count(),
            fold_pairs,
            line_points,
            private_queries,
            offsets,
            stages,
        },
    ))
}

pub fn verify(
    vk: &VerificationKey,
    index: &TraceIndex,
    public: &[Fr],
    proof: &[u8],
) -> Result<TraceMetrics> {
    let start = Instant::now();
    let mut checkpoint = start;
    let mut stages = BTreeMap::new();
    let p = &index.profile;
    if vk.dimension() != p.l() || vk.srs_digest() != index.srs_id {
        return Err("trace verifier index/SRS mismatch".into());
    }
    let schedule = p.schedule();
    let templates = relations(p, index.gate, Fr::one(), Fr::zero());
    let max_values = templates
        .iter()
        .map(|r| r.sources.iter().filter(|s| s.handle != "__public").count() + 1)
        .sum::<usize>();
    let max_bytes = 37
        + 288
        + 80 * schedule.len()
        + 32 * (p.round_scalars() + max_values)
        + 48 * max_values * (p.l() + 1);
    if proof.len() > max_bytes {
        return Err("trace proof exceeds layout bound".into());
    }
    let mut reader = Reader::new(proof);
    if reader.bytes(5)? != HEADER {
        return Err("trace proof header".into());
    }
    let salt = reader.bytes(32)?.try_into().unwrap();
    let mut tx = Transcript::new(&context(index, public)?, salt);
    let mut commitments = index
        .commitments
        .iter()
        .map(|(h, c)| (h.clone(), Commitment::Source(*c)))
        .collect::<BTreeMap<_, _>>();
    let mut offsets = BTreeMap::new();
    offsets.insert("witness".into(), reader.position());
    let off = reader.position();
    commitments.insert("W".into(), Commitment::Source(reader.g2()?));
    tx.absorb("witness", &proof[off..reader.position()])?;
    let (beta, gamma) = if p.m() > 0 {
        let v = tx.challenge_mixed("copy", &[Domain::Nonzero, Domain::Field])?;
        (v[0], v[1])
    } else {
        (Fr::zero(), Fr::zero())
    };
    if p.m() > 0 {
        for name in ["A", "B"] {
            let off = reader.position();
            commitments.insert(name.into(), Commitment::Source(reader.g2()?));
            tx.absorb(&format!("tree/{name}"), &proof[off..reader.position()])?;
        }
    }
    let mut sums = vec![];
    offsets.insert("helpers".into(), reader.position());
    for (name, _, _) in &schedule {
        let off = reader.position();
        commitments.insert(format!("g/{name}"), Commitment::Helper(reader.g1()?));
        sums.push(reader.scalar()?);
        tx.absorb(&format!("helper/{name}"), &proof[off..reader.position()])?;
    }
    let mut rels = relations(p, index.gate, beta, gamma);
    let rhos = packet(&mut tx, &mut rels, &schedule)?;
    let mut current = sums
        .iter()
        .zip(&rhos)
        .map(|(g, r)| *g * r)
        .collect::<Vec<_>>();
    let mut path = vec![];
    stage(
        &mut stages,
        &mut checkpoint,
        "context_commitment_decode_and_transcript",
    );
    offsets.insert("rounds".into(), reader.position());
    for depth in 0..p.l() {
        let mut rows = vec![];
        for (j, (name, d, cap)) in schedule.iter().enumerate() {
            if depth >= *d {
                continue;
            }
            let off = reader.position();
            let row = (0..=*cap)
                .map(|_| reader.scalar())
                .collect::<Result<Vec<_>>>()?;
            if row[0] + native::univariate(&row, Fr::one()) != current[j] {
                return Err("historical sumcheck recurrence".into());
            }
            tx.absorb(
                &format!("round/{name}/{depth}"),
                &proof[off..reader.position()],
            )?;
            rows.push((j, row));
        }
        let challenge = tx.challenge(&format!("sumcheck_depth/{depth}"), 1, Domain::Nonboolean)?[0];
        for (j, row) in rows {
            current[j] = native::univariate(&row, challenge);
        }
        path.push(challenge);
    }
    stage(&mut stages, &mut checkpoint, "sumcheck_transcript");
    let ordered = queries(&rels, &schedule, &path, p.l());
    let private_queries = query_budget(p, &ordered)?;
    offsets.insert("values".into(), reader.position());
    let values = (0..ordered.len())
        .map(|_| reader.scalar())
        .collect::<Result<Vec<_>>>()?;
    for (i, q) in ordered.iter().enumerate() {
        for (j, old) in ordered[..i].iter().enumerate() {
            if old == q && values[j] != values[i] {
                return Err("inconsistent repeated historical endpoint".into());
            }
        }
    }
    freeze(&mut tx, &ordered, &values)?;
    let public_poly = public_source(p, public)?;
    let mut get = |h: &str, z: &[Fr]| {
        if h == "__public" {
            public_poly.evaluate(z)
        } else {
            ordered
                .iter()
                .position(|q| q.handle == h && q.point == z)
                .map(|i| values[i])
                .ok_or("missing endpoint".into())
        }
    };
    for (j, (r, (name, d, _))) in rels.iter().zip(&schedule).enumerate() {
        let point = vec![Fr::zero(); p.l() - d]
            .into_iter()
            .chain(path[..*d].iter().copied())
            .collect::<Vec<_>>();
        let terminal =
            r.evaluate(&path[..*d], &mut get)? + rhos[j] * get(&format!("g/{name}"), &point)?;
        if terminal != current[j] {
            return Err("historical terminal relation".into());
        }
    }
    let buckets = buckets(&ordered);
    let alphas = weights(&mut tx, &buckets)?;
    stage(
        &mut stages,
        &mut checkpoint,
        "endpoints_terminal_and_batching",
    );
    offsets.insert("openings".into(), reader.position());
    let mut openings = vec![];
    for (b, weights) in buckets.iter().zip(&alphas) {
        let mut commitment = commitments[&ordered[b.indices[0]].handle].scale(Fr::zero());
        let mut value = Fr::zero();
        for (i, a) in b.indices.iter().zip(weights) {
            commitment = commitment.add(&commitments[&ordered[*i].handle].scale(*a))?;
            value += values[*i] * *a;
        }
        let points = (0..=p.l())
            .map(|_| reader.g1())
            .collect::<Result<Vec<_>>>()?;
        openings.push(Opening {
            commitment,
            point: b.point.clone(),
            value,
            proof: OpeningProof { points },
        });
    }
    reader.finish()?;
    stage(
        &mut stages,
        &mut checkpoint,
        "opening_decode_and_subgroup_checks",
    );
    if openings.iter().any(|o| !pcs::verify_opening(vk, o)) {
        return Err("trace PCS equation rejected".into());
    }
    stage(&mut stages, &mut checkpoint, "pairing_equations");
    Ok(TraceMetrics {
        seconds: start.elapsed().as_secs_f64(),
        proof_bytes: proof.len(),
        round_scalars: p.round_scalars(),
        endpoint_claims: ordered.len(),
        opening_count: buckets.len(),
        hash_packets: tx.query_count(),
        fold_pairs: 0,
        line_points: 0,
        private_queries,
        offsets,
        stages,
    })
}

/// Trusted small integration fixture: public data only, no witness, setup
/// scalar, mask or commitment/opening blind. The external oracle independently
/// reconstructs every relation, endpoint and pairing equation from this data.
pub fn public_fixture(
    vk: &VerificationKey,
    index: &TraceIndex,
    public: &[Fr],
    proof: &[u8],
) -> Result<serde_json::Value> {
    let p = &index.profile;
    if p.l() > 10 || vk.srs_digest() != index.srs_id {
        return Err("trace fixture bounds or SRS".into());
    }
    Ok(
        serde_json::json!({"schema":"B1-seven-trace-public-fixture-v1","profile":{"nu":p.nu,"c":p.c,"public_log":p.public_log,"degree":p.degree,"T":p.pcs.t(),"D":p.pcs.d()},"gate":index.gate.name(),"context_hex":hex::encode(context(index,public)?),"public_input":public.iter().map(|v|hex::encode(scalar_bytes(v))).collect::<Vec<_>>(),"index_commitments":index.commitments.iter().map(|(n,c)|(n.clone(),hex::encode(g2_bytes(c)))).collect::<BTreeMap<_,_>>(),"tau_g2":vk.tau_g2().iter().map(|c|hex::encode(g2_bytes(c))).collect::<Vec<_>>(),"zeta_g2":hex::encode(g2_bytes(vk.zeta_g2())),"proof_hex":hex::encode(proof),"index_digest":hex::encode(index.digest),"srs_digest":hex::encode(index.srs_id)}),
    )
}
