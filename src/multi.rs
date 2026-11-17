//! Independent native sumchecks synchronized on one non-Boolean suffix path.
use crate::{
    codec::{g1_bytes, pack_bytes, scalar_bytes, Reader},
    gates,
    index::ValidatedIndex,
    native::{self, NativeRelation, NativeSumcheck},
    pcs::{self, Commitment, Opening, OpeningProof, PublicSrs, SourceKind, VerificationKey},
    profile::ValidatedProfile,
    protocol::{self, bucket_weights, buckets, queries, Metrics, ProverOptions, Query},
    random::sample_fr,
    tables::{DenseMle, StructuredPolynomial},
    transcript::{Domain, Transcript},
    Result,
};
use ark_bls12_381::{Fr, G1Affine, G2Affine};
use ark_ff::{Field, One, Zero};
use rand::RngCore;
use serde::Serialize;
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::time::Instant;

pub const HEADER: &[u8; 5] = b"HPM\0\x01";

#[derive(Serialize)]
struct Check {
    name: &'static str,
    dimension: usize,
    suffix_offset: usize,
    honest_caps: Vec<usize>,
    native_expression_caps: Vec<usize>,
    actual_helper_caps: Vec<usize>,
    soundness_caps: Vec<usize>,
    first_round_free: usize,
    helper_coefficients: usize,
}

impl Check {
    fn handle(&self) -> String {
        format!("multi_helper/{}", self.name)
    }
    fn point(&self, path: &[Fr]) -> Vec<Fr> {
        let mut point = vec![Fr::zero(); self.suffix_offset];
        point.extend_from_slice(&path[self.suffix_offset..]);
        point
    }
}

fn checks(p: &ValidatedProfile, index: &ValidatedIndex) -> Result<Vec<Check>> {
    if p.flags() > 3 || index.lookup().is_some() || !index.matches(p, &index.srs_id()) {
        return Err(
            "independent sumchecks require the matching core geometry index and SRS profile".into(),
        );
    }
    let mut names = vec!["gate"];
    if !p.virtual_public() {
        names.push("public");
    }
    if p.m() != 0 {
        names.extend(["leaf_A", "leaf_B", "internal_A", "internal_B", "root"]);
    }
    let templates = protocol::relations(p, index.gate(), Fr::one(), Fr::zero());
    if names.len() != templates.len() {
        return Err("native check count".into());
    }
    names
        .into_iter()
        .zip(templates)
        .map(|(name, r)| {
            let raw = p
                .native_caps()
                .get(name)
                .ok_or("missing native degree certificate")?;
            if raw.len() != r.dimension || raw.len() > p.l() || raw.is_empty() {
                return Err("native degree certificate arity".into());
            }
            let offset = p.l() - raw.len();
            // The same SRS is shared by all helpers. Q(V) has axis degree at most
            // two; the published pure powers reach E at every relevant axis.
            let actual_helper_caps = p.e()[offset..]
                .iter()
                .map(|e| (*e).max(2))
                .collect::<Vec<_>>();
            let honest_caps = raw
                .iter()
                .zip(&p.e()[offset..])
                .map(|(d, e)| (*d).min(*e))
                .collect::<Vec<_>>();
            if honest_caps[0] < 2 || honest_caps.contains(&0) {
                return Err("native message cap".into());
            }
            let soundness_caps = raw
                .iter()
                .zip(&actual_helper_caps)
                .map(|(d, u)| (*d).max(*u))
                .collect();
            Ok(Check {
                name,
                dimension: r.dimension,
                suffix_offset: offset,
                first_round_free: honest_caps[0] - 1,
                helper_coefficients: honest_caps.iter().sum::<usize>() - 1,
                honest_caps,
                native_expression_caps: raw.clone(),
                actual_helper_caps,
                soundness_caps,
            })
        })
        .collect()
}

pub fn ledger(p: &ValidatedProfile, index: &ValidatedIndex) -> Result<Value> {
    let cs = checks(p, index)?;
    let h: usize = cs.iter().map(|c| c.helper_coefficients).sum();
    let helper_opening_buckets = cs
        .iter()
        .map(|c| c.suffix_offset)
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    Ok(
        json!({"checks":cs,"relation_family":"native-core","shared_suffix":true,
        "helper_count":cs.len(),"round_scalars":h,"helper_coefficients":h,
        "helper_opening_buckets":helper_opening_buckets,
        "private_commitment_bytes":288+48*cs.len()}),
    )
}

fn context(
    p: &ValidatedProfile,
    index: &ValidatedIndex,
    public: &[Fr],
    cs: &[Check],
) -> Result<Vec<u8>> {
    let mut bytes = pack_bytes(b"independent-native-half-sum-suffix-v1");
    bytes.extend(pack_bytes(&protocol::context_bytes(p, index, public)?));
    bytes.extend((cs.len() as u64).to_be_bytes());
    for check in cs {
        bytes.extend(pack_bytes(check.name.as_bytes()));
        bytes.extend((check.suffix_offset as u64).to_be_bytes());
        bytes.extend((check.dimension as u64).to_be_bytes());
        for cap in check.honest_caps.iter().chain(&check.soundness_caps) {
            bytes.extend((*cap as u64).to_be_bytes());
        }
    }
    Ok(bytes)
}

fn packet(tx: &mut Transcript, rels: &mut [NativeRelation], cs: &[Check]) -> Result<Vec<Fr>> {
    let n = cs
        .iter()
        .filter(|c| c.name != "root")
        .map(|c| c.dimension)
        .sum();
    let mut domains = vec![Domain::Field; n];
    domains.extend(std::iter::repeat_n(Domain::Nonzero, cs.len()));
    let mut v = tx
        .challenge_mixed("independent_native_packet", &domains)?
        .into_iter();
    for (r, c) in rels.iter_mut().zip(cs) {
        if c.name != "root" {
            r.tau = Some(v.by_ref().take(c.dimension).collect());
        }
        r.weight = Fr::one();
    }
    Ok(v.collect())
}

// Compute both views from the same coefficients. The PCS commitment uses
// L coordinates and the folding engine uses the native suffix coordinates.
fn helper(
    p: &ValidatedProfile,
    c: &Check,
    rng: &mut impl RngCore,
) -> Result<(StructuredPolynomial, StructuredPolynomial)> {
    let d = c.dimension;
    let mut extras = BTreeMap::<Vec<usize>, Fr>::new();
    let half = Fr::from(2u64).inverse().unwrap();
    for (a, &cap) in c.honest_caps.iter().enumerate() {
        for e in (if a == 0 { 2 } else { 1 })..=cap {
            let coin = sample_fr(rng)?;
            let mut exponent = vec![0; d];
            exponent[a] = e;
            *extras.entry(exponent).or_default() += coin;
            let mut base = vec![0; d];
            if a == 0 {
                base[0] = 1;
            }
            *extras.entry(base).or_default() -= if a == 0 { coin } else { half * coin };
        }
    }
    let ambient = extras
        .iter()
        .map(|(e, v)| {
            let mut exp = vec![0; c.suffix_offset];
            exp.extend(e);
            (exp, *v)
        })
        .collect();
    Ok((
        StructuredPolynomial::new(d, vec![], extras)?,
        StructuredPolynomial::new(p.l(), vec![], ambient)?,
    ))
}

fn round_coefficients(
    engine: &mut NativeSumcheck,
    cap: usize,
    first: bool,
    current: Fr,
) -> Result<Vec<Fr>> {
    let samples = (0..=cap)
        .map(|i| engine.round_value(Fr::from(i as u64)))
        .collect::<Vec<_>>();
    let coeffs = native::interpolate(&samples)?;
    for x in [
        Fr::from((cap + 1) as u64),
        Fr::from((cap + 2) as u64),
        -Fr::one(),
    ] {
        if native::univariate(&coeffs, x) != engine.round_value(x) {
            return Err("native honest expression exceeds cap".into());
        }
    }
    let at1 = native::univariate(&coeffs, Fr::one());
    if first && (!coeffs[0].is_zero() || !at1.is_zero()) {
        return Err("first native half sum is nonzero".into());
    }
    if coeffs[0] + at1 != current {
        return Err("native recurrence".into());
    }
    Ok(coeffs)
}

fn derive_endpoints(
    path: &[Fr],
    rels: &[NativeRelation],
    cs: &[Check],
    current: &[Fr],
    rho: &[Fr],
    get: &mut impl FnMut(&str, &[Fr]) -> Result<Fr>,
) -> Result<Vec<Fr>> {
    (0..cs.len())
        .map(|j| {
            let residual = rels[j].evaluate(&path[cs[j].suffix_offset..], get)?;
            Ok((current[j] - residual) * rho[j].inverse().ok_or("zero helper mixer")?)
        })
        .collect()
}

fn add_helper_queries(ordered: &mut Vec<Query>, path: &[Fr], cs: &[Check]) {
    for c in cs {
        ordered.push(Query {
            handle: c.handle(),
            point: c.point(path),
        });
    }
}

fn stage(stages: &mut BTreeMap<String, f64>, checkpoint: &mut Instant, name: &str) {
    let now = Instant::now();
    stages.insert(name.into(), now.duration_since(*checkpoint).as_secs_f64());
    *checkpoint = now;
}
pub fn prove_with_options(
    srs: &PublicSrs,
    index: &ValidatedIndex,
    public: &[Fr],
    witness: &[Fr],
    rng: &mut impl RngCore,
    options: ProverOptions,
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
    let cs = checks(p, index)?;
    let round_scalars = cs.iter().map(|c| c.helper_coefficients).sum::<usize>();
    let semantic = gates::semantic_witness(witness, public)?;
    let mut salt = [0; 32];
    rng.try_fill_bytes(&mut salt).map_err(|e| e.to_string())?;
    let mut tx = Transcript::new(&context(p, index, public, &cs)?, salt);
    let mut wire = HEADER.to_vec();
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
    polys.insert("W".into(), protocol::witness_poly(p, witness, rng)?);
    let blind = sample_fr(rng)?;
    blinds.insert("W".into(), blind);
    let cw = pcs::commit(srs, &polys["W"], SourceKind::Source, blind)?;
    commits.insert("W".into(), cw);
    offsets.insert("witness".into(), wire.len());
    let block = cw.bytes();
    wire.extend(&block);
    tx.absorb("witness", &block)?;
    stage(&mut stages, &mut checkpoint, "witness_context_commitment");
    let fp = tx.challenge_mixed("copy_fingerprint", &[Domain::Nonzero, Domain::Field])?;
    let (beta, gamma) = (fp[0], fp[1]);
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
            protocol::tree_poly(p, leaves, name == "A", rng)?
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
    let mut rels = protocol::relations(p, index.gate(), beta, gamma);
    let mut locals = Vec::new();
    offsets.insert("helper".into(), wire.len());
    let mut helper_bytes = Vec::new();
    for c in &cs {
        let (local, ambient) = helper(p, c, rng)?;
        let blind = sample_fr(rng)?;
        let ch = pcs::commit(srs, &ambient, SourceKind::Helper, blind)?;
        helper_bytes.extend(ch.bytes());
        blinds.insert(c.handle(), blind);
        polys.insert(c.handle(), ambient);
        locals.push(local);
    }
    wire.extend(&helper_bytes);
    tx.absorb("native_helpers", &helper_bytes)?;
    let rho = packet(&mut tx, &mut rels, &cs)?;
    stage(&mut stages, &mut checkpoint, "trees_helper_commitments");
    polys.insert(
        "__public".into(),
        StructuredPolynomial::from_table(
            p.l(),
            p.l() - p.public_log(),
            DenseMle::new(public.to_vec())?,
        )?,
    );
    let mut engines = locals
        .into_iter()
        .enumerate()
        .map(|(j, h)| NativeSumcheck::new_native(p.l(), rels[j].clone(), &polys, h, rho[j]))
        .collect::<Result<Vec<_>>>()?;
    stage(&mut stages, &mut checkpoint, "native_compile_and_precheck");
    offsets.insert("rounds".into(), wire.len());
    let mut current = vec![Fr::zero(); cs.len()];
    let mut path = Vec::new();
    for a in 0..p.l() {
        let mut messages = Vec::new();
        let mut block = Vec::new();
        for (j, c) in cs.iter().enumerate().filter(|(_, c)| a >= c.suffix_offset) {
            let b = a - c.suffix_offset;
            let coeffs = round_coefficients(&mut engines[j], c.honest_caps[b], b == 0, current[j])?;
            block.extend(
                coeffs[if b == 0 { 2 } else { 1 }..]
                    .iter()
                    .flat_map(scalar_bytes),
            );
            messages.push((j, coeffs));
        }
        wire.extend(&block);
        tx.absorb(&format!("native_round_{a}"), &block)?;
        let r = tx.challenge(&format!("suffix_challenge_{a}"), 1, Domain::Nonboolean)?[0];
        for (j, coeffs) in messages {
            current[j] = native::univariate(&coeffs, r);
            engines[j].fold(r);
        }
        path.push(r);
    }
    let fold_pairs = engines.iter().map(|e| e.fold_pairs).sum();
    let sample_points = engines.iter().map(|e| e.sample_points).sum();
    drop(engines);
    stage(&mut stages, &mut checkpoint, "sumcheck_rounds");
    let mut ordered = queries(&path, &rels);
    let mut values = ordered
        .iter()
        .map(|q| polys[&q.handle].evaluate(&q.point))
        .collect::<Result<Vec<_>>>()?;
    offsets.insert("values".into(), wire.len());
    let block = values.iter().flat_map(scalar_bytes).collect::<Vec<_>>();
    wire.extend(&block);
    tx.absorb("endpoint_values", &block)?;
    let source_values = ordered.len();
    let derived = derive_endpoints(&path, &rels, &cs, &current, &rho, &mut |h, z| {
        polys[h].evaluate(z)
    })?;
    for (c, y) in cs.iter().zip(&derived) {
        if *y != polys[&c.handle()].evaluate(&c.point(&path))? {
            return Err("native helper endpoint mismatch".into());
        }
    }
    add_helper_queries(&mut ordered, &path, &cs);
    let derived_bytes = derived.iter().flat_map(scalar_bytes).collect::<Vec<_>>();
    tx.absorb("derived_native_helper_values", &derived_bytes)?;
    values.extend(derived);
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

    let expected = 37
        + (288 + 48 * cs.len())
        + 32 * (round_scalars + source_values)
        + 48 * buckets.len() * (p.l() + 1);
    if wire.len() != expected {
        return Err("communication ledger mismatch".into());
    }
    stage(&mut stages, &mut checkpoint, "final_transcript_and_ledger");
    let metrics = Metrics {
        seconds: start.elapsed().as_secs_f64(),
        proof_bytes: wire.len(),
        round_scalars,
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
    let start = Instant::now();
    let mut checkpoint = start;
    let mut stages = BTreeMap::new();
    if vk.dimension != p.l() || !index.matches(p, &vk.srs_digest) {
        return Err("index/SRS/profile mismatch".into());
    }
    let cs = checks(p, index)?;
    let round_scalars = cs.iter().map(|c| c.helper_coefficients).sum::<usize>();
    let templates = protocol::relations(p, index.gate(), Fr::one(), Fr::zero());
    let max_values = templates
        .iter()
        .map(|r| r.sources.iter().filter(|s| s.handle != "__public").count())
        .sum::<usize>();
    let max_bytes = 37
        + (288 + 48 * cs.len())
        + 32 * (round_scalars + max_values)
        + 48 * (max_values + cs.len()) * (p.l() + 1);
    if proof.len() > max_bytes {
        return Err("proof exceeds format bound".into());
    }
    let mut rd = Reader::new(proof);
    if rd.bytes(5)? != HEADER {
        return Err("proof header".into());
    }
    let salt: [u8; 32] = rd.bytes(32)?.try_into().unwrap();
    let mut tx = Transcript::new(&context(p, index, public, &cs)?, salt);
    let mut commits: BTreeMap<String, Commitment> = index
        .commitments()
        .iter()
        .map(|(n, c)| (n.clone(), Commitment::Source(*c)))
        .collect();
    let off = rd.position();
    commits.insert("W".into(), Commitment::Source(rd.g2()?));
    tx.absorb("witness", &proof[off..rd.position()])?;
    let fp = tx.challenge_mixed("copy_fingerprint", &[Domain::Nonzero, Domain::Field])?;
    let (beta, gamma) = (fp[0], fp[1]);
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
    let off = rd.position();
    for c in &cs {
        commits.insert(c.handle(), Commitment::Helper(rd.g1()?));
    }
    tx.absorb("native_helpers", &proof[off..rd.position()])?;
    let mut rels = protocol::relations(p, index.gate(), beta, gamma);
    let rho = packet(&mut tx, &mut rels, &cs)?;
    stage(
        &mut stages,
        &mut checkpoint,
        "context_commitment_decode_and_transcript",
    );
    let mut current = vec![Fr::zero(); cs.len()];
    let mut path = Vec::new();
    let half = Fr::from(2u64).inverse().unwrap();
    for a in 0..p.l() {
        let mut messages = vec![];
        let off = rd.position();
        for (j, c) in cs.iter().enumerate().filter(|(_, c)| a >= c.suffix_offset) {
            let b = a - c.suffix_offset;
            let count = c.honest_caps[b] - usize::from(b == 0);
            let tail = (0..count)
                .map(|_| rd.scalar())
                .collect::<Result<Vec<_>>>()?;
            let sum: Fr = tail.iter().sum();
            let mut coeffs = if b == 0 {
                vec![Fr::zero(), -sum]
            } else {
                vec![(current[j] - sum) * half]
            };
            coeffs.extend(tail);
            messages.push((j, coeffs));
        }
        tx.absorb(&format!("native_round_{a}"), &proof[off..rd.position()])?;
        let r = tx.challenge(&format!("suffix_challenge_{a}"), 1, Domain::Nonboolean)?[0];
        for (j, coeffs) in messages {
            current[j] = native::univariate(&coeffs, r);
        }
        path.push(r);
    }
    stage(&mut stages, &mut checkpoint, "sumcheck_transcript");
    let mut ordered = queries(&path, &rels);
    let off = rd.position();
    let mut values = (0..ordered.len())
        .map(|_| rd.scalar())
        .collect::<Result<Vec<_>>>()?;
    tx.absorb("endpoint_values", &proof[off..rd.position()])?;
    let public_poly = DenseMle::new(public.to_vec())?;
    let source_values = ordered.len();
    let derived = derive_endpoints(&path, &rels, &cs, &current, &rho, &mut |h, z| {
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
    add_helper_queries(&mut ordered, &path, &cs);
    let derived_bytes = derived.iter().flat_map(scalar_bytes).collect::<Vec<_>>();
    tx.absorb("derived_native_helper_values", &derived_bytes)?;
    values.extend(derived);
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
        round_scalars,
        source_values,
        opening_count: openings.len(),
        hash_packets: tx.query_count() as u64,
        fold_pairs: 0,
        sample_points: 0,
        offsets: BTreeMap::new(),
        stages,
        opening_cache: BTreeMap::new(),
    })
}
