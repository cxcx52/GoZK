//! Exact historical V5 trace-space PCS on the same BLS12-381 backend.
//!
//! The public key contains precisely the listed Boolean, trace and axis
//! generators. Suffix caches are public group sums. An accepted file is bound
//! to its complete support and certified extension polynomial; the digest is
//! an integrity identifier, not a proof of an honest setup ceremony.
use crate::{
    codec::{g1_bytes, g1_from_bytes, g2_bytes, g2_from_bytes, scalar_bytes, scalar_from_bytes},
    pcs::{Commitment, OpeningProof, VerificationKey},
    random::sample_fr,
    tables::StructuredPolynomial,
    trace::{ExtensionField, TraceMask, TraceQuotient},
    Result,
};
use ark_bls12_381::{Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{scalar_mul::fixed_base::FixedBase, AffineRepr, CurveGroup, Group, VariableBaseMSM};
use ark_ff::{One, PrimeField, Zero};
use rand::RngCore;
use sha2::{Digest, Sha256};
use std::{
    io::{Read, Write},
    sync::Arc,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceParameters {
    l: usize,
    t: usize,
    d: usize,
}
impl TraceParameters {
    pub fn new(l: usize, t: usize, d: usize) -> Result<Self> {
        if !(1..=25).contains(&l) || !(1..=4096).contains(&t) || d < t + 1 || d > 65536 {
            return Err("invalid trace PCS parameters".into());
        }
        Ok(Self { l, t, d })
    }
    pub fn l(&self) -> usize {
        self.l
    }
    pub fn t(&self) -> usize {
        self.t
    }
    pub fn d(&self) -> usize {
        self.d
    }
    /// Counts include one hiding generator in each group. Deliberate linear
    /// dependence of a listed basis does not change the support-list count.
    pub fn primary_counts(&self) -> (usize, usize) {
        (
            (1usize << (self.l - 1)) + self.l * (self.l + 1) * (self.t - 1) + self.l * self.d + 1,
            (1usize << self.l) + self.l * self.t + 1,
        )
    }
}

#[derive(Clone, Debug)]
pub struct ValidatedTraceSrs {
    parameters: TraceParameters,
    field: Arc<ExtensionField>,
    v_suffix: Vec<Vec<G2Affine>>,
    u_suffix: Vec<Vec<G1Affine>>,
    // j-major, component-minor; the two U blocks omit j=0.
    v_trace: Vec<G2Affine>,
    u_power: Vec<G1Affine>,
    u_axis_power: Vec<G1Affine>,
    // axis-major, degree 1..=D.
    u_axis: Vec<G1Affine>,
    zeta_g1: G1Affine,
    vk: VerificationKey,
}

fn boolean_weights(point: &[Fr]) -> Vec<Fr> {
    let mut row = vec![Fr::one()];
    for x in point {
        let mut next = Vec::with_capacity(row.len() * 2);
        for a in row {
            next.push(a * (Fr::one() - x));
            next.push(a * x);
        }
        row = next;
    }
    row
}
fn g1_fixed(values: &[Fr]) -> Vec<G1Affine> {
    if values.is_empty() {
        return vec![];
    }
    let bits = Fr::MODULUS_BIT_SIZE as usize;
    let w = FixedBase::get_mul_window_size(values.len());
    let table = FixedBase::get_window_table(bits, w, G1Projective::generator());
    G1Projective::normalize_batch(&FixedBase::msm::<G1Projective>(bits, w, &table, values))
}
fn g2_fixed(values: &[Fr]) -> Vec<G2Affine> {
    if values.is_empty() {
        return vec![];
    }
    let bits = Fr::MODULUS_BIT_SIZE as usize;
    let w = FixedBase::get_mul_window_size(values.len());
    let table = FixedBase::get_window_table(bits, w, G2Projective::generator());
    G2Projective::normalize_batch(&FixedBase::msm::<G2Projective>(bits, w, &table, values))
}
fn g1_suffix(primary: Vec<G1Affine>) -> Vec<Vec<G1Affine>> {
    let mut out = vec![primary];
    while out.last().unwrap().len() > 1 {
        let p = out.last().unwrap();
        let h = p.len() / 2;
        out.push(G1Projective::normalize_batch(
            &(0..h).map(|i| p[i] + p[i + h]).collect::<Vec<_>>(),
        ));
    }
    out
}
fn g2_suffix(primary: Vec<G2Affine>) -> Vec<Vec<G2Affine>> {
    let mut out = vec![primary];
    while out.last().unwrap().len() > 1 {
        let p = out.last().unwrap();
        let h = p.len() / 2;
        out.push(G2Projective::normalize_batch(
            &(0..h).map(|i| p[i] + p[i + h]).collect::<Vec<_>>(),
        ));
    }
    out
}

impl ValidatedTraceSrs {
    pub fn setup(
        parameters: TraceParameters,
        field: Arc<ExtensionField>,
        rng: &mut impl RngCore,
        max_primary_points: usize,
    ) -> Result<Self> {
        if field.degree() != parameters.l {
            return Err("extension dimension mismatch".into());
        }
        let (u, v) = parameters.primary_counts();
        if u.checked_add(v).ok_or("SRS count overflow")? > max_primary_points {
            return Err("SRS allocation bound exceeded".into());
        }
        let l = parameters.l;
        let tau = (0..l).map(|_| sample_fr(rng)).collect::<Result<Vec<_>>>()?;
        let mut zeta = sample_fr(rng)?;
        while zeta.is_zero() {
            zeta = sample_fr(rng)?;
        }
        let h = tau.iter().map(|x| *x * (Fr::one() - x)).collect::<Vec<_>>();
        let mut powers = vec![field.one()];
        for j in 1..parameters.t {
            powers.push(field.mul(&powers[j - 1], &tau)?);
        }
        let mut v_values = Vec::with_capacity(l * parameters.t);
        let mut u_values = Vec::with_capacity(l * (parameters.t - 1));
        for (j, power) in powers.iter().enumerate() {
            let hp = field.mul(&h, power)?;
            for a in 0..l {
                let e = field.basis(a)?;
                v_values.push(field.trace(&field.mul(&e, &hp)?)?);
                if j > 0 {
                    u_values.push(field.trace(&field.mul(&e, power)?)?);
                }
            }
        }
        let mut axis_power = Vec::with_capacity(l * u_values.len());
        for x in &tau {
            axis_power.extend(u_values.iter().map(|a| *x * a));
        }
        let mut axis = Vec::with_capacity(l * parameters.d);
        for x in &tau {
            let mut power = *x;
            for _ in 0..parameters.d {
                axis.push(power);
                power *= x;
            }
        }
        let mut out = Self {
            parameters,
            field,
            v_suffix: g2_suffix(g2_fixed(&boolean_weights(&tau))),
            u_suffix: g1_suffix(g1_fixed(&boolean_weights(&tau[1..]))),
            v_trace: g2_fixed(&v_values),
            u_power: g1_fixed(&u_values),
            u_axis_power: g1_fixed(&axis_power),
            u_axis: g1_fixed(&axis),
            zeta_g1: (G1Affine::generator() * zeta).into_affine(),
            vk: VerificationKey {
                dimension: l,
                tau_g2: g2_fixed(&tau),
                zeta_g2: (G2Affine::generator() * zeta).into_affine(),
                srs_digest: [0; 32],
            },
        };
        out.vk.srs_digest = out.digest();
        Ok(out)
    }
    pub fn parameters(&self) -> &TraceParameters {
        &self.parameters
    }
    pub fn field(&self) -> &Arc<ExtensionField> {
        &self.field
    }
    pub fn vk(&self) -> &VerificationKey {
        &self.vk
    }
    pub fn cached_point_counts(&self) -> (usize, usize) {
        (
            self.u_suffix.iter().map(Vec::len).sum::<usize>()
                + self.u_power.len()
                + self.u_axis_power.len()
                + self.u_axis.len()
                + 1,
            self.v_suffix.iter().map(Vec::len).sum::<usize>()
                + self.v_trace.len()
                + self.vk.tau_g2.len()
                + 1,
        )
    }
    fn digest(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"HyperPlonk-repair/trace-exact-SRS/v1\0");
        for n in [self.parameters.l, self.parameters.t, self.parameters.d] {
            h.update((n as u64).to_be_bytes());
        }
        h.update(b"extension/power-basis/Rabin");
        for c in self.field.modulus() {
            h.update(scalar_bytes(c));
        }
        h.update(b"V/full-Boolean");
        for p in &self.v_suffix[0] {
            h.update(g2_bytes(p));
        }
        h.update(b"V/trace-ea-H-Lj/j-major/0..T");
        for p in &self.v_trace {
            h.update(g2_bytes(p));
        }
        h.update(b"U/suffix-Boolean");
        for p in &self.u_suffix[0] {
            h.update(g1_bytes(p));
        }
        h.update(b"U/trace-ea-Lj/j-major/1..T");
        for p in &self.u_power {
            h.update(g1_bytes(p));
        }
        h.update(b"U/Xi-trace-ea-Lj/i-j-a/1..T");
        for p in &self.u_axis_power {
            h.update(g1_bytes(p));
        }
        h.update(b"U/Xi-d/i-degree/1..=D");
        for p in &self.u_axis {
            h.update(g1_bytes(p));
        }
        h.update(b"zeta/G1");
        h.update(g1_bytes(&self.zeta_g1));
        h.update(b"tau/G2");
        for p in &self.vk.tau_g2 {
            h.update(g2_bytes(p));
        }
        h.update(b"zeta/G2");
        h.update(g2_bytes(&self.vk.zeta_g2));
        h.finalize().into()
    }
    pub fn write_to(&self, w: &mut impl Write) -> Result<()> {
        let mut put = |b: &[u8]| w.write_all(b).map_err(|e| e.to_string());
        put(b"HP5SRS\0\x01")?;
        for n in [self.parameters.l, self.parameters.t, self.parameters.d] {
            put(&(n as u64).to_be_bytes())?;
        }
        for c in self.field.modulus() {
            put(&scalar_bytes(c))?;
        }
        put(&self.vk.srs_digest)?;
        for p in self.v_suffix[0].iter().chain(&self.v_trace) {
            put(&g2_bytes(p))?;
        }
        for p in self.u_suffix[0]
            .iter()
            .chain(&self.u_power)
            .chain(&self.u_axis_power)
            .chain(&self.u_axis)
        {
            put(&g1_bytes(p))?;
        }
        put(&g1_bytes(&self.zeta_g1))?;
        for p in &self.vk.tau_g2 {
            put(&g2_bytes(p))?;
        }
        put(&g2_bytes(&self.vk.zeta_g2))?;
        Ok(())
    }
    pub fn read_from(r: &mut impl Read, max_primary_points: usize) -> Result<Self> {
        fn take<const N: usize>(r: &mut impl Read) -> Result<[u8; N]> {
            let mut b = [0; N];
            r.read_exact(&mut b).map_err(|e| e.to_string())?;
            Ok(b)
        }
        if &take::<8>(r)? != b"HP5SRS\0\x01" {
            return Err("trace SRS format".into());
        }
        let mut pars = [0usize; 3];
        for n in &mut pars {
            *n = usize::try_from(u64::from_be_bytes(take(r)?))
                .map_err(|_| "SRS parameter overflow")?;
        }
        let parameters = TraceParameters::new(pars[0], pars[1], pars[2])?;
        let (u, v) = parameters.primary_counts();
        if u.checked_add(v).ok_or("SRS count overflow")? > max_primary_points {
            return Err("SRS allocation bound exceeded".into());
        }
        let (l, t, d) = (parameters.l, parameters.t, parameters.d);
        let modulus = (0..=l)
            .map(|_| scalar_from_bytes(&take::<32>(r)?))
            .collect::<Result<Vec<_>>>()?;
        let field = Arc::new(ExtensionField::from_modulus(modulus)?);
        let digest = take::<32>(r)?;
        let v_primary = (0..1usize << l)
            .map(|_| g2_from_bytes(&take::<96>(r)?))
            .collect::<Result<Vec<_>>>()?;
        let v_trace = (0..l * t)
            .map(|_| g2_from_bytes(&take::<96>(r)?))
            .collect::<Result<Vec<_>>>()?;
        let u_primary = (0..1usize << (l - 1))
            .map(|_| g1_from_bytes(&take::<48>(r)?))
            .collect::<Result<Vec<_>>>()?;
        let u_power = (0..l * (t - 1))
            .map(|_| g1_from_bytes(&take::<48>(r)?))
            .collect::<Result<Vec<_>>>()?;
        let u_axis_power = (0..l * l * (t - 1))
            .map(|_| g1_from_bytes(&take::<48>(r)?))
            .collect::<Result<Vec<_>>>()?;
        let u_axis = (0..l * d)
            .map(|_| g1_from_bytes(&take::<48>(r)?))
            .collect::<Result<Vec<_>>>()?;
        let zeta_g1 = g1_from_bytes(&take::<48>(r)?)?;
        let tau_g2 = (0..l)
            .map(|_| g2_from_bytes(&take::<96>(r)?))
            .collect::<Result<Vec<_>>>()?;
        let zeta_g2 = g2_from_bytes(&take::<96>(r)?)?;
        let mut trailing = [0; 1];
        if r.read(&mut trailing).map_err(|e| e.to_string())? != 0 {
            return Err("trailing trace SRS bytes".into());
        }
        let out = Self {
            parameters,
            field,
            v_suffix: g2_suffix(v_primary),
            u_suffix: g1_suffix(u_primary),
            v_trace,
            u_power,
            u_axis_power,
            u_axis,
            zeta_g1,
            vk: VerificationKey {
                dimension: l,
                tau_g2,
                zeta_g2,
                srs_digest: digest,
            },
        };
        if out.digest() != digest {
            return Err("trace SRS support digest mismatch".into());
        }
        Ok(out)
    }
    fn axis(&self, axis: usize, degree: usize) -> G1Affine {
        self.u_axis[axis * self.parameters.d + degree - 1]
    }
}

/// A source is an MLE plus one trace mask with exactly the key's budget.
/// Linear combinations merge trace coefficients without expanding monomials.
#[derive(Clone, Debug)]
pub struct TraceSource {
    dense: StructuredPolynomial,
    mask: Option<TraceMask>,
}
impl TraceSource {
    pub fn new(dense: StructuredPolynomial, mask: Option<TraceMask>) -> Result<Self> {
        if !dense.extras().is_empty() {
            return Err("trace source dense component has monomial extras".into());
        }
        if mask
            .as_ref()
            .is_some_and(|m| m.field().degree() != dense.dimension())
        {
            return Err("trace source mask dimension".into());
        }
        Ok(Self { dense, mask })
    }
    pub fn dense(&self) -> &StructuredPolynomial {
        &self.dense
    }
    pub fn mask(&self) -> Option<&TraceMask> {
        self.mask.as_ref()
    }
    pub fn evaluate(&self, p: &[Fr]) -> Result<Fr> {
        Ok(self.dense.evaluate(p)?
            + self
                .mask
                .as_ref()
                .map_or(Ok(Fr::zero()), |m| m.evaluate(p))?)
    }
    pub fn scaled(&self, c: Fr) -> Result<Self> {
        Self::new(
            self.dense.scaled(c),
            self.mask
                .as_ref()
                .map(|m| {
                    TraceMask::from_coefficients(
                        Arc::new(m.field().clone()),
                        m.coefficients()
                            .iter()
                            .map(|a| a.iter().map(|x| *x * c).collect())
                            .collect(),
                    )
                })
                .transpose()?,
        )
    }
    pub fn add(&self, b: &Self) -> Result<Self> {
        let mask = match (&self.mask, &b.mask) {
            (None, m) | (m, None) => m.clone(),
            (Some(a), Some(b)) => {
                if a.field().modulus() != b.field().modulus() || a.budget() != b.budget() {
                    return Err("trace mask combination parameters".into());
                }
                Some(TraceMask::from_coefficients(
                    Arc::new(a.field().clone()),
                    a.coefficients()
                        .iter()
                        .zip(b.coefficients())
                        .map(|(x, y)| x.iter().zip(y).map(|(a, b)| *a + b).collect())
                        .collect(),
                )?)
            }
        };
        Self::new(self.dense.add(&b.dense)?, mask)
    }
}
fn check_source(srs: &ValidatedTraceSrs, source: &TraceSource) -> Result<()> {
    if source.dense.dimension() != srs.parameters.l {
        return Err("trace source dimension".into());
    }
    if let Some(m) = source.mask() {
        if m.budget() != srs.parameters.t || m.field().modulus() != srs.field.modulus() {
            return Err("trace source support differs from SRS".into());
        }
    }
    Ok(())
}
fn pure_axis(e: &[usize]) -> Result<Option<(usize, usize)>> {
    let mut nonzero = e.iter().enumerate().filter(|(_, d)| **d > 0);
    let first = nonzero.next().map(|(a, d)| (a, *d));
    if nonzero.next().is_some() {
        return Err("helper monomial is not a pure axis".into());
    }
    Ok(first)
}
fn helper_dense(srs: &ValidatedTraceSrs, p: &StructuredPolynomial) -> Result<G1Projective> {
    let l = srs.parameters.l;
    if p.dimension() != l {
        return Err("helper dimension".into());
    }
    let mut out = G1Projective::zero();
    for term in p.terms() {
        let dim = term.table.dimension();
        let start = if dim == 0 { l } else { term.start };
        if start == 0 {
            return Err("helper dense table starts before suffix".into());
        }
        let basis = &srs.u_suffix[start - 1];
        let tail = l - start - dim;
        let values = term
            .table
            .values()
            .iter()
            .map(|v| *v * term.scale)
            .collect::<Vec<_>>();
        if tail == 0 {
            out += G1Projective::msm(basis, &values).map_err(|_| "helper dense MSM")?;
        } else {
            let sums = basis
                .chunks(1usize << tail)
                .map(|b| b.iter().map(|p| p.into_group()).sum())
                .collect::<Vec<G1Projective>>();
            out += G1Projective::msm(&G1Projective::normalize_batch(&sums), &values)
                .map_err(|_| "helper block MSM")?;
        }
    }
    for (e, c) in p.extras() {
        out += match pure_axis(e)? {
            None => G1Affine::generator() * c,
            Some((a, d)) => {
                if d > srs.parameters.d {
                    return Err("helper axis degree exceeds SRS".into());
                }
                srs.axis(a, d) * c
            }
        };
    }
    Ok(out)
}
pub fn commit_helper(
    srs: &ValidatedTraceSrs,
    p: &StructuredPolynomial,
    blind: Fr,
) -> Result<G1Affine> {
    Ok((helper_dense(srs, p)? + srs.zeta_g1 * blind).into_affine())
}
pub fn commit_source(srs: &ValidatedTraceSrs, p: &TraceSource, blind: Fr) -> Result<G2Affine> {
    check_source(srs, p)?;
    let l = srs.parameters.l;
    let mut out = srs.vk.zeta_g2 * blind;
    for term in p.dense.terms() {
        let dim = term.table.dimension();
        let start = if dim == 0 { l } else { term.start };
        let basis = &srs.v_suffix[start];
        let tail = l - start - dim;
        let values = term
            .table
            .values()
            .iter()
            .map(|v| *v * term.scale)
            .collect::<Vec<_>>();
        if tail == 0 {
            out += G2Projective::msm(basis, &values).map_err(|_| "source dense MSM")?;
        } else {
            let sums = basis
                .chunks(1usize << tail)
                .map(|b| b.iter().map(|p| p.into_group()).sum())
                .collect::<Vec<G2Projective>>();
            out += G2Projective::msm(&G2Projective::normalize_batch(&sums), &values)
                .map_err(|_| "source block MSM")?;
        }
    }
    if let Some(m) = p.mask() {
        let values = m
            .coefficients()
            .iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        out += G2Projective::msm(&srs.v_trace, &values).map_err(|_| "trace source MSM")?;
    }
    Ok(out.into_affine())
}
fn commit_trace_quotient(srs: &ValidatedTraceSrs, q: &TraceQuotient) -> Result<G1Projective> {
    let (l, t) = (srs.parameters.l, srs.parameters.t);
    if q.axis >= l
        || q.pure.len() != t
        || q.times_axis.len() != t
        || q.pure.iter().chain(&q.times_axis).any(|a| a.len() != l)
    {
        return Err("trace quotient support".into());
    }
    let mut out = G1Affine::generator() * srs.field.trace(&q.pure[0])?
        + srs.axis(q.axis, 1) * srs.field.trace(&q.times_axis[0])?;
    let pure = q.pure[1..].iter().flatten().copied().collect::<Vec<_>>();
    let times = q.times_axis[1..]
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    if !pure.is_empty() {
        out += G1Projective::msm(&srs.u_power, &pure).map_err(|_| "trace pure MSM")?;
        let stride = l * (t - 1);
        out += G1Projective::msm(
            &srs.u_axis_power[q.axis * stride..(q.axis + 1) * stride],
            &times,
        )
        .map_err(|_| "trace axis MSM")?;
    }
    Ok(out)
}
fn hide_quotients(
    srs: &ValidatedTraceSrs,
    mut quotients: Vec<G1Projective>,
    point: &[Fr],
    blind: Fr,
    rng: &mut impl RngCore,
) -> Result<OpeningProof> {
    let masks = (0..point.len())
        .map(|_| sample_fr(rng))
        .collect::<Result<Vec<_>>>()?;
    let mut constant = blind;
    let mut tail = G1Projective::zero();
    for (i, mask) in masks.iter().enumerate() {
        quotients[i] += srs.zeta_g1 * mask;
        constant += *mask * point[i];
        tail -= srs.axis(i, 1) * mask;
    }
    tail += G1Affine::generator() * constant;
    quotients.push(tail);
    Ok(OpeningProof {
        points: G1Projective::normalize_batch(&quotients),
    })
}
pub fn open_source(
    srs: &ValidatedTraceSrs,
    p: &TraceSource,
    point: &[Fr],
    blind: Fr,
    rng: &mut impl RngCore,
) -> Result<OpeningProof> {
    check_source(srs, p)?;
    if point.len() != srs.parameters.l {
        return Err("trace opening dimension".into());
    }
    let (_, q, _) = p.dense.canonical_quotients(point)?;
    let mut groups = q
        .iter()
        .map(|q| helper_dense(srs, q))
        .collect::<Result<Vec<_>>>()?;
    if let Some(mask) = p.mask() {
        for (group, q) in groups.iter_mut().zip(mask.quotients(point)?) {
            *group += commit_trace_quotient(srs, &q)?;
        }
    }
    hide_quotients(srs, groups, point, blind, rng)
}
pub fn open_helper(
    srs: &ValidatedTraceSrs,
    p: &StructuredPolynomial,
    point: &[Fr],
    blind: Fr,
    rng: &mut impl RngCore,
) -> Result<OpeningProof> {
    // Validate the original polynomial even if an unsupported term would vanish
    // after substitution. The honest helper API exposes the exact additive subspace.
    let _ = helper_dense(srs, p)?;
    if point.len() != srs.parameters.l {
        return Err("helper opening dimension".into());
    }
    let (_, q, _) = p.canonical_quotients(point)?;
    let groups = q
        .iter()
        .map(|q| helper_dense(srs, q))
        .collect::<Result<Vec<_>>>()?;
    hide_quotients(srs, groups, point, blind, rng)
}
pub fn source_commitment(
    srs: &ValidatedTraceSrs,
    p: &TraceSource,
    blind: Fr,
) -> Result<Commitment> {
    Ok(Commitment::Source(commit_source(srs, p, blind)?))
}
