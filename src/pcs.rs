//! Typed hiding PCS with Boolean Lagrange bases and structured quotients.
//!
//! Setup is an honest research setup, not a multiparty ceremony or secure
//! erasure implementation. Returned keys contain no trapdoor scalars. The
//! primary published bases span exactly the profile's U and V; suffix caches
//! are derived group sums and introduce no additional algebraic directions.
use std::collections::BTreeMap;
use std::io::{Read, Write};

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{
    pairing::Pairing, scalar_mul::fixed_base::FixedBase, AffineRepr, CurveGroup, Group,
    VariableBaseMSM,
};
use ark_ff::{Field, One, PrimeField, Zero};
use rand::RngCore;
use sha2::{Digest, Sha256};

use crate::codec::{g1_bytes, g1_from_bytes, g2_bytes, g2_from_bytes};
use crate::profile::ValidatedProfile;
use crate::random::sample_fr;
use crate::tables::StructuredPolynomial;
use crate::Result;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceKind {
    Source,
    Helper,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Commitment {
    Source(G2Affine),
    Helper(G1Affine),
}

impl Commitment {
    pub fn kind(&self) -> SourceKind {
        match self {
            Self::Source(_) => SourceKind::Source,
            Self::Helper(_) => SourceKind::Helper,
        }
    }
    pub fn bytes(&self) -> Vec<u8> {
        match self {
            Self::Source(p) => g2_bytes(p).to_vec(),
            Self::Helper(p) => g1_bytes(p).to_vec(),
        }
    }
    pub fn scale(&self, weight: Fr) -> Self {
        match self {
            Self::Source(p) => Self::Source((*p * weight).into_affine()),
            Self::Helper(p) => Self::Helper((*p * weight).into_affine()),
        }
    }
    pub fn add(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Self::Source(a), Self::Source(b)) => Ok(Self::Source((*a + *b).into_affine())),
            (Self::Helper(a), Self::Helper(b)) => Ok(Self::Helper((*a + *b).into_affine())),
            _ => Err("cannot combine different source groups".into()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct OpeningProof {
    pub points: Vec<G1Affine>,
}

#[derive(Clone, Debug)]
pub struct Opening {
    pub commitment: Commitment,
    pub point: Vec<Fr>,
    pub value: Fr,
    pub proof: OpeningProof,
}

/// Reuses deterministic dense quotient commitments across one opening batch.
/// Every proof still gets independently sampled hiding masks. Retained Arc
/// tables make process-local pointer keys safe from allocator-address reuse.
pub struct OpeningCache {
    srs_id: [u8; 32],
    retained: BTreeMap<usize, crate::tables::DenseMle>,
    commitments: BTreeMap<(usize, usize, Vec<[u8; 32]>), G1Affine>,
    pub hits: usize,
    pub misses: usize,
    pub msm_cells: usize,
}
impl OpeningCache {
    pub fn new(srs: &PublicSrs) -> Self {
        Self {
            srs_id: srs.vk.srs_digest,
            retained: BTreeMap::new(),
            commitments: BTreeMap::new(),
            hits: 0,
            misses: 0,
            msm_cells: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct VerificationKey {
    pub(crate) dimension: usize,
    pub(crate) tau_g2: Vec<G2Affine>,
    pub(crate) zeta_g2: G2Affine,
    pub(crate) srs_digest: [u8; 32],
}

impl VerificationKey {
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    pub fn tau_g2(&self) -> &[G2Affine] {
        &self.tau_g2
    }
    pub fn zeta_g2(&self) -> &G2Affine {
        &self.zeta_g2
    }
    pub fn srs_digest(&self) -> [u8; 32] {
        self.srs_digest
    }
}

/// Full bases occur only once. Later levels are suffix marginals, with total
/// storage less than twice the primary basis size in each source group.
#[derive(Clone, Debug)]
pub struct PublicSrs {
    profile: ValidatedProfile,
    v_suffix: Vec<Vec<G2Affine>>,
    u_suffix: Vec<Vec<G1Affine>>,
    v_extras: BTreeMap<Vec<usize>, G2Affine>,
    u_extras: BTreeMap<Vec<usize>, G1Affine>,
    v_monomials: BTreeMap<Vec<usize>, G2Affine>,
    u_monomials: BTreeMap<Vec<usize>, G1Affine>,
    zeta_g1: G1Affine,
    u_axes: Vec<G1Affine>,
    vk: VerificationKey,
}

fn boolean_weights(tau: &[Fr]) -> Vec<Fr> {
    let mut values = vec![Fr::one()];
    for t in tau {
        let mut next = Vec::with_capacity(values.len() * 2);
        for v in values {
            next.push(v * (Fr::one() - t));
            next.push(v * t);
        }
        values = next;
    }
    values
}

fn g1_fixed(values: &[Fr]) -> Vec<G1Affine> {
    let bits = Fr::MODULUS_BIT_SIZE as usize;
    let window = FixedBase::get_mul_window_size(values.len());
    let table = FixedBase::get_window_table(bits, window, G1Projective::generator());
    G1Projective::normalize_batch(&FixedBase::msm::<G1Projective>(
        bits, window, &table, values,
    ))
}

fn g2_fixed(values: &[Fr]) -> Vec<G2Affine> {
    let bits = Fr::MODULUS_BIT_SIZE as usize;
    let window = FixedBase::get_mul_window_size(values.len());
    let table = FixedBase::get_window_table(bits, window, G2Projective::generator());
    G2Projective::normalize_batch(&FixedBase::msm::<G2Projective>(
        bits, window, &table, values,
    ))
}

fn g1_suffix(primary: Vec<G1Affine>) -> Vec<Vec<G1Affine>> {
    let mut levels = vec![primary];
    while levels.last().unwrap().len() > 1 {
        let previous = levels.last().unwrap();
        let half = previous.len() / 2;
        let sums: Vec<_> = (0..half)
            .map(|i| previous[i] + previous[i + half])
            .collect();
        levels.push(G1Projective::normalize_batch(&sums));
    }
    levels
}

fn g2_suffix(primary: Vec<G2Affine>) -> Vec<Vec<G2Affine>> {
    let mut levels = vec![primary];
    while levels.last().unwrap().len() > 1 {
        let previous = levels.last().unwrap();
        let half = previous.len() / 2;
        let sums: Vec<_> = (0..half)
            .map(|i| previous[i] + previous[i + half])
            .collect();
        levels.push(G2Projective::normalize_batch(&sums));
    }
    levels
}

fn monomial(tau: &[Fr], exponent: &[usize]) -> Fr {
    tau.iter()
        .zip(exponent)
        .map(|(t, e)| t.pow([*e as u64]))
        .product()
}

// Both the geometric masks and the projected universal masks use only the
// prefix through the columns and the last axis. Lookup includes the two
// tree/helper leading axes in this prefix, including the extra padding axis
// for k=1. Quotients can only delete
// axes, so this Boolean cube also covers all multilinear quotient fragments.
// Pure row axes are needed by the independent sumcheck helper polynomial.
fn cache_axes(profile: &ValidatedProfile, helper: bool) -> Vec<usize> {
    let first = usize::from(helper);
    let mut axes: Vec<_> = (first..profile.l() - profile.nu()).collect();
    let last = profile.l() - 1;
    // With nu=0 the last axis is already in the prefix. With L=1 the helper
    // Boolean block is constant and has no axes at all.
    if last >= first && !axes.contains(&last) {
        axes.push(last);
    }
    axes
}

fn cache_exponent(dimension: usize, axes: &[usize], index: usize) -> Vec<usize> {
    let mut exponent = vec![0; dimension];
    for (bit, axis) in axes.iter().enumerate() {
        exponent[*axis] = (index >> (axes.len() - 1 - bit)) & 1;
    }
    exponent
}

fn cached_monomials(profile: &ValidatedProfile, helper: bool) -> Vec<Vec<usize>> {
    use std::collections::BTreeSet;
    let axes = cache_axes(profile, helper);
    let mut result: BTreeSet<_> = (0..1usize << axes.len())
        .map(|index| cache_exponent(profile.l(), &axes, index))
        .collect();
    for axis in usize::from(helper)..profile.l() {
        let mut exponent = vec![0; profile.l()];
        exponent[axis] = 1;
        result.insert(exponent);
    }
    result.into_iter().collect()
}

/// Marginalize the middle row coordinates, then apply the superset zeta
/// transform. Its output at mask a is sum_{b superset a} L_b(tau), hence the
/// monomial tau^a. No trapdoor or extra algebraic direction is introduced.
/// For M=2^L, c>=1 and nu>=1 this costs M+2kc G2 additions and
/// M/2+k(c-1) G1 additions before the remaining pure row axes. The subcube
/// uses O(k) projective points, plus O(L) points for batched row-axis
/// normalization. The two groups are processed sequentially when loading.
fn derive_cached_monomials<A: AffineRepr>(
    profile: &ValidatedProfile,
    helper: bool,
    suffix: &[Vec<A>],
) -> BTreeMap<Vec<usize>, A> {
    let axes = cache_axes(profile, helper);
    let primary = &suffix[0];
    let mut cube = Vec::with_capacity(1usize << axes.len());
    if profile.nu() == 0 {
        cube.extend(primary.iter().map(|point| point.into_group()));
    } else {
        let width = 1usize << profile.nu();
        for rows in primary.chunks_exact(width) {
            let mut even = rows[0].into_group();
            let mut odd = rows[1].into_group();
            for pair in rows[2..].chunks_exact(2) {
                even += pair[0];
                odd += pair[1];
            }
            cube.push(even);
            cube.push(odd);
        }
    }
    debug_assert_eq!(cube.len(), 1usize << axes.len());
    for bit in 0..axes.len() {
        let half = 1usize << bit;
        for block in cube.chunks_exact_mut(2 * half) {
            let (zero, one) = block.split_at_mut(half);
            for (target, source) in zero.iter_mut().zip(one) {
                *target += *source;
            }
        }
    }
    let mut keys: Vec<_> = (0..cube.len())
        .map(|index| cache_exponent(profile.l(), &axes, index))
        .collect();
    // Use the shrinking suffix marginals for the other pure axes. Their
    // combined input length is less than 2^nu, rather than one M-point scan
    // per axis. The helper excludes global axis zero by construction.
    for axis in usize::from(helper)..profile.l() {
        if axes.contains(&axis) {
            continue;
        }
        let basis = &suffix[axis - usize::from(helper)];
        let half = basis.len() / 2;
        let mut value = basis[half].into_group();
        for point in &basis[half + 1..] {
            value += *point;
        }
        let mut exponent = vec![0; profile.l()];
        exponent[axis] = 1;
        keys.push(exponent);
        cube.push(value);
    }
    keys.into_iter()
        .zip(A::Group::normalize_batch(&cube))
        .collect()
}

pub fn setup(profile: &ValidatedProfile, rng: &mut impl RngCore) -> Result<PublicSrs> {
    PublicSrs::setup(profile.clone(), rng)
}

impl PublicSrs {
    pub fn setup(profile: ValidatedProfile, rng: &mut impl RngCore) -> Result<Self> {
        let l = profile.l();
        let tau: Vec<Fr> = (0..l).map(|_| sample_fr(rng)).collect::<Result<_>>()?;
        let mut zeta = sample_fr(rng)?;
        while zeta.is_zero() {
            zeta = sample_fr(rng)?;
        }
        let v_primary = g2_fixed(&boolean_weights(&tau));
        let u_primary = g1_fixed(&boolean_weights(&tau[1..]));
        let v_exponents = profile.v_extras();
        let u_exponents = profile.u_extras();
        let v_values: Vec<_> = v_exponents.iter().map(|e| monomial(&tau, e)).collect();
        let u_values: Vec<_> = u_exponents.iter().map(|e| monomial(&tau, e)).collect();
        let v_extras = v_exponents.into_iter().zip(g2_fixed(&v_values)).collect();
        let u_extras = u_exponents.into_iter().zip(g1_fixed(&u_values)).collect();
        let vk = VerificationKey {
            dimension: l,
            tau_g2: g2_fixed(&tau),
            zeta_g2: (G2Affine::generator() * zeta).into_affine(),
            srs_digest: [0; 32],
        };
        let vm = cached_monomials(&profile, false);
        let um = cached_monomials(&profile, true);
        let vm_values: Vec<_> = vm.iter().map(|e| monomial(&tau, e)).collect();
        let um_values: Vec<_> = um.iter().map(|e| monomial(&tau, e)).collect();
        let mut result = Self {
            profile,
            v_suffix: g2_suffix(v_primary),
            u_suffix: g1_suffix(u_primary),
            v_extras,
            u_extras,
            zeta_g1: (G1Affine::generator() * zeta).into_affine(),
            v_monomials: vm.into_iter().zip(g2_fixed(&vm_values)).collect(),
            u_monomials: um.into_iter().zip(g1_fixed(&um_values)).collect(),
            u_axes: g1_fixed(&tau),
            vk,
        };
        result.vk.srs_digest = result.digest();
        // No trapdoor is returned. This does not promise memory erasure.
        Ok(result)
    }

    pub fn profile(&self) -> &ValidatedProfile {
        &self.profile
    }
    pub fn vk(&self) -> &VerificationKey {
        &self.vk
    }
    pub fn primary_point_counts(&self) -> (usize, usize) {
        (
            self.u_suffix[0].len() + self.u_extras.len() + 1,
            self.v_suffix[0].len() + self.v_extras.len() + 1,
        )
    }
    pub fn cached_point_counts(&self) -> (usize, usize) {
        (
            self.u_suffix.iter().map(Vec::len).sum::<usize>()
                + self.u_extras.len()
                + self.u_axes.len()
                + self.u_monomials.len()
                + 1,
            self.v_suffix.iter().map(Vec::len).sum::<usize>()
                + self.v_extras.len()
                + self.vk.tau_g2.len()
                + self.v_monomials.len()
                + 1,
        )
    }

    fn digest(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"HyperPlonk-repair-v7/lagrange-typed-SRS/v1\0");
        for n in self.parameters() {
            h.update(n.to_be_bytes());
        }
        h.update(b"V/G2/full-Boolean");
        h.update((self.v_suffix[0].len() as u64).to_be_bytes());
        for p in &self.v_suffix[0] {
            h.update(g2_bytes(p));
        }
        h.update(b"V/G2/extras");
        for (e, p) in &self.v_extras {
            for n in e {
                h.update((*n as u64).to_be_bytes());
            }
            h.update(g2_bytes(p));
        }
        h.update(b"U/G1/suffix-Boolean");
        h.update((self.u_suffix[0].len() as u64).to_be_bytes());
        for p in &self.u_suffix[0] {
            h.update(g1_bytes(p));
        }
        h.update(b"U/G1/extras");
        for (e, p) in &self.u_extras {
            for n in e {
                h.update((*n as u64).to_be_bytes());
            }
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

    fn parameters(&self) -> [u64; 6] {
        [
            self.profile.nu() as u64,
            self.profile.c() as u64,
            self.profile.public_log() as u64,
            self.profile.degree() as u64,
            self.profile.anchor() as u64,
            self.profile.flags(),
        ]
    }

    /// Streaming public-key format. Suffix caches and U axes are reconstructed
    /// on loading, never accepted as independently supplied SRS directions.
    pub fn write_to(&self, writer: &mut impl Write) -> Result<()> {
        let mut put = |bytes: &[u8]| writer.write_all(bytes).map_err(|e| e.to_string());
        put(b"HP7SRS\0\x01")?;
        for n in self.parameters() {
            put(&n.to_be_bytes())?;
        }
        put(&self.vk.srs_digest)?;
        for p in &self.v_suffix[0] {
            put(&g2_bytes(p))?;
        }
        for p in self.v_extras.values() {
            put(&g2_bytes(p))?;
        }
        for p in &self.u_suffix[0] {
            put(&g1_bytes(p))?;
        }
        for p in self.u_extras.values() {
            put(&g1_bytes(p))?;
        }
        put(&g1_bytes(&self.zeta_g1))?;
        for p in &self.vk.tau_g2 {
            put(&g2_bytes(p))?;
        }
        put(&g2_bytes(&self.vk.zeta_g2))?;
        Ok(())
    }

    /// Checked offline loading. `max_primary_points` is an allocation bound
    /// supplied by the experiment runner; the stored digest is not a ceremony
    /// proof. An external trusted SRS ID remains part of the setup contract.
    pub fn read_from(reader: &mut impl Read, max_primary_points: usize) -> Result<Self> {
        fn take<const N: usize>(r: &mut impl Read) -> Result<[u8; N]> {
            let mut b = [0; N];
            r.read_exact(&mut b).map_err(|e| e.to_string())?;
            Ok(b)
        }
        if &take::<8>(reader)? != b"HP7SRS\0\x01" {
            return Err("SRS format mismatch".into());
        }
        let mut par = [0usize; 6];
        for n in &mut par {
            *n = usize::try_from(u64::from_be_bytes(take(reader)?))
                .map_err(|_| "parameter overflow")?;
        }
        // Bound dimensions before generic profiles enumerate their finite
        // extra blocks. A caller-selected point limit is also an input cap.
        let ell = par[0]
            .checked_add(par[1])
            .and_then(|m| m.checked_add(1))
            .ok_or("SRS dimension overflow")?;
        let dimension = if par[5] & 4 != 0 {
            ell.max(par[0].checked_add(2).ok_or("SRS dimension overflow")?)
        } else {
            ell
        };
        if dimension >= usize::BITS as usize
            || (1usize << dimension) > max_primary_points
            || par[3] > max_primary_points
        {
            return Err("SRS allocation bound exceeded".into());
        }
        let profile = ValidatedProfile::from_flags(
            par[0],
            par[1],
            par[2],
            par[3],
            Some(par[4]),
            par[5] as u64,
        )?;
        let l = profile.l();
        let v_count = 1usize
            .checked_shl(l as u32)
            .ok_or("SRS dimension overflow")?;
        let u_count = v_count / 2;
        // Use symbolic counts before enumerating even the small extra blocks:
        // malformed public parameters must not trigger huge allocations first.
        let total = profile
            .v_count()
            .checked_add(profile.u_count())
            .ok_or("SRS size overflow")?;
        if total > max_primary_points {
            return Err("SRS allocation bound exceeded".into());
        }
        let expected_digest = take::<32>(reader)?;
        let mut v_primary = Vec::with_capacity(v_count);
        while v_primary.len() < v_count {
            let count = (v_count - v_primary.len()).min(4096);
            let mut bytes = vec![0u8; 96 * count];
            reader.read_exact(&mut bytes).map_err(|e| e.to_string())?;
            #[cfg(feature = "parallel")]
            {
                use rayon::prelude::*;
                let points = bytes
                    .par_chunks_exact(96)
                    .map(g2_from_bytes)
                    .collect::<Result<Vec<_>>>()?;
                v_primary.extend(points);
            }
            #[cfg(not(feature = "parallel"))]
            {
                for bytes in bytes.chunks_exact(96) {
                    v_primary.push(g2_from_bytes(bytes)?);
                }
            }
        }
        let v_extras = profile
            .v_extras()
            .into_iter()
            .map(|e| Ok((e, g2_from_bytes(&take::<96>(reader)?)?)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let mut u_primary = Vec::with_capacity(u_count);
        while u_primary.len() < u_count {
            let count = (u_count - u_primary.len()).min(4096);
            let mut bytes = vec![0u8; 48 * count];
            reader.read_exact(&mut bytes).map_err(|e| e.to_string())?;
            #[cfg(feature = "parallel")]
            {
                use rayon::prelude::*;
                let points = bytes
                    .par_chunks_exact(48)
                    .map(g1_from_bytes)
                    .collect::<Result<Vec<_>>>()?;
                u_primary.extend(points);
            }
            #[cfg(not(feature = "parallel"))]
            {
                for bytes in bytes.chunks_exact(48) {
                    u_primary.push(g1_from_bytes(bytes)?);
                }
            }
        }
        let u_extras = profile
            .u_extras()
            .into_iter()
            .map(|e| Ok((e, g1_from_bytes(&take::<48>(reader)?)?)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let zeta_g1 = g1_from_bytes(&take::<48>(reader)?)?;
        let tau_g2 = (0..l)
            .map(|_| g2_from_bytes(&take::<96>(reader)?))
            .collect::<Result<Vec<_>>>()?;
        let zeta_g2 = g2_from_bytes(&take::<96>(reader)?)?;
        let mut trailing = [0; 1];
        if reader.read(&mut trailing).map_err(|e| e.to_string())? != 0 {
            return Err("trailing SRS bytes".into());
        }
        let mut result = Self {
            profile,
            v_suffix: g2_suffix(v_primary),
            u_suffix: g1_suffix(u_primary),
            v_extras,
            u_extras,
            v_monomials: BTreeMap::new(),
            u_monomials: BTreeMap::new(),
            zeta_g1,
            u_axes: Vec::new(),
            vk: VerificationKey {
                dimension: l,
                tau_g2,
                zeta_g2,
                srs_digest: expected_digest,
            },
        };
        if result.digest() != expected_digest {
            return Err("SRS digest mismatch".into());
        }
        result.v_monomials = derive_cached_monomials(&result.profile, false, &result.v_suffix);
        result.u_monomials = derive_cached_monomials(&result.profile, true, &result.u_suffix);
        // Derive X_0 from its U extra, and X_i (i>=1) from suffix MLE bases.
        let mut first_axis = vec![0; l];
        first_axis[0] = 1;
        result.u_axes.push(
            *result
                .u_extras
                .get(&first_axis)
                .ok_or("missing U axis zero")?,
        );
        for axis in 1..l {
            let mut exponent = vec![0; l];
            exponent[axis] = 1;
            result.u_axes.push(
                *result
                    .u_monomials
                    .get(&exponent)
                    .expect("cached helper axis"),
            );
        }
        Ok(result)
    }
}

fn supported(srs: &PublicSrs, poly: &StructuredPolynomial, kind: SourceKind) -> Result<()> {
    if poly.dimension() != srs.profile.l() {
        return Err("polynomial dimension mismatch".into());
    }
    for term in poly.terms() {
        if kind == SourceKind::Helper && term.start == 0 && term.table.dimension() != 0 {
            return Err("helper dense MLE must start at suffix axis one or later".into());
        }
    }
    for e in poly.extras().keys() {
        let ok = match kind {
            SourceKind::Source => srs.profile.contains_v(e),
            SourceKind::Helper => srs.profile.contains_u(e),
        };
        if !ok {
            return Err("polynomial outside actual typed support".into());
        }
    }
    Ok(())
}

fn mle_monomial_g1(srs: &PublicSrs, e: &[usize]) -> G1Projective {
    // Generic sparse multilinear fallback. Protocol masks and their quotients
    // use the derived geometric cache; dense terms use Lagrange-table MSMs.
    srs.u_suffix[0]
        .iter()
        .enumerate()
        .filter(|(index, _)| {
            e[1..]
                .iter()
                .enumerate()
                .all(|(a, p)| *p == 0 || ((index >> (e.len() - 2 - a)) & 1) == 1)
        })
        .map(|(_, p)| p.into_group())
        .sum()
}
fn mle_monomial_g2(srs: &PublicSrs, e: &[usize]) -> G2Projective {
    srs.v_suffix[0]
        .iter()
        .enumerate()
        .filter(|(index, _)| {
            e.iter()
                .enumerate()
                .all(|(a, p)| *p == 0 || ((index >> (e.len() - 1 - a)) & 1) == 1)
        })
        .map(|(_, p)| p.into_group())
        .sum()
}

pub fn commit_source(srs: &PublicSrs, poly: &StructuredPolynomial, blind: Fr) -> Result<G2Affine> {
    supported(srs, poly, SourceKind::Source)?;
    let mut result = srs.vk.zeta_g2 * blind;
    for term in poly.terms() {
        let dim = term.table.dimension();
        let start = if dim == 0 {
            poly.dimension()
        } else {
            term.start
        };
        let basis = &srs.v_suffix[start];
        let trailing = poly.dimension() - start - dim;
        let scalars: Vec<_> = term
            .table
            .values()
            .iter()
            .map(|v| *v * term.scale)
            .collect();
        if trailing == 0 {
            result += G2Projective::msm(basis, &scalars).map_err(|_| "G2 MSM size mismatch")?;
        } else {
            let width = 1usize << trailing;
            let sums: Vec<G2Projective> = basis
                .chunks(width)
                .map(|chunk| chunk.iter().map(|p| p.into_group()).sum())
                .collect();
            result += G2Projective::msm(&G2Projective::normalize_batch(&sums), &scalars)
                .map_err(|_| "G2 block MSM size mismatch")?;
        }
    }
    let (bases, scalars): (Vec<_>, Vec<_>) = poly
        .extras()
        .iter()
        .map(|(e, c)| {
            (
                srs.v_extras
                    .get(e)
                    .or_else(|| srs.v_monomials.get(e))
                    .copied()
                    .unwrap_or_else(|| mle_monomial_g2(srs, e).into_affine()),
                *c,
            )
        })
        .unzip();
    if !bases.is_empty() {
        result += G2Projective::msm(&bases, &scalars).map_err(|_| "G2 sparse MSM mismatch")?;
    }
    Ok(result.into_affine())
}

pub fn commit_helper(srs: &PublicSrs, poly: &StructuredPolynomial, blind: Fr) -> Result<G1Affine> {
    supported(srs, poly, SourceKind::Helper)?;
    let mut result = srs.zeta_g1 * blind;
    for term in poly.terms() {
        let dim = term.table.dimension();
        let start = if dim == 0 {
            poly.dimension()
        } else {
            term.start
        };
        let basis = &srs.u_suffix[start - 1];
        let trailing = poly.dimension() - start - dim;
        let scalars: Vec<_> = term
            .table
            .values()
            .iter()
            .map(|v| *v * term.scale)
            .collect();
        if trailing == 0 {
            result += G1Projective::msm(basis, &scalars).map_err(|_| "G1 MSM size mismatch")?;
        } else {
            let width = 1usize << trailing;
            let sums: Vec<G1Projective> = basis
                .chunks(width)
                .map(|chunk| chunk.iter().map(|p| p.into_group()).sum())
                .collect();
            result += G1Projective::msm(&G1Projective::normalize_batch(&sums), &scalars)
                .map_err(|_| "G1 block MSM size mismatch")?;
        }
    }
    let (bases, scalars): (Vec<_>, Vec<_>) = poly
        .extras()
        .iter()
        .map(|(e, c)| {
            (
                srs.u_extras
                    .get(e)
                    .or_else(|| srs.u_monomials.get(e))
                    .copied()
                    .unwrap_or_else(|| mle_monomial_g1(srs, e).into_affine()),
                *c,
            )
        })
        .unzip();
    if !bases.is_empty() {
        result += G1Projective::msm(&bases, &scalars).map_err(|_| "G1 sparse MSM mismatch")?;
    }
    Ok(result.into_affine())
}

pub fn commit(
    srs: &PublicSrs,
    poly: &StructuredPolynomial,
    kind: SourceKind,
    blind: Fr,
) -> Result<Commitment> {
    match kind {
        SourceKind::Source => Ok(Commitment::Source(commit_source(srs, poly, blind)?)),
        SourceKind::Helper => Ok(Commitment::Helper(commit_helper(srs, poly, blind)?)),
    }
}

pub fn open_polynomial(
    srs: &PublicSrs,
    poly: &StructuredPolynomial,
    kind: SourceKind,
    point: &[Fr],
    blind: Fr,
    rng: &mut impl RngCore,
) -> Result<OpeningProof> {
    supported(srs, poly, kind)?;
    if point.len() != srs.vk.dimension {
        return Err("opening dimension mismatch".into());
    }
    let (_, quotients, _) = poly.canonical_quotients(point)?;
    let masks: Vec<_> = (0..point.len())
        .map(|_| sample_fr(rng))
        .collect::<Result<_>>()?;
    let mut points = Vec::with_capacity(point.len() + 1);
    for (quotient, mask) in quotients.iter().zip(&masks) {
        points.push(commit_helper(srs, quotient, *mask)?);
    }
    let constant = blind + masks.iter().zip(point).map(|(s, z)| *s * z).sum::<Fr>();
    let mut tail = G1Affine::generator() * constant;
    for (axis, mask) in srs.u_axes.iter().zip(&masks) {
        tail -= *axis * mask;
    }
    points.push(tail.into_affine());
    Ok(OpeningProof { points })
}

pub fn open_cached(
    srs: &PublicSrs,
    poly: &StructuredPolynomial,
    kind: SourceKind,
    point: &[Fr],
    blind: Fr,
    rng: &mut impl RngCore,
    cache: &mut OpeningCache,
) -> Result<OpeningProof> {
    supported(srs, poly, kind)?;
    if point.len() != srs.vk.dimension || cache.srs_id != srs.vk.srs_digest {
        return Err("opening cache key or dimension mismatch".into());
    }
    let masks = (0..point.len())
        .map(|_| sample_fr(rng))
        .collect::<Result<Vec<_>>>()?;
    let sparse = StructuredPolynomial::new(poly.dimension(), vec![], poly.extras().clone())?;
    let (_, quotients, _) = sparse.canonical_quotients(point)?;
    let mut points = quotients
        .iter()
        .zip(&masks)
        .map(|(q, s)| commit_helper(srs, q, *s).map(|p| p.into_group()))
        .collect::<Result<Vec<_>>>()?;
    for term in poly.terms() {
        let id = term.table.storage_id();
        cache
            .retained
            .entry(id)
            .or_insert_with(|| term.table.clone());
        let mut row = term.table.values().to_vec();
        let mut prefix = vec![];
        for axis in term.start..term.start + term.table.dimension() {
            let half = row.len() / 2;
            let key = (id, term.start, prefix.clone());
            let cached = cache.commitments.get(&key).copied();
            let mut difference = if cached.is_none() {
                vec![Fr::zero(); half]
            } else {
                vec![]
            };
            crate::parallel::fold_pairs(
                &mut row,
                point[axis],
                if cached.is_none() {
                    Some(&mut difference)
                } else {
                    None
                },
            );
            row.truncate(half);
            let commitment = if let Some(c) = cached {
                cache.hits += 1;
                c
            } else {
                let q = StructuredPolynomial::from_table(
                    poly.dimension(),
                    axis + 1,
                    crate::tables::DenseMle::new(difference)?,
                )?;
                let c = commit_helper(srs, &q, Fr::zero())?;
                cache.commitments.insert(key, c);
                cache.misses += 1;
                cache.msm_cells += half;
                c
            };
            points[axis] += commitment * term.scale;
            prefix.push(crate::codec::scalar_bytes(&point[axis]));
        }
    }
    let constant = blind + masks.iter().zip(point).map(|(s, z)| *s * z).sum::<Fr>();
    let mut tail = G1Affine::generator() * constant;
    for (axis, mask) in srs.u_axes.iter().zip(&masks) {
        tail -= *axis * mask;
    }
    points.push(tail);
    Ok(OpeningProof {
        points: G1Projective::normalize_batch(&points),
    })
}

fn valid_g1(p: &G1Affine) -> bool {
    p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve()
}
fn valid_g2(p: &G2Affine) -> bool {
    p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve()
}
fn valid(vk: &VerificationKey, op: &Opening) -> bool {
    vk.dimension > 0
        && vk.tau_g2.len() == vk.dimension
        && op.point.len() == vk.dimension
        && op.proof.points.len() == vk.dimension + 1
        && op.proof.points.iter().all(valid_g1)
        && match &op.commitment {
            Commitment::Source(p) => valid_g2(p),
            Commitment::Helper(p) => valid_g1(p),
        }
}

pub fn verify_opening(vk: &VerificationKey, opening: &Opening) -> bool {
    if !valid(vk, opening) {
        return false;
    }
    let mut a = Vec::with_capacity(vk.dimension + 2);
    let mut b = Vec::with_capacity(vk.dimension + 2);
    match opening.commitment {
        Commitment::Source(p) => {
            a.push(G1Affine::generator());
            b.push((p.into_group() - G2Affine::generator() * opening.value).into_affine());
        }
        Commitment::Helper(p) => {
            a.push((p.into_group() - G1Affine::generator() * opening.value).into_affine());
            b.push(G2Affine::generator());
        }
    }
    for ((tau, z), proof) in vk
        .tau_g2
        .iter()
        .zip(&opening.point)
        .zip(&opening.proof.points)
    {
        a.push(-*proof);
        b.push((tau.into_group() - G2Affine::generator() * z).into_affine());
    }
    a.push(-opening.proof.points[vk.dimension]);
    b.push(vk.zeta_g2);
    Bls12_381::multi_pairing(a, b).is_zero()
}

/// Weights must come from an independently domain-separated transcript after
/// ALL opening bytes have been frozen, or from fresh verifier-private coins.
/// This algebraic function cannot enforce that external ordering. Predictable
/// weights can allow malicious cancellation; callers must account for FS
/// grinding in their security model. Mixed groups use L+3 Miller terms.
pub fn cross_bucket_verify(vk: &VerificationKey, openings: &[Opening], weights: &[Fr]) -> bool {
    if openings.is_empty()
        || openings.len() != weights.len()
        || !openings.iter().all(|op| valid(vk, op))
    {
        return false;
    }
    let mut summed = vec![G1Projective::zero(); vk.dimension];
    let mut tail = G1Projective::zero();
    let mut correction = G1Projective::zero();
    let mut left_g2 = G2Projective::zero();
    let mut has_source = false;
    for (op, weight) in openings.iter().zip(weights) {
        for (axis, sum) in summed.iter_mut().enumerate() {
            let weighted = op.proof.points[axis] * weight;
            *sum += weighted;
            correction -= weighted * op.point[axis];
        }
        tail += op.proof.points[vk.dimension] * weight;
        match op.commitment {
            Commitment::Source(p) => {
                has_source = true;
                left_g2 += (p.into_group() - G2Affine::generator() * op.value) * weight;
            }
            Commitment::Helper(p) => {
                correction -= (p.into_group() - G1Affine::generator() * op.value) * weight;
            }
        }
    }
    summed.push(tail);
    summed.push(correction);
    let mut a = G1Projective::normalize_batch(&summed);
    let mut b = vk.tau_g2.clone();
    b.push(vk.zeta_g2);
    b.push(G2Affine::generator());
    if has_source {
        a.push(-G1Affine::generator());
        b.push(left_g2.into_affine());
    }
    Bls12_381::multi_pairing(a, b).is_zero()
}

#[cfg(test)]
#[path = "pcs_cache_tests.rs"]
mod cache_tests;
