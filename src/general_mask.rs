//! Source masking for arbitrary sets of distinct non-Boolean projected
//! points. W retains Z and every column coordinate; A and B retain their
//! first and last coordinates. Distinct full queries to one source must have
//! distinct projections for this guarantee.
//!
//! On a legal non-Boolean path r (zero-based indices), the W projections are
//! (r_c, b) for Boolean columns b, (0, r[1..=c]), and (r_0, r[1..=c]).
//! The five projections of each tree are (1,last), (0,last), (r_1,0),
//! (r_1,1), (r_0,last), where last is the final path coordinate. They are
//! distinct within each source, including when all challenges coincide.
//! The separate uniform A and B masks hide all ten tree values jointly;
//! applying the common root-difference observation gives the nine outputs.
//!
//! For the full-coordinate version in s variables, the same family's basis
//! size is sum_j binom(s,j)*h_j. Here h_j counts its positive-support
//! exponents on j chosen axes, and positivity makes j<=1+floor(log2 T).
//! For T=10 the counts by j>=1 are [10,34,25,4], for T=5 [5,11,3].
//! These are construction costs, not bounds required of other masks.
use crate::{profile::ValidatedProfile, random::sample_fr, Result};
use ark_bls12_381::Fr;
use rand::RngCore;
use std::collections::{BTreeMap, BTreeSet};

pub const PROFILE_FLAG: u64 = 8;

#[derive(Clone, Copy)]
pub(crate) enum Source {
    Witness,
    Tree,
}

fn parameters(c: usize, l: usize, source: Source) -> (Vec<usize>, usize) {
    match source {
        Source::Witness => ((0..=c).collect(), (1usize << c) + 2),
        Source::Tree => (vec![0, l - 1], 5),
    }
}

/// Generate all non-multilinear indices in down(Lambda_T + {2 e_j}).
/// Lambda_T consists of exponents whose divisor count is at most T. For
/// a set of s<=T distinct points the s standard monomials of its point ideal
/// are downward closed, so they belong to Lambda_T and interpolate the set.
/// At a non-Boolean target choose j where x_j^2-x_j is nonzero. The product
/// of this factor with a cardinal interpolant isolates that target. This
/// product vanishes on the cube and is in the span of X^a-X^supp(a) indexed
/// below: Boolean reduction is a linear projection onto multilinear forms.
fn projected_basis(arity: usize, budget: usize) -> BTreeSet<Vec<usize>> {
    fn visit(
        exponent: &mut [usize],
        axis: usize,
        remaining: usize,
        out: &mut BTreeSet<Vec<usize>>,
    ) {
        if axis == exponent.len() {
            for j in 0..exponent.len() {
                for shift in 0..=2 {
                    exponent[j] += shift;
                    if exponent.iter().any(|v| *v > 1) {
                        out.insert(exponent.to_vec());
                    }
                    exponent[j] -= shift;
                }
            }
            return;
        }
        for factor in 1..=remaining {
            exponent[axis] = factor - 1;
            visit(exponent, axis + 1, remaining / factor, out);
        }
    }
    let mut out = BTreeSet::new();
    visit(&mut vec![0; arity], 0, budget, &mut out);
    out
}

fn lifted_basis(c: usize, l: usize, source: Source) -> impl Iterator<Item = Vec<usize>> {
    let (axes, budget) = parameters(c, l, source);
    projected_basis(axes.len(), budget)
        .into_iter()
        .map(move |small| {
            let mut exponent = vec![0; l];
            for (&axis, power) in axes.iter().zip(small) {
                exponent[axis] = power;
            }
            exponent
        })
}

pub(crate) fn support(c: usize, l: usize) -> BTreeSet<Vec<usize>> {
    lifted_basis(c, l, Source::Witness)
        .chain(lifted_basis(c, l, Source::Tree))
        .collect()
}

pub(crate) fn sample(
    profile: &ValidatedProfile,
    source: Source,
    rng: &mut impl RngCore,
) -> Result<BTreeMap<Vec<usize>, Fr>> {
    let mut extras = BTreeMap::new();
    for exponent in lifted_basis(profile.c(), profile.l(), source) {
        let reduced = exponent.iter().map(|e| usize::from(*e != 0)).collect();
        let coin = sample_fr(rng)?;
        *extras.entry(exponent).or_default() += coin;
        *extras.entry(reduced).or_default() -= coin;
    }
    Ok(extras)
}

/// Independent field samples per source [W,A,B] for the paired core7 arms.
pub fn source_mask_counts(p: &ValidatedProfile) -> Result<[usize; 3]> {
    if p.nu() == 0 || p.c() == 0 || !matches!(p.flags(), 0 | PROFILE_FLAG) {
        return Err("mask control requires nondegenerate core7 flags 0 or 8".into());
    }
    if p.flags() == 0 {
        return Ok([p.k() + 2, 5, 4]);
    }
    let witness = projected_basis(p.c() + 1, p.k() + 2).len();
    let tree = projected_basis(2, 5).len();
    Ok([witness, tree, tree])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        index::{self, Gate, ValidatedIndex},
        pcs::PublicSrs,
        protocol,
    };
    use ark_ff::{Field, One, Zero};
    use rand::{rngs::StdRng, SeedableRng};

    fn evaluations(points: &[Vec<Fr>], exponents: BTreeSet<Vec<usize>>) -> Vec<Vec<Fr>> {
        points
            .iter()
            .map(|p| {
                exponents
                    .iter()
                    .map(|e| {
                        let monomial = p
                            .iter()
                            .zip(e)
                            .map(|(x, a)| x.pow([*a as u64]))
                            .product::<Fr>();
                        let reduced = p
                            .iter()
                            .zip(e)
                            .filter(|(_, a)| **a > 0)
                            .map(|(x, _)| *x)
                            .product::<Fr>();
                        monomial - reduced
                    })
                    .collect()
            })
            .collect()
    }

    fn rank(mut rows: Vec<Vec<Fr>>) -> usize {
        let mut rank = 0;
        for column in 0..rows[0].len() {
            let Some(pivot) = (rank..rows.len()).find(|i| !rows[*i][column].is_zero()) else {
                continue;
            };
            rows.swap(rank, pivot);
            let inv = rows[rank][column].inverse().unwrap();
            let pivot = rows[rank].clone();
            for row in &mut rows[rank + 1..] {
                let factor = row[column] * inv;
                for j in column..row.len() {
                    row[j] -= factor * pivot[j];
                }
            }
            rank += 1;
            if rank == rows.len() {
                break;
            }
        }
        rank
    }

    #[test]
    fn projected_basis_interpolates_a_line_and_mixed_axis_queries() {
        for points in [
            (2..12u64)
                .map(|x| vec![Fr::zero(), Fr::one(), Fr::from(x), Fr::zero()])
                .collect::<Vec<_>>(),
            (0..10usize)
                .map(|i| {
                    let mut point = vec![Fr::one(); 4];
                    point[i % 4] = Fr::from((2 + i / 4) as u64);
                    point
                })
                .collect(),
        ] {
            assert_eq!(rank(evaluations(&points, projected_basis(4, 10))), 10);
        }
        let bits = (0..16)
            .map(|i| crate::native::bits(i, 4))
            .collect::<Vec<_>>();
        assert!(evaluations(&bits, projected_basis(4, 10))
            .iter()
            .flatten()
            .all(Zero::is_zero));
    }

    #[test]
    fn projections_separate_protocol_queries_even_on_a_constant_challenge_path() {
        let p = ValidatedProfile::from_flags(2, 3, 2, 5, None, PROFILE_FLAG).unwrap();
        assert_eq!(source_mask_counts(&p).unwrap(), [348, 21, 21]);
        assert_eq!(p.v_extras().len(), 364);
        assert_eq!(p.e(), p.d());
        let (v, u) = p.explicit_supports().unwrap();
        for exponent in v.union(&u) {
            for (axis, &degree) in exponent.iter().enumerate() {
                for power in 0..degree {
                    let mut quotient = vec![0; p.l()];
                    quotient[axis] = power;
                    quotient[axis + 1..].copy_from_slice(&exponent[axis + 1..]);
                    assert!(u.contains(&quotient));
                }
            }
        }
        let relations = protocol::relations(&p, Gate::FixedThirteen, Fr::one(), Fr::one());
        let queries = protocol::queries(&vec![Fr::from(2); p.l()], &relations);
        for (role, name, budget) in [
            (Source::Witness, "W", 10usize),
            (Source::Tree, "A", 5),
            (Source::Tree, "B", 5),
        ] {
            let (axes, _) = parameters(p.c(), p.l(), role);
            let projected = queries
                .iter()
                .filter(|q| q.handle == name || (name != "W" && q.handle == "AminusB"))
                .map(|q| axes.iter().map(|i| q.point[*i]).collect())
                .collect::<Vec<Vec<Fr>>>();
            assert_eq!(projected.len(), budget);
            assert_eq!(
                rank(evaluations(&projected, projected_basis(axes.len(), budget))),
                budget
            );
        }
        assert!(ValidatedProfile::from_flags(0, 3, 0, 5, None, PROFILE_FLAG).is_err());
        assert!(ValidatedProfile::from_flags(1, 5, 0, 5, None, PROFILE_FLAG).is_err());
    }

    #[test]
    fn projected_mask_source_and_quotient_support_round_trip() {
        let p = ValidatedProfile::from_flags(1, 1, 1, 2, None, PROFILE_FLAG).unwrap();
        let mut rng = StdRng::seed_from_u64(632155);
        let srs = PublicSrs::setup(p.clone(), &mut rng).unwrap();
        let mut wire = vec![];
        srs.write_to(&mut wire).unwrap();
        let loaded = PublicSrs::read_from(&mut &wire[..], p.v_count() + p.u_count()).unwrap();
        let (spec, witness) = index::reference_fixture(&p);
        let index = ValidatedIndex::certify(&loaded, spec).unwrap();
        let public = &witness[..2];
        let (proof, _) = protocol::prove(&loaded, &index, public, &witness, &mut rng).unwrap();
        assert!(protocol::verify(loaded.vk(), &p, &index, public, &proof, true).is_ok());
        assert!(protocol::verify(loaded.vk(), &p, &index, public, &proof, false).is_ok());
    }

    #[test]
    fn fixed_thirteen_projected_mask_uses_the_core7_opening_schedule() {
        let p = ValidatedProfile::from_flags(1, 3, 1, 5, None, PROFILE_FLAG).unwrap();
        let mut rng = StdRng::seed_from_u64(634654);
        let srs = PublicSrs::setup(p.clone(), &mut rng).unwrap();
        let (spec, witness) = index::fixed_thirteen_fixture(&p, &mut rng).unwrap();
        let index = ValidatedIndex::certify(&srs, spec).unwrap();
        let public = &witness[..2];
        let (proof, metrics) = protocol::prove(&srs, &index, public, &witness, &mut rng).unwrap();
        assert_eq!(metrics.source_values, 33);
        assert_eq!(metrics.opening_count, 15);
        assert_eq!(
            proof.len(),
            37 + 336 + 32 * (p.round_scalar_count() + 33) + 48 * 15 * (p.l() + 1)
        );
        assert!(protocol::verify(srs.vk(), &p, &index, public, &proof, true).is_ok());
    }

    #[test]
    fn main_profile_ledgers_match_without_constructing_a_large_srs() {
        for (m, r0, r8, u0, u8, bytes0, bytes8) in [
            (10, 79, 208, 79, 416, 12_597, 16_725),
            (14, 107, 236, 103, 440, 16_373, 20_501),
            (16, 121, 250, 115, 452, 18_261, 22_389),
        ] {
            for (flag, rounds, v_extra, u_extra, bytes) in
                [(0, r0, 14, u0, bytes0), (PROFILE_FLAG, r8, 364, u8, bytes8)]
            {
                let p = ValidatedProfile::from_flags(m - 3, 3, 1, 5, None, flag).unwrap();
                assert_eq!(p.e(), p.d());
                assert_eq!(p.round_scalar_count(), rounds);
                assert_eq!(p.v_count(), (1 << p.l()) + v_extra);
                assert_eq!(p.u_count(), (1 << (p.l() - 1)) + u_extra);
                assert_eq!(bytes, 373 + 32 * (rounds + 33) + 48 * 15 * (p.l() + 1));
            }
        }
    }
}
