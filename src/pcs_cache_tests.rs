//! Unit tests can inspect derived cache coverage without adding a production
//! cache API or accepting cache points in the serialized SRS.
use super::*;
use rand::{rngs::StdRng, SeedableRng};
use std::{collections::BTreeSet, io::Cursor};

fn profiles() -> Vec<ValidatedProfile> {
    [
        (3, 2, 1), // legacy core7, including a middle row coordinate
        (3, 2, 3), // virtual-public core6
        (3, 2, 4), // lookup12
        (3, 2, 6), // lookup11
        (2, 0, 0), // single column
        (2, 0, 2),
        (2, 0, 4), // single-column lookup has a leading global padding axis
        (2, 0, 6),
        (0, 2, 0), // last axis overlaps the column block
        (0, 2, 2),
        (0, 0, 0), // constant helper Boolean block
        (0, 0, 2),
    ]
    .into_iter()
    .map(|(nu, c, flags)| ValidatedProfile::new_config(nu, c, 0, 5, None, flags).unwrap())
    .collect()
}

#[test]
fn derived_cache_matches_trapdoor_setup_across_geometry_boundaries() {
    for (case, profile) in profiles().into_iter().enumerate() {
        let mut rng = StdRng::seed_from_u64(0x53525300 + case as u64);
        let original = PublicSrs::setup(profile.clone(), &mut rng).unwrap();
        let mut bytes = Vec::new();
        original.write_to(&mut bytes).unwrap();
        let loaded = PublicSrs::read_from(&mut Cursor::new(&bytes), 100_000).unwrap();
        // Setup computes these values from tau; loading derives them solely
        // from the checked Lagrange bases. Compare every point and key.
        assert_eq!(original.v_monomials, loaded.v_monomials, "V case {case}");
        assert_eq!(original.u_monomials, loaded.u_monomials, "U case {case}");
        assert_eq!(original.u_axes, loaded.u_axes, "axes case {case}");
        assert_eq!(
            original.primary_point_counts(),
            loaded.primary_point_counts()
        );
        assert_eq!(original.cached_point_counts(), loaded.cached_point_counts());
        assert_eq!(original.vk.srs_digest, loaded.vk.srs_digest);
        for exponent in loaded.v_monomials.keys() {
            assert!(profile.contains_v(exponent));
            assert_eq!(
                loaded.v_monomials[exponent],
                mle_monomial_g2(&loaded, exponent).into_affine()
            );
        }
        for exponent in loaded.u_monomials.keys() {
            assert!(profile.contains_u(exponent));
            assert_eq!(
                loaded.u_monomials[exponent],
                mle_monomial_g1(&loaded, exponent).into_affine()
            );
        }
        let mut reencoded = Vec::new();
        loaded.write_to(&mut reencoded).unwrap();
        assert_eq!(
            bytes, reencoded,
            "derived caches must not alter SRS wire format"
        );
    }
}

#[test]
fn derived_cache_handles_identity_points_at_boolean_trapdoor_coordinates() {
    let profile = ValidatedProfile::new_config(3, 2, 0, 5, None, 6).unwrap();
    let tau: Vec<_> = (0..profile.l())
        .map(|i| match i % 3 {
            0 => Fr::zero(),
            1 => Fr::one(),
            _ => Fr::from(7u64),
        })
        .collect();
    let v_suffix = g2_suffix(g2_fixed(&boolean_weights(&tau)));
    let u_suffix = g1_suffix(g1_fixed(&boolean_weights(&tau[1..])));
    for (exponent, point) in derive_cached_monomials(&profile, false, &v_suffix) {
        assert_eq!(
            point,
            (G2Affine::generator() * monomial(&tau, &exponent)).into_affine()
        );
    }
    for (exponent, point) in derive_cached_monomials(&profile, true, &u_suffix) {
        assert_eq!(
            point,
            (G1Affine::generator() * monomial(&tau, &exponent)).into_affine()
        );
    }
}

fn geometric_sparse_source(profile: &ValidatedProfile) -> StructuredPolynomial {
    let mut exponents: BTreeSet<_> = profile.v_extras().into_iter().collect();
    // The low-degree part of each vanishing mask replaces its squares by
    // first powers. Include the whole Boolean cache to cover all subfaces.
    exponents.extend(cached_monomials(profile, false));
    StructuredPolynomial::new(
        profile.l(),
        vec![],
        exponents
            .into_iter()
            .enumerate()
            .map(|(i, exponent)| (exponent, Fr::from((i + 1) as u64)))
            .collect(),
    )
    .unwrap()
}

#[test]
fn geometric_masks_and_all_helper_quotients_have_cached_fragments() {
    for profile in profiles() {
        let source_keys: BTreeSet<_> = cached_monomials(&profile, false).into_iter().collect();
        let helper_keys: BTreeSet<_> = cached_monomials(&profile, true).into_iter().collect();
        let source = geometric_sparse_source(&profile);
        for exponent in source.extras().keys() {
            assert!(profile.contains_v(exponent));
            if exponent.iter().all(|power| *power <= 1) {
                assert!(source_keys.contains(exponent));
            }
        }
        let helper_extras: BTreeSet<_> = profile.u_extras().into_iter().collect();
        let helper = StructuredPolynomial::new(
            profile.l(),
            vec![],
            helper_extras
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, exponent)| (exponent, Fr::from((i + 1) as u64)))
                .collect(),
        )
        .unwrap();
        let point: Vec<_> = (0..profile.l()).map(|i| Fr::from((i + 3) as u64)).collect();
        for polynomial in [source, helper] {
            let (_, quotients, _) = polynomial.canonical_quotients(&point).unwrap();
            for quotient in quotients {
                for exponent in quotient.extras().keys() {
                    assert!(
                        profile.contains_u(exponent),
                        "unsupported quotient {exponent:?}"
                    );
                    assert!(
                        helper_extras.contains(exponent) || helper_keys.contains(exponent),
                        "uncached quotient fragment {exponent:?} for {}",
                        profile.profile_id()
                    );
                }
            }
        }
    }
}

#[test]
fn loaded_boundary_srs_opens_sparse_geometry_in_real_groups() {
    for (nu, c, flags) in [(2, 2, 6), (2, 0, 4), (0, 2, 2), (0, 0, 2)] {
        let profile = ValidatedProfile::new_config(nu, c, 0, 5, None, flags).unwrap();
        let mut rng = StdRng::seed_from_u64(0x53525380 + nu as u64 + c as u64 + flags);
        let srs = PublicSrs::setup(profile.clone(), &mut rng).unwrap();
        let mut bytes = Vec::new();
        srs.write_to(&mut bytes).unwrap();
        let loaded = PublicSrs::read_from(&mut Cursor::new(bytes), 100_000).unwrap();
        let source = geometric_sparse_source(&profile);
        let point: Vec<_> = (0..profile.l()).map(|i| Fr::from((i + 7) as u64)).collect();
        let blind = Fr::from(13u64);
        let commitment = commit(&loaded, &source, SourceKind::Source, blind).unwrap();
        assert_eq!(
            commitment,
            commit(&srs, &source, SourceKind::Source, blind).unwrap()
        );
        let proof = open_polynomial(
            &loaded,
            &source,
            SourceKind::Source,
            &point,
            blind,
            &mut rng,
        )
        .unwrap();
        let opening = Opening {
            commitment,
            value: source.evaluate(&point).unwrap(),
            point,
            proof,
        };
        assert!(verify_opening(srs.vk(), &opening));
    }
}
