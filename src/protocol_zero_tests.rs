//! Legal challenge injection for completeness boundaries only. This module and
//! its transcript override do not exist in production builds. It does not test
//! the probability of sampling these challenges in a random oracle.
use crate::{
    index::{self, ValidatedIndex},
    lookup::{LookupFunction, LookupWitness},
    pcs::PublicSrs,
    profile::ValidatedProfile,
    protocol,
    transcript::test_override,
};
use ark_bls12_381::Fr;
use ark_ff::{One, Zero};
use rand::rngs::OsRng;

#[test]
fn core_zero_leaves_and_zero_products_verify_in_real_groups() {
    let p = ValidatedProfile::new(2, 1, 2, 5, None, true).unwrap();
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, w) = index::reference_fixture(&p);
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let public = &w[..4];
    let beta = Fr::one();
    let gamma = -w[0];
    let a = w
        .iter()
        .enumerate()
        .map(|(i, x)| *x + beta * Fr::from(i as u64) + gamma)
        .collect::<Vec<_>>();
    let b = w
        .iter()
        .enumerate()
        .map(|(i, x)| *x + beta * Fr::from(ix.wiring()[i] as u64) + gamma)
        .collect::<Vec<_>>();
    assert!(a[0].is_zero());
    assert!(b[1].is_zero());
    assert!(a.iter().copied().product::<Fr>().is_zero());
    assert!(b.iter().copied().product::<Fr>().is_zero());
    let guard = test_override("copy_fingerprint", vec![beta, gamma]);
    let (proof, metrics) = protocol::prove(&srs, &ix, public, &w, &mut OsRng).unwrap();
    assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, false).is_ok());
    assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_ok());
    assert_eq!(metrics.opening_count, 9);
    drop(guard);
    assert!(
        protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_err(),
        "test override leaked beyond guard"
    );
}

#[test]
fn lookup11_and_lookup12_zero_product_paths_use_legal_nonzero_gamma() {
    for virtual_public in [false, true] {
        let p = ValidatedProfile::new_config(2, 1, 2, 5, None, 4 + 2 * u64::from(virtual_public))
            .unwrap();
        let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
        let (spec, w) = index::reference_fixture(&p);
        let spec = index::attach_lookup(spec, &p, &w, LookupFunction::FirstColumn).unwrap();
        let ix = ValidatedIndex::certify(&srs, spec).unwrap();
        let public = &w[..4];
        let beta_copy = Fr::one();
        let gamma_copy = -w[0];
        let beta_lookup = Fr::zero();
        let gamma_lookup = -w[0];
        assert!(!gamma_lookup.is_zero());
        let lk = ix.lookup().unwrap();
        let auxiliary =
            LookupWitness::new(&p, &lk.physical_table, &w, lk.function, &mut OsRng).unwrap();
        let (c, e) = auxiliary.leaves(beta_lookup, gamma_lookup).unwrap();
        assert!(c[0].is_zero());
        assert!(e.iter().any(|x| x.is_zero()));
        assert!(c.iter().copied().product::<Fr>().is_zero());
        assert!(e.iter().copied().product::<Fr>().is_zero());
        let mut stored = w.clone();
        if virtual_public {
            for x in &mut stored[..public.len()] {
                *x += Fr::from(919);
            }
        }
        let guard = test_override(
            "joint_fingerprints",
            vec![beta_copy, gamma_copy, beta_lookup, gamma_lookup],
        );
        let (proof, metrics) = protocol::prove(&srs, &ix, public, &stored, &mut OsRng).unwrap();
        assert!(metrics.offsets.contains_key("lookup_trees"));
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, false).is_ok());
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_ok());
        drop(guard);
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_err());
    }
}
