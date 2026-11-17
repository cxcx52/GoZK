//! Parameter/statement binding tests. Every negative below reaches the verifier
//! with proof bytes; index and witness-construction failures live elsewhere.
use ark_bls12_381::{Fr, G2Affine};
use ark_ec::AffineRepr;
use hyperplonk_repair::{
    codec::g2_bytes,
    index::{self, Gate, ValidatedIndex},
    lookup::LookupFunction,
    pcs::PublicSrs,
    profile::ValidatedProfile,
    protocol,
};
use rand::rngs::OsRng;

#[test]
fn changing_profile_anchor_degrees_public_slice_or_srs_rejects() {
    let p = ValidatedProfile::new_config(2, 2, 2, 5, Some(1), 1).unwrap();
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, w) = index::gate_fixture(&p, Gate::PowerCopy, 101).unwrap();
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let (proof, _) = protocol::prove(&srs, &ix, &w[..4], &w, &mut OsRng).unwrap();
    assert!(protocol::verify(srs.vk(), &p, &ix, &w[..4], &proof, true).is_ok());
    for (publog, degree, anchor, flags) in [
        (2, 5, 2, 1),
        (2, 9, 1, 1),
        (2, 5, 1, 0),
        (3, 5, 1, 1),
        (2, 5, 1, 3),
    ] {
        let changed =
            ValidatedProfile::new_config(2, 2, publog, degree, Some(anchor), flags).unwrap();
        assert!(
            protocol::verify(srs.vk(), &changed, &ix, &w[..1 << publog], &proof, true).is_err()
        );
        let other = PublicSrs::setup(changed.clone(), &mut OsRng).unwrap();
        let (spec, new_w) = index::gate_fixture(&changed, Gate::PowerCopy, 101).unwrap();
        let new_ix = ValidatedIndex::certify(&other, spec).unwrap();
        assert!(protocol::verify(
            other.vk(),
            &changed,
            &new_ix,
            &new_w[..1 << publog],
            &proof,
            true
        )
        .is_err());
    }
    let other = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, _) = index::gate_fixture(&p, Gate::PowerCopy, 101).unwrap();
    let new_ix = ValidatedIndex::certify(&other, spec).unwrap();
    assert!(protocol::verify(other.vk(), &p, &new_ix, &w[..4], &proof, true).is_err());
}

#[test]
fn certified_selector_and_permutation_changes_reject_old_bytes() {
    let p = ValidatedProfile::new(2, 1, 2, 5, None, true).unwrap();
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, w) = index::gate_fixture(&p, Gate::PowerCopy, 102).unwrap();
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let (proof, _) = protocol::prove(&srs, &ix, &w[..4], &w, &mut OsRng).unwrap();
    let (mut spec, _) = index::gate_fixture(&p, Gate::PowerCopy, 102).unwrap();
    spec.selectors.get_mut("q0").unwrap()[0] += Fr::from(1);
    let changed = ValidatedIndex::certify(&srs, spec).unwrap();
    assert!(protocol::verify(srs.vk(), &p, &changed, &w[..4], &proof, true).is_err());
    let (mut spec, _) = index::gate_fixture(&p, Gate::PowerCopy, 102).unwrap();
    spec.wiring.swap(0, 2);
    let changed = ValidatedIndex::certify(&srs, spec).unwrap();
    assert!(protocol::verify(srs.vk(), &p, &changed, &w[..4], &proof, true).is_err());
}

#[test]
fn lookup_source_roles_function_and_all_opening_bytes_are_bound() {
    let p = ValidatedProfile::new_lookup(2, 1, 2, 5, None, false).unwrap();
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, w) = index::gate_fixture(&p, Gate::PowerCopy, 103).unwrap();
    let spec = index::attach_lookup(spec, &p, &w, LookupFunction::SumColumns).unwrap();
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let (proof, m) = protocol::prove(&srs, &ix, &w[..4], &w, &mut OsRng).unwrap();
    // Swap valid source-group encodings, so canonical parsing alone is insufficient.
    let mut bad = proof.clone();
    let a = m.offsets["witness"];
    let b = m.offsets["lookup_helper"];
    bad[a..a + 96].copy_from_slice(&proof[b..b + 96]);
    bad[b..b + 96].copy_from_slice(&proof[a..a + 96]);
    assert!(protocol::verify(srs.vk(), &p, &ix, &w[..4], &bad, true).is_err());
    let mut bad = proof.clone();
    let a = m.offsets["trees"];
    let b = m.offsets["lookup_trees"];
    bad[a..a + 192].copy_from_slice(&proof[b..b + 192]);
    bad[b..b + 192].copy_from_slice(&proof[a..a + 192]);
    assert!(protocol::verify(srs.vk(), &p, &ix, &w[..4], &bad, true).is_err());
    // Reorder canonical opening points after all endpoint and round bytes freeze.
    let mut bad = proof.clone();
    let a = m.offsets["openings"];
    bad[a..a + 48].copy_from_slice(&proof[a + 48..a + 96]);
    bad[a + 48..a + 96].copy_from_slice(&proof[a..a + 48]);
    assert!(protocol::verify(srs.vk(), &p, &ix, &w[..4], &bad, true).is_err());
    let (spec, _) = index::gate_fixture(&p, Gate::PowerCopy, 103).unwrap();
    let mut spec = index::attach_lookup(spec, &p, &w, LookupFunction::SumColumns).unwrap();
    spec.lookup.as_mut().unwrap().function = LookupFunction::FirstColumn;
    let changed = ValidatedIndex::certify(&srs, spec).unwrap();
    assert!(protocol::verify(srs.vk(), &p, &changed, &w[..4], &proof, true).is_err());
}

#[test]
fn n1_dummy_commitments_are_canonical_identity_only() {
    let p = ValidatedProfile::new_config(0, 0, 0, 5, None, 1).unwrap();
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, w) = index::gate_fixture(&p, Gate::SingleColumnBoolean, 104).unwrap();
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let (proof, m) = protocol::prove(&srs, &ix, &w, &w, &mut OsRng).unwrap();
    assert!(protocol::verify(srs.vk(), &p, &ix, &w, &proof, true).is_ok());
    let mut bad = proof.clone();
    let off = m.offsets["trees"];
    bad[off..off + 96].copy_from_slice(&g2_bytes(&G2Affine::generator()));
    let error = protocol::verify(srs.vk(), &p, &ix, &w, &bad, true).unwrap_err();
    assert!(error.contains("dummy tree"));
}
