//! Genuine group integration for the extended profiles. Test fixtures use fresh
//! private coins. Prover-side input failures are separate from verifier rejects.
use ark_bls12_381::Fr;
use hyperplonk_repair::{
    index::{self, Gate, ValidatedIndex},
    lookup::LookupFunction,
    pcs::PublicSrs,
    profile::ValidatedProfile,
    protocol,
};
use rand::{
    rngs::{OsRng, StdRng},
    SeedableRng,
};

fn profile(nu: usize, c: usize, publog: usize, degree: usize, flags: u64) -> ValidatedProfile {
    ValidatedProfile::new_config(nu, c, publog, degree, None, flags).unwrap()
}

#[test]
fn core6_compiled_public_prefix_accepts_different_storage() {
    for (nu, c, publog, gate) in [
        (2, 1, 0, Gate::PowerCopy),
        (2, 1, 2, Gate::PowerCopy),
        (2, 1, 3, Gate::PowerCopy),
        (0, 2, 2, Gate::PowerCopy),
        (1, 0, 1, Gate::SingleColumnBoolean),
        (0, 0, 0, Gate::SingleColumnBoolean),
    ] {
        let p = profile(nu, c, publog, 5, 3);
        let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
        let (spec, semantic) = index::gate_fixture(&p, gate, 71).unwrap();
        let ix = ValidatedIndex::certify(&srs, spec).unwrap();
        let public = &semantic[..1 << publog];
        let mut stored = semantic.clone();
        for x in &mut stored[..public.len()] {
            *x += Fr::from(123);
        }
        let (proof, metrics) = protocol::prove(&srs, &ix, public, &stored, &mut OsRng)
            .unwrap_or_else(|e| panic!("core6 nu={nu} c={c} pub={publog}: {e}"));
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, false).is_ok());
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_ok());
        assert_eq!(metrics.proof_bytes, proof.len());
        let mut wrong_public = public.to_vec();
        wrong_public[0] += Fr::from(1);
        assert!(protocol::verify(srs.vk(), &p, &ix, &wrong_public, &proof, true).is_err());
    }
}

#[test]
fn native_core_boundaries_and_experiment_gates() {
    for (nu, c, degree, gate) in [
        (0, 0, 5, Gate::SingleColumnBoolean),
        (1, 0, 5, Gate::SingleColumnBoolean),
        (0, 1, 5, Gate::PowerCopy),
        (1, 1, 33, Gate::PowerCopy),
        (1, 3, 5, Gate::Dense { terms: 16 }),
    ] {
        let p = profile(nu, c, nu, degree, 1);
        let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
        let (spec, w) = index::gate_fixture(&p, gate, 72).unwrap();
        let ix = ValidatedIndex::certify(&srs, spec).unwrap();
        let public = &w[..1 << nu];
        let (proof, _) = protocol::prove(&srs, &ix, public, &w, &mut OsRng)
            .unwrap_or_else(|e| panic!("core7 nu={nu} c={c} degree={degree}: {e}"));
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_ok());
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, false).is_ok());
    }
}

#[test]
fn lookup12_lookup11_real_group_paths_and_table_binding() {
    for (nu, c, publog, virtual_public, function) in [
        (1, 0, 0, false, LookupFunction::FirstColumn),
        (2, 0, 2, true, LookupFunction::SumColumns),
        (2, 1, 0, false, LookupFunction::SumColumns),
        (2, 1, 3, true, LookupFunction::SumColumns),
        (2, 3, 2, false, LookupFunction::SumColumns),
    ] {
        let p = profile(nu, c, publog, 5, 4 + 2 * u64::from(virtual_public));
        let gate = if c == 0 {
            Gate::SingleColumnBoolean
        } else {
            Gate::PowerCopy
        };
        let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
        let (spec, w) = index::gate_fixture(&p, gate, 73).unwrap();
        let spec = index::attach_lookup(spec, &p, &w, function).unwrap();
        let ix = ValidatedIndex::certify(&srs, spec).unwrap();
        let public = &w[..1 << publog];
        let mut stored = w.clone();
        if virtual_public {
            for x in &mut stored[..public.len()] {
                *x += Fr::from(33);
            }
        }
        let (proof, metrics) = protocol::prove(&srs, &ix, public, &stored, &mut OsRng)
            .unwrap_or_else(|e| {
                panic!("lookup nu={nu} c={c} pub={publog} virtual={virtual_public}: {e}")
            });
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_ok());
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, false).is_ok());
        assert!(metrics.offsets.contains_key("lookup_helper"));
        assert!(metrics.offsets.contains_key("lookup_trees"));
        for stage in ["lookup_helper", "lookup_trees", "values", "openings"] {
            let mut bad = proof.clone();
            bad[metrics.offsets[stage] + 10] ^= 1;
            assert!(protocol::verify(srs.vk(), &p, &ix, public, &bad, true).is_err());
        }
        let (spec, _) = index::gate_fixture(&p, gate, 73).unwrap();
        let mut spec = index::attach_lookup(spec, &p, &w, function).unwrap();
        spec.lookup.as_mut().unwrap().physical_table[0] += Fr::from(1);
        let wrong = ValidatedIndex::certify(&srs, spec).unwrap();
        assert!(protocol::verify(srs.vk(), &p, &wrong, public, &proof, true).is_err());
    }
}

#[test]
fn lookup_cached_and_uncached_openings_share_wire() {
    let p = profile(2, 1, 2, 5, 6);
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, w) = index::gate_fixture(&p, Gate::PowerCopy, 76).unwrap();
    let spec = index::attach_lookup(spec, &p, &w, LookupFunction::SumColumns).unwrap();
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let public = &w[..4];
    // Explicit test-only deterministic private tapes, never benchmark coins.
    let (a, _) = protocol::prove_with_options(
        &srs,
        &ix,
        public,
        &w,
        &mut StdRng::seed_from_u64(911),
        protocol::ProverOptions {
            cache_openings: true,
        },
    )
    .unwrap();
    let (b, _) = protocol::prove_with_options(
        &srs,
        &ix,
        public,
        &w,
        &mut StdRng::seed_from_u64(911),
        protocol::ProverOptions {
            cache_openings: false,
        },
    )
    .unwrap();
    assert_eq!(a, b);
    assert!(protocol::verify(srs.vk(), &p, &ix, public, &a, true).is_ok());
}

#[test]
fn lookup_missing_values_and_mismatched_index_shapes_reject() {
    let p = profile(2, 1, 2, 5, 4);
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, w) = index::gate_fixture(&p, Gate::PowerCopy, 78).unwrap();
    assert!(ValidatedIndex::certify(&srs, spec).is_err());
    let (spec, _) = index::gate_fixture(&p, Gate::PowerCopy, 78).unwrap();
    let mut spec = index::attach_lookup(spec, &p, &w, LookupFunction::SumColumns).unwrap();
    spec.lookup.as_mut().unwrap().physical_table.pop();
    assert!(ValidatedIndex::certify(&srs, spec).is_err());
    let (spec, _) = index::gate_fixture(&p, Gate::PowerCopy, 78).unwrap();
    let spec = index::attach_lookup(spec, &p, &w, LookupFunction::SumColumns).unwrap();
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let mut bad = w.clone();
    bad[4] += Fr::from(123);
    bad[5] += Fr::from(123);
    assert!(protocol::prove(&srs, &ix, &w[..4], &bad, &mut OsRng).is_err());
}
