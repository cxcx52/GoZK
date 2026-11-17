use ark_bls12_381::Fr;
use ark_ff::{One, Zero};
use hyperplonk_repair::{
    index::{self, IndexSpec},
    profile::ValidatedProfile,
    trace_protocol::{self, TraceIndex, TraceProfile},
};
use rand::{rngs::StdRng, SeedableRng};

#[test]
fn historical_seven_sumchecks_accept_fresh_coins_and_reject_corruption() {
    let mut rng = StdRng::seed_from_u64(53001);
    let p = TraceProfile::new(1, 1, 1, 2).unwrap();
    let geometry = ValidatedProfile::new(1, 1, 1, 2, None, true).unwrap();
    let (spec, witness) = index::reference_fixture(&geometry);
    let public = &witness[..2];
    let srs = p.setup(&mut rng, 100_000).unwrap();
    let index = TraceIndex::certify(&srs, p, spec).unwrap();
    let (proof, pm) = trace_protocol::prove(&srs, &index, public, &witness, &mut rng).unwrap();
    let vm = trace_protocol::verify(srs.vk(), &index, public, &proof).unwrap();
    assert_eq!(pm.hash_packets, vm.hash_packets);
    assert_eq!(pm.proof_bytes, proof.len());
    assert_eq!(pm.private_queries["W"], 4);
    assert!(pm.private_queries["A"] <= 5 && pm.private_queries["B"] <= 5);
    let fresh = trace_protocol::prove(&srs, &index, public, &witness, &mut rng)
        .unwrap()
        .0;
    assert_ne!(proof, fresh);
    assert_eq!(proof.len(), fresh.len());
    assert!(trace_protocol::verify(srs.vk(), &index, public, &fresh).is_ok());
    for label in ["witness", "helpers", "rounds", "values", "openings"] {
        let mut bad = proof.clone();
        bad[pm.offsets[label]] ^= 1;
        assert!(
            trace_protocol::verify(srs.vk(), &index, public, &bad).is_err(),
            "{label}"
        );
    }
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(trace_protocol::verify(srs.vk(), &index, public, &trailing).is_err());
    assert!(trace_protocol::verify(srs.vk(), &index, public, &proof[..proof.len() - 1]).is_err());
    let wrong = [public[0] + Fr::one(), public[1]];
    assert!(trace_protocol::verify(srs.vk(), &index, &wrong, &proof).is_err());
    let mut bad = witness.clone();
    bad[2] += Fr::one();
    assert!(trace_protocol::prove(&srs, &index, public, &bad, &mut rng).is_err());
}

#[test]
fn fixed_thirteen_baseline_has_matching_fixed_circuit_and_trace_budget() {
    let mut rng = StdRng::seed_from_u64(53002);
    let geometry = ValidatedProfile::new(1, 3, 1, 5, None, true).unwrap();
    let (spec, witness) = index::fixed_thirteen_fixture(&geometry, &mut rng).unwrap();
    let p = TraceProfile::new(1, 3, 1, 5).unwrap();
    assert_eq!(p.parameters().t(), 11);
    assert_eq!(p.parameters().d(), 62);
    let srs = p.setup(&mut rng, 100_000).unwrap();
    let index = TraceIndex::certify(&srs, p, spec).unwrap();
    let (proof, pm) =
        trace_protocol::prove(&srs, &index, &witness[..2], &witness, &mut rng).unwrap();
    assert!(trace_protocol::verify(srs.vk(), &index, &witness[..2], &proof).is_ok());
    assert_eq!(pm.private_queries["W"], 10);
    assert_eq!(pm.private_queries["A"], 5);
    assert_eq!(pm.private_queries["B"], 5);
}

#[test]
fn scalar_boundary_omits_copy_tree_and_checks_public_input() {
    let mut rng = StdRng::seed_from_u64(53003);
    let p = TraceProfile::new(0, 0, 0, 2).unwrap();
    let srs = p.setup(&mut rng, 100_000).unwrap();
    let witness = vec![Fr::from(3u64)];
    let spec = IndexSpec {
        gate: index::Gate::ReferencePower,
        selectors: [
            ("q0".into(), vec![Fr::one()]),
            ("qout".into(), vec![Fr::from(9u64)]),
        ]
        .into(),
        wiring: vec![0],
        lookup: None,
    };
    let index = TraceIndex::certify(&srs, p, spec).unwrap();
    let (proof, pm) = trace_protocol::prove(&srs, &index, &witness, &witness, &mut rng).unwrap();
    assert!(trace_protocol::verify(srs.vk(), &index, &witness, &proof).is_ok());
    assert_eq!(pm.private_queries["A"], 0);
    assert_eq!(pm.private_queries["B"], 0);
    assert!(TraceProfile::new(25, 0, 0, 2).is_err());
    assert!(TraceProfile::new(0, 0, 1, 2).is_err());
    let _ = Fr::zero();
}

#[test]
#[ignore = "explicit trusted fixtures for independent archived-V5 py_ecc verification"]
fn export_trace_protocol_fixtures() {
    let directory = std::env::var("HP7_TRACE_PROTOCOL_FIXTURES").expect("fixture output directory");
    std::fs::create_dir_all(&directory).unwrap();
    for (fixed, c, degree) in [(false, 1, 2), (true, 3, 5)] {
        let mut rng = StdRng::seed_from_u64(53100 + u64::from(fixed));
        let geometry = ValidatedProfile::new(1, c, 1, degree, None, true).unwrap();
        let (spec, witness) = if fixed {
            index::fixed_thirteen_fixture(&geometry, &mut rng).unwrap()
        } else {
            index::reference_fixture(&geometry)
        };
        let p = TraceProfile::new(1, c, 1, degree).unwrap();
        let srs = p.setup(&mut rng, 100_000).unwrap();
        let index = TraceIndex::certify(&srs, p, spec).unwrap();
        let (proof, _) =
            trace_protocol::prove(&srs, &index, &witness[..2], &witness, &mut rng).unwrap();
        assert!(trace_protocol::verify(srs.vk(), &index, &witness[..2], &proof).is_ok());
        let fixture =
            trace_protocol::public_fixture(srs.vk(), &index, &witness[..2], &proof).unwrap();
        let name = if fixed { "fixed13" } else { "reference" };
        std::fs::write(
            std::path::Path::new(&directory).join(format!("{name}.json")),
            serde_json::to_vec_pretty(&fixture).unwrap(),
        )
        .unwrap();
    }
}
