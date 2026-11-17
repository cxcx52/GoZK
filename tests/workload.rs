use ark_bls12_381::Fr;
use ark_ff::Zero;
use hyperplonk_repair::{
    index::Gate,
    lookup::{LookupFunction, LookupWitness},
    workload::{LookupWorkload, WorkloadConfig},
};
use rand::{rngs::StdRng, SeedableRng};
use std::collections::BTreeSet;

fn config(gate: &str, c: usize) -> WorkloadConfig {
    WorkloadConfig {
        nu: 3,
        c,
        public_log: 3,
        degree: 5,
        anchor: None,
        flags: 1,
        gate: gate.into(),
        dense_terms: 4,
        lookup: None,
        input_seed: 71,
    }
}
fn assert_gate(
    instance: &hyperplonk_repair::workload::Instance,
    p: &hyperplonk_repair::profile::ValidatedProfile,
) {
    if let Some(gate) = instance.spec.gate.descriptor(p).unwrap() {
        for row in 0..p.n() {
            assert!(gate
                .row_value(&instance.spec.selectors, &instance.witness, p.n(), row)
                .unwrap()
                .is_zero());
        }
    }
    for (i, j) in instance.spec.wiring.iter().enumerate() {
        assert_eq!(instance.witness[i], instance.witness[*j]);
    }
}

#[test]
fn deterministic_workloads_preserve_fixed_circuit_across_application_seeds() {
    for (gate, c) in [
        ("fixed13", 3),
        ("power-copy", 2),
        ("dense", 2),
        ("single", 0),
    ] {
        let cfg = config(gate, c);
        let p = cfg.profile().unwrap();
        let a = cfg.instance(41).unwrap();
        let again = cfg.instance(41).unwrap();
        let b = cfg.instance(42).unwrap();
        assert_eq!(a.witness, again.witness);
        assert_eq!(a.public, again.public);
        assert_eq!(a.instance_id, again.instance_id);
        assert_eq!(a.witness_id, again.witness_id);
        assert_eq!(a.spec.selectors, b.spec.selectors);
        assert_eq!(a.spec.wiring, b.spec.wiring);
        assert_eq!(a.definition_id, b.definition_id);
        assert_ne!(a.instance_id, b.instance_id);
        assert!(a.samples_application_inputs);
        assert_gate(&a, &p);
        assert_gate(&b, &p);
        if c > 0 {
            assert_ne!(a.witness, b.witness);
        }
        if a.spec.gate == Gate::FixedThirteen {
            assert_eq!(a.public, b.public);
        }
        let roundtrip: WorkloadConfig =
            serde_json::from_str(&serde_json::to_string(&cfg).unwrap()).unwrap();
        assert_eq!(cfg, roundtrip);
    }
}

#[test]
fn fixed_lookup_tables_and_requested_value_distributions() {
    for c in [1, 2, 3] {
        for distribution in ["uniform", "skewed"] {
            for include_zero in [false, true] {
                let mut cfg = config("power-copy", c);
                cfg.flags = 4;
                cfg.lookup = Some(LookupWorkload {
                    distinct: 3,
                    distribution: distribution.into(),
                    include_zero,
                });
                let p = cfg.profile().unwrap();
                let a = cfg.instance(10).unwrap();
                let b = cfg.instance(11).unwrap();
                assert_eq!(a.definition_id, b.definition_id);
                assert_eq!(
                    a.spec.lookup.as_ref().unwrap().physical_table,
                    b.spec.lookup.as_ref().unwrap().physical_table
                );
                let table = &a.spec.lookup.as_ref().unwrap().physical_table;
                assert_eq!(table.len(), p.n() - 1);
                assert_eq!(
                    table
                        .iter()
                        .map(hyperplonk_repair::codec::scalar_bytes)
                        .collect::<BTreeSet<_>>()
                        .len(),
                    3
                );
                assert_eq!(table.contains(&Fr::zero()), include_zero);
                for instance in [&a, &b] {
                    assert_gate(instance, &p);
                    let lk = instance.spec.lookup.as_ref().unwrap();
                    let expected = if c == 1 {
                        LookupFunction::FirstColumn
                    } else {
                        LookupFunction::SumColumns
                    };
                    assert_eq!(lk.function, expected);
                    LookupWitness::new(
                        &p,
                        &lk.physical_table,
                        &instance.witness,
                        lk.function,
                        &mut StdRng::seed_from_u64(4),
                    )
                    .unwrap();
                }
            }
        }
    }
}

#[test]
fn boolean_lookup_and_minimum_table_boundary() {
    for (nu, distinct, include_zero) in [(1, 1, true), (1, 1, false), (2, 2, true)] {
        let mut cfg = config("single", 0);
        cfg.nu = nu;
        cfg.public_log = nu;
        cfg.flags = 6;
        cfg.lookup = Some(LookupWorkload {
            distinct,
            distribution: "uniform".into(),
            include_zero,
        });
        let p = cfg.profile().unwrap();
        let instance = cfg.instance(23).unwrap();
        assert_gate(&instance, &p);
        let lk = instance.spec.lookup.as_ref().unwrap();
        LookupWitness::new(
            &p,
            &lk.physical_table,
            &instance.witness,
            lk.function,
            &mut StdRng::seed_from_u64(5),
        )
        .unwrap();
    }
}

#[test]
fn workload_validation_and_reference_fixture_accounting() {
    let mut cfg = config("power-copy", 2);
    cfg.lookup = Some(LookupWorkload {
        distinct: 2,
        distribution: "uniform".into(),
        include_zero: true,
    });
    assert!(cfg.profile().is_err());
    cfg.flags = 4;
    assert!(cfg.profile().is_ok());
    cfg.lookup.as_mut().unwrap().distinct = 8;
    assert!(cfg.profile().is_err());
    cfg.lookup.as_mut().unwrap().distinct = 2;
    cfg.lookup.as_mut().unwrap().distribution = "bad".into();
    assert!(cfg.profile().is_err());
    cfg = config("fixed13", 3);
    cfg.flags = 4;
    cfg.lookup = Some(LookupWorkload {
        distinct: 2,
        distribution: "uniform".into(),
        include_zero: true,
    });
    assert!(cfg.profile().is_err());
    cfg = config("reference", 1);
    let a = cfg.instance(1).unwrap();
    let b = cfg.instance(2).unwrap();
    assert_eq!(a.witness_id, b.witness_id);
    assert!(!a.samples_application_inputs);
    assert_ne!(a.instance_id, b.instance_id);
    cfg = config("single", 0);
    cfg.flags = 4;
    cfg.lookup = Some(LookupWorkload {
        distinct: 2,
        distribution: "uniform".into(),
        include_zero: false,
    });
    assert!(cfg.profile().is_err());
    let bad = serde_json::json!({"nu":3,"c":2,"public_log":3,"degree":5,"flags":1,"gate":"power-copy","typo":true});
    assert!(serde_json::from_value::<WorkloadConfig>(bad).is_err());
}
