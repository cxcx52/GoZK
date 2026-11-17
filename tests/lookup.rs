use ark_bls12_381::Fr;
use ark_ff::{One, Zero};
use hyperplonk_repair::{
    lookup::{masked_tree, relations, witness_mask, LookupFunction, LookupWitness, PrimitiveCycle},
    native::{bits, interpolate, univariate, NativeSumcheck},
    profile::ValidatedProfile,
    tables::{DenseMle, StructuredPolynomial},
};
use rand::{rngs::StdRng, SeedableRng};
use std::collections::{BTreeMap, BTreeSet};

#[test]
fn primitive_feedback_certificates_and_full_small_periods() {
    let mut certificates = vec![];
    for d in 1..=22 {
        let cycle = PrimitiveCycle::new(d).unwrap();
        assert_eq!(cycle.dimension(), d);
        assert_eq!(
            PrimitiveCycle::from_polynomial(d, cycle.polynomial()).unwrap(),
            cycle
        );
        certificates.push(serde_json::json!({"dimension":d,"polynomial":cycle.polynomial(),"order_factors":cycle.order_factors()}));
        if d <= 12 {
            let mut seen = BTreeSet::new();
            let mut p = 1usize << (d - 1);
            while seen.insert(p) {
                assert_ne!(p, 0);
                p = cycle.step(p);
            }
            assert_eq!(p, 1usize << (d - 1));
            assert_eq!(seen.len(), (1 << d) - 1);
        }
    }
    // x^4+x^3+x^2+x+1 is irreducible but has order 5, not 15.
    assert!(PrimitiveCycle::from_polynomial(4, 31).is_err());
    assert!(PrimitiveCycle::from_polynomial(4, 17).is_err());
    assert!(PrimitiveCycle::new(0).is_err());
    assert!(PrimitiveCycle::new(23).is_err());
    if let Some(path) = std::env::var_os("HP7_LOOKUP_CYCLE_CERTIFICATES") {
        std::fs::write(path, serde_json::to_vec_pretty(&certificates).unwrap()).unwrap();
    }
}

fn fixture(
    nu: usize,
    c: usize,
    virtual_public: bool,
) -> (
    ValidatedProfile,
    LookupWitness,
    BTreeMap<String, StructuredPolynomial>,
) {
    let p = ValidatedProfile::new_lookup(nu, c, nu, 5, None, virtual_public).unwrap();
    let mut rng = StdRng::seed_from_u64(2081 + nu as u64 + 10 * c as u64);
    let witness = (0..p.n_total())
        .map(|i| Fr::from((i % p.n() / 2) as u64))
        .collect::<Vec<_>>();
    let table = (0..p.n() - 1)
        .map(|i| Fr::from(((i % (p.n() / 2)) * p.k()) as u64))
        .collect::<Vec<_>>();
    let lookup =
        LookupWitness::new(&p, &table, &witness, LookupFunction::SumColumns, &mut rng).unwrap();
    let mut padded = witness.clone();
    padded.resize(2 * p.n_total(), Fr::zero());
    let w =
        StructuredPolynomial::from_table(p.l(), p.core_offset(), DenseMle::new(padded).unwrap())
            .unwrap()
            .add(&witness_mask(&p, &mut rng).unwrap())
            .unwrap();
    let (l, r) = lookup.leaves(Fr::from(7), Fr::from(11)).unwrap();
    let mut sorted_l = l.clone();
    let mut sorted_r = r.clone();
    sorted_l.sort_by_key(|v| hyperplonk_repair::codec::scalar_bytes(v));
    sorted_r.sort_by_key(|v| hyperplonk_repair::codec::scalar_bytes(v));
    assert_eq!(sorted_l, sorted_r);
    let a = masked_tree(&p, &l, true, &mut rng).unwrap();
    let b = masked_tree(&p, &r, false, &mut rng).unwrap();
    let diff = a.add(&b.scaled(-Fr::one())).unwrap();
    let mut sources = BTreeMap::from([
        ("W".into(), w),
        ("H".into(), lookup.h_source.clone()),
        ("C".into(), a),
        ("E".into(), b),
        ("CminusE".into(), diff),
    ]);
    sources.insert(
        "table".into(),
        StructuredPolynomial::from_table(
            p.l(),
            p.l() - p.nu(),
            DenseMle::new(lookup.table_embedded.clone()).unwrap(),
        )
        .unwrap(),
    );
    sources.insert(
        "__public".into(),
        StructuredPolynomial::from_table(
            p.l(),
            p.l() - p.public_log(),
            DenseMle::new(witness[..1 << p.public_log()].to_vec()).unwrap(),
        )
        .unwrap(),
    );
    (p, lookup, sources)
}

#[test]
fn lookup_five_native_relations_masks_and_sumcheck_caps() {
    for (nu, c) in [(1, 0), (1, 1), (2, 0), (2, 1), (3, 2)] {
        for virtual_public in [false, true] {
            let (p, lookup, polys) = fixture(nu, c, virtual_public);
            let mut rels = relations(
                &p,
                LookupFunction::SumColumns,
                &lookup.table_cycle,
                &lookup.h_cycle,
                Fr::from(7),
                Fr::from(11),
            )
            .unwrap();
            assert_eq!(rels.len(), 5);
            for (i, rel) in rels.iter_mut().enumerate() {
                if i < 4 {
                    rel.tau = Some(vec![Fr::from((i + 3) as u64); rel.dimension]);
                }
                rel.weight = Fr::from((i + 1) as u64);
                for b in 0..1 << rel.dimension {
                    assert!(rel
                        .evaluate(&bits(b, rel.dimension), &mut |h, z| polys[h].evaluate(z))
                        .unwrap()
                        .is_zero());
                }
            }
            for source in polys.values() {
                for e in source.extras().keys() {
                    assert!(p.contains_v(e), "unsupported actual lookup direction {e:?}");
                }
            }
            let helper = StructuredPolynomial::zero(p.l()).unwrap();
            let mut engine = NativeSumcheck::new(p.l(), rels, &polys, helper, Fr::from(5)).unwrap();
            let mut claim = Fr::zero();
            for (a, cap) in p.e().iter().enumerate() {
                let values = (0..=*cap)
                    .map(|x| engine.round_value(Fr::from(x as u64)))
                    .collect::<Vec<_>>();
                let coeff = interpolate(&values).unwrap();
                assert_eq!(coeff[0] + univariate(&coeff, Fr::one()), claim);
                if a == 0 {
                    assert!(coeff[0].is_zero());
                    assert!(univariate(&coeff, Fr::one()).is_zero());
                }
                for x in [Fr::from((*cap + 1) as u64), -Fr::one()] {
                    assert_eq!(univariate(&coeff, x), engine.round_value(x));
                }
                let r = Fr::from((17 + a) as u64);
                claim = univariate(&coeff, r);
                engine.fold(r);
            }
        }
    }
}

#[test]
fn generic_support_is_quotient_closed_and_variant_bound() {
    for (nu, c) in [(0, 0), (0, 1), (1, 0), (1, 1), (2, 2)] {
        for flags in 0..8 {
            if flags & 4 != 0 && nu == 0 {
                continue;
            }
            let p = ValidatedProfile::new_config(nu, c, nu, 5, None, flags).unwrap();
            let (v, u) = p.explicit_supports().unwrap();
            assert_eq!(p.v_count(), v.len());
            assert_eq!(p.u_count(), u.len());
            for a in v.union(&u) {
                for (axis, power) in a.iter().enumerate() {
                    for e in 0..*power {
                        let mut q = vec![0; p.l()];
                        q[axis] = e;
                        q[axis + 1..].copy_from_slice(&a[axis + 1..]);
                        assert!(u.contains(&q), "missing quotient for {a:?}");
                    }
                }
            }
            assert_eq!(
                p,
                ValidatedProfile::from_flags(nu, c, nu, 5, None, flags).unwrap()
            );
        }
    }
    let native = ValidatedProfile::new(2, 2, 2, 5, None, true).unwrap();
    let lookup = ValidatedProfile::new_config(2, 2, 2, 5, None, 5).unwrap();
    assert_ne!(native.profile_id(), lookup.profile_id());
    assert!(lookup.v_count() > native.v_count());
    assert!(ValidatedProfile::new_config(1, 1, 1, 5, None, 9).is_err());
}

#[test]
fn lookup_zero_duplicates_missing_target_and_zero_products() {
    let p = ValidatedProfile::new_lookup(2, 1, 2, 5, None, false).unwrap();
    let mut rng = StdRng::seed_from_u64(1);
    let witness = vec![Fr::zero(); p.n_total()];
    let table = vec![Fr::zero(); p.n() - 1];
    let lookup =
        LookupWitness::new(&p, &table, &witness, LookupFunction::FirstColumn, &mut rng).unwrap();
    assert_eq!(lookup.counts, vec![4, 0, 0]);
    assert_eq!(lookup.addresses, vec![0; 4]);
    let (l, r) = lookup.leaves(Fr::from(7), Fr::from(11)).unwrap();
    assert_eq!(l, r);
    assert!(lookup.leaves(Fr::from(7), Fr::zero()).is_err());
    let mut invalid = witness;
    invalid[0] = Fr::one();
    assert!(
        LookupWitness::new(&p, &table, &invalid, LookupFunction::FirstColumn, &mut rng).is_err()
    );
    // Legal controlled fingerprint: target 1, beta=1, gamma=-2 makes query
    // leaves zero. This checks division-free completeness, not ROM security.
    let witness = vec![Fr::one(); p.n_total()];
    let table = vec![Fr::one(); p.n() - 1];
    let lookup =
        LookupWitness::new(&p, &table, &witness, LookupFunction::FirstColumn, &mut rng).unwrap();
    let (l, r) = lookup.leaves(Fr::one(), -Fr::from(2)).unwrap();
    assert!(l.iter().any(|x| x.is_zero()));
    assert!(r.iter().any(|x| x.is_zero()));
    assert_eq!(l.iter().product::<Fr>(), Fr::zero());
    assert_eq!(r.iter().product::<Fr>(), Fr::zero());
}
