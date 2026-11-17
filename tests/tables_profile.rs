use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};
use hyperplonk_repair::{
    profile::ValidatedProfile,
    tables::{DenseMle, MleTerm, StructuredPolynomial},
};
use std::collections::{BTreeMap, BTreeSet};

fn f(x: u64) -> Fr {
    Fr::from(x)
}
fn points(dimension: usize) -> Vec<Vec<Fr>> {
    (0..1usize << dimension)
        .map(|i| {
            (0..dimension)
                .map(|j| f(((i >> (dimension - 1 - j)) & 1) as u64))
                .collect()
        })
        .collect()
}

#[test]
fn msb_table_and_fold_agree_with_independent_lagrange_sum() {
    let values = (0..32)
        .map(|i| f((i * i + 3 * i + 7) as u64))
        .collect::<Vec<_>>();
    let table = DenseMle::new(values.clone()).unwrap();
    for (i, point) in points(5).iter().enumerate() {
        assert_eq!(table.evaluate(point).unwrap(), values[i]);
    }
    let point = [f(2), f(7), f(0), f(1), -f(3)];
    let expected: Fr = points(5)
        .iter()
        .zip(&values)
        .map(|(bits, value)| {
            *value
                * bits
                    .iter()
                    .zip(point)
                    .map(|(bit, x)| if bit.is_zero() { Fr::one() - x } else { x })
                    .product::<Fr>()
        })
        .sum();
    assert_eq!(table.evaluate(&point).unwrap(), expected);
    let mut view = table.fold_view();
    for x in point {
        for suffix in 0..view.values().len() / 2 {
            let half = view.values().len() / 2;
            assert_eq!(
                view.at_current(x, suffix).unwrap(),
                (Fr::one() - x) * view.values()[suffix] + x * view.values()[half + suffix]
            );
        }
        view.fold(x).unwrap();
    }
    assert_eq!(view.values(), &[expected]);
    assert_eq!(view.work().pairs, 31);
    assert!(view.fold(f(0)).is_err());
    assert!(DenseMle::new(vec![]).is_err());
    assert!(DenseMle::new(vec![f(0); 3]).is_err());
    assert!(table.evaluate(&point[..4]).is_err());
}

#[test]
fn structured_quotients_handle_zero_one_points_and_high_extras() {
    let dimension = 5;
    let terms = vec![
        MleTerm {
            start: 0,
            table: DenseMle::new((0..32).map(|i| f((i * i + 11) as u64)).collect()).unwrap(),
            scale: f(3),
        },
        MleTerm {
            start: 2,
            table: DenseMle::new(vec![f(5), f(9), f(2), f(3)]).unwrap(),
            scale: -f(7),
        },
        MleTerm {
            start: 5,
            table: DenseMle::new(vec![f(19)]).unwrap(),
            scale: f(2),
        },
    ];
    let extras = BTreeMap::from([
        (vec![2, 0, 0, 0, 2], f(7)),
        (vec![0, 0, 4, 0, 1], -f(9)),
        (vec![0; 5], f(21)),
    ]);
    let poly = StructuredPolynomial::new(dimension, terms, extras).unwrap();
    let queries = [
        vec![Fr::zero(); 5],
        vec![Fr::one(); 5],
        vec![f(3), f(1), f(0), -f(4), f(19)],
    ];
    for z in queries {
        let (value, quotients, work) = poly.canonical_quotients(&z).unwrap();
        assert_eq!(value, poly.evaluate(&z).unwrap());
        assert_eq!(work.pairs, 31 + 3);
        assert_eq!(work.quotient_cells, 31 + 3);
        for x in [
            vec![f(2), f(3), f(5), f(7), f(11)],
            vec![f(0), f(1), f(0), f(1), f(0)],
            z.clone(),
        ] {
            let rhs: Fr = quotients
                .iter()
                .enumerate()
                .map(|(i, q)| (x[i] - z[i]) * q.evaluate(&x).unwrap())
                .sum();
            assert_eq!(poly.evaluate(&x).unwrap() - value, rhs);
        }
        for (axis, q) in quotients.iter().enumerate() {
            assert!(q.terms().iter().all(|t| t.start > axis));
            assert!(q.extras().keys().all(|e| e[..axis].iter().all(|d| *d == 0)));
        }
    }
}

#[test]
fn dense_quotient_work_is_geometric_and_preserves_suffix_layout() {
    for dimension in [1, 2, 5, 10, 14] {
        let n = 1usize << dimension;
        let poly = StructuredPolynomial::from_table(
            dimension,
            0,
            DenseMle::new((0..n).map(|i| f(i as u64)).collect()).unwrap(),
        )
        .unwrap();
        let (value, qs, work) = poly.canonical_quotients(&vec![f(3); dimension]).unwrap();
        assert_eq!(work.pairs, n - 1);
        assert_eq!(work.quotient_cells, n - 1);
        assert_eq!(qs.iter().map(|q| q.table_cells()).sum::<usize>(), n - 1);
        for (i, q) in qs.iter().enumerate() {
            assert_eq!(q.terms()[0].table.values().len(), n >> (i + 1));
        }
        assert_eq!(value, poly.evaluate(&vec![f(3); dimension]).unwrap());
    }
}

fn quotients_of(a: &[usize]) -> BTreeSet<Vec<usize>> {
    let mut out = BTreeSet::new();
    for axis in 0..a.len() {
        for degree in 0..a[axis] {
            let mut e = a.to_vec();
            e[..axis].fill(0);
            e[axis] = degree;
            out.insert(e);
        }
    }
    out
}

#[test]
fn symbolic_supports_equal_independent_quotient_closure() {
    for nu in 1..=3 {
        for c in 1..=3 {
            for anchor in 1..=c {
                for tight in [false, true] {
                    for degree in [2, 5] {
                        let p =
                            ValidatedProfile::new(nu, c, nu, degree, Some(anchor), tight).unwrap();
                        let (v, u) = p.explicit_supports().unwrap();
                        assert_eq!(v.len(), p.v_count());
                        assert_eq!(u.len(), p.u_count());
                        let mut expected: BTreeSet<_> =
                            v.iter().flat_map(|a| quotients_of(a)).collect();
                        for (axis, cap) in p.e().iter().enumerate() {
                            for power in 1..=*cap {
                                let mut e = vec![0; p.l()];
                                e[axis] = power;
                                expected.insert(e);
                            }
                        }
                        loop {
                            let previous = expected.len();
                            let added: BTreeSet<_> =
                                expected.iter().flat_map(|a| quotients_of(a)).collect();
                            expected.extend(added);
                            if expected.len() == previous {
                                break;
                            }
                        }
                        assert_eq!(u, expected);
                        for a in &v {
                            assert!(p.contains_v(a));
                        }
                        for a in &u {
                            assert!(p.contains_u(a));
                        }
                        // Probe excluded directions by changing each legal exponent in turn.
                        for a in v.iter().chain(u.iter()) {
                            for axis in 0..p.l() {
                                for power in [0, 1, 2, 3, degree + 3] {
                                    let mut probe = a.clone();
                                    probe[axis] = power;
                                    assert_eq!(p.contains_v(&probe), v.contains(&probe));
                                    assert_eq!(p.contains_u(&probe), u.contains(&probe));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn profile_counts_match_paper_and_keep_adversarial_degree() {
    let old = ValidatedProfile::new(20, 3, 20, 5, None, false).unwrap();
    let tight = ValidatedProfile::new(20, 3, 20, 5, None, true).unwrap();
    assert_eq!(tight.l(), 24);
    assert_eq!(tight.k(), 8);
    assert_eq!(tight.n_total(), 1 << 23);
    let mut actual = vec![4, 6, 4, 12];
    actual.extend(vec![7; 19]);
    actual.push(12);
    assert_eq!(tight.d(), actual);
    assert_eq!(old.e(), actual);
    assert_eq!(tight.e()[23], 7);
    assert_eq!(tight.round_scalar_count(), 165);
    assert_eq!(old.round_scalar_count(), 170);
    assert_eq!(tight.v_count(), (1 << 24) + 14);
    assert_eq!(tight.u_count(), (1 << 23) + 152);
    assert_eq!(tight.delta(), 24);
    assert_eq!(old.u_count() - tight.u_count(), 5);
    assert!(tight.explicit_supports().is_err());
    assert_ne!(tight.profile_id(), old.profile_id());
}

#[test]
fn invalid_profiles_and_shapes_rejected() {
    for args in [
        (0, 1, 0, 5, None, false),
        (1, 0, 0, 5, None, false),
        (1, 1, 3, 5, None, false),
        (1, 1, 1, 1, None, false),
        (1, 1, 1, 5, Some(0), false),
        (1, 1, 1, 5, Some(2), false),
        (64, 1, 1, 5, None, false),
        (1, 1, 1, usize::MAX, None, false),
    ] {
        assert!(ValidatedProfile::new(args.0, args.1, args.2, args.3, args.4, args.5).is_err());
    }
    let p = ValidatedProfile::new(2, 2, 2, 5, None, true).unwrap();
    assert!(p.contains_mle_u(1, 4));
    assert!(p.contains_mle_u(0, 3));
    assert!(!p.contains_mle_u(0, 4));
    assert!(!p.contains_mle_v(5, 1));
    assert!(!p.contains_v(&[0, 0]));
    assert!(!p.contains_u(&[0, 0]));
    assert!(StructuredPolynomial::new(0, vec![], BTreeMap::new()).is_err());
    assert!(StructuredPolynomial::new(
        3,
        vec![MleTerm {
            start: 2,
            table: DenseMle::new(vec![f(1); 4]).unwrap(),
            scale: f(1)
        }],
        BTreeMap::new()
    )
    .is_err());
}

#[test]
fn addition_and_scaling_keep_independent_tables_shared_semantics() {
    let a = StructuredPolynomial::from_table(
        3,
        1,
        DenseMle::new(vec![f(2), f(4), f(6), f(8)]).unwrap(),
    )
    .unwrap();
    let b = StructuredPolynomial::new(3, vec![], BTreeMap::from([(vec![1, 0, 2], f(13))])).unwrap();
    let c = a.scaled(f(7)).add(&b.scaled(-f(2))).unwrap();
    let point = [f(3), f(5), f(7)];
    assert_eq!(
        c.evaluate(&point).unwrap(),
        f(7) * a.evaluate(&point).unwrap() - f(2) * b.evaluate(&point).unwrap()
    );
    assert_eq!(a.scaled(f(0)).evaluate(&point).unwrap(), Fr::zero());
    assert!(a.add(&StructuredPolynomial::zero(2).unwrap()).is_err());
}

#[test]
fn profile_golden_vectors_from_python() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("testdata/profiles.json");
    let raw = std::fs::read(path)
        .expect("generate testdata/profiles.json remotely with profile_vectors.py first");
    let records: Vec<serde_json::Value> = serde_json::from_slice(&raw).unwrap();
    assert_eq!(records.len(), 9);
    for r in records {
        let n = |key: &str| r[key].as_u64().unwrap() as usize;
        let p = ValidatedProfile::new(
            n("nu"),
            n("c"),
            n("public_log"),
            n("degree"),
            Some(n("anchor")),
            r["tight"].as_bool().unwrap(),
        )
        .unwrap();
        assert_eq!(p.profile_id(), r["profile_id"].as_str().unwrap());
        assert_eq!(
            p.e(),
            serde_json::from_value::<Vec<usize>>(r["E"].clone()).unwrap()
        );
        assert_eq!(
            p.d(),
            serde_json::from_value::<Vec<usize>>(r["D"].clone()).unwrap()
        );
        assert_eq!(p.l(), n("L"));
        assert_eq!(p.n_total(), n("N"));
        assert_eq!(p.v_count(), n("v_count"));
        assert_eq!(p.u_count(), n("u_count"));
        assert_eq!(p.b_v(), n("b_V"));
        assert_eq!(p.b_u(), n("b_U"));
        assert_eq!(p.delta(), n("Delta"));
        assert_eq!(p.round_scalar_count(), n("round_scalar_count"));
        if let Some(v) = r.get("v_support") {
            let (actual_v, actual_u) = p.explicit_supports().unwrap();
            assert_eq!(
                actual_v,
                serde_json::from_value::<BTreeSet<Vec<usize>>>(v.clone()).unwrap()
            );
            assert_eq!(
                actual_u,
                serde_json::from_value::<BTreeSet<Vec<usize>>>(r["u_support"].clone()).unwrap()
            );
        }
    }
}
