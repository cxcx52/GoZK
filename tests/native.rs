use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};
use hyperplonk_repair::{
    native::{bits, interpolate, univariate, Binding, Expr, NativeRelation, NativeSumcheck},
    tables::{DenseMle, StructuredPolynomial},
};
use std::collections::BTreeMap;

fn f(x: u64) -> Fr {
    Fr::from(x)
}

fn fixture() -> (
    usize,
    Vec<NativeRelation>,
    BTreeMap<String, StructuredPolynomial>,
    StructuredPolynomial,
    Fr,
) {
    let l = 5;
    let bare = StructuredPolynomial::from_table(
        l,
        0,
        DenseMle::new((0..16).map(|i| f((i * i + 3 * i + 2) as u64)).collect()).unwrap(),
    )
    .unwrap();
    // Masks vanish on Boolean points but have overlapping powers and survive
    // distinct source-coordinate maps, including the shifted child maps.
    let extras = BTreeMap::from([
        (vec![2, 0, 0, 0], f(3)),
        (vec![1, 0, 0, 0], -f(3)),
        (vec![0, 0, 0, 2], f(5)),
        (vec![0, 0, 0, 1], -f(5)),
        (vec![1, 0, 0, 2], f(7)),
        (vec![1, 0, 0, 1], -f(7)),
        (vec![0, 2, 0, 0], f(11)),
        (vec![0, 1, 0, 0], -f(11)),
        (vec![2, 0, 0, 2], f(13)),
        (vec![2, 0, 0, 1], -f(13)),
    ]);
    // Last two terms =13 Z^2 phi(last), still Boolean vanishing.
    let extras = extras
        .into_iter()
        .map(|(mut e, c)| {
            e.push(0);
            (e, c)
        })
        .collect();
    let masked = bare
        .add(&StructuredPolynomial::new(l, vec![], extras).unwrap())
        .unwrap();
    let polys = BTreeMap::from([("masked".into(), masked), ("bare".into(), bare)]);
    use Binding::{Complement as C, Fixed as F, Variable as V};
    let specifications = vec![
        (5, vec![V(0), V(1), V(3), V(4)]), // full native span, skipped coordinate
        (4, vec![V(0), V(1), V(2), V(3)]),
        (3, vec![F(false), V(0), V(1), V(2)]), // parent/leaf fixed first coordinate
        (3, vec![V(0), V(1), V(2), F(false)]), // left child, last coordinate fixed
        (3, vec![V(0), V(1), V(2), F(true)]),  // right child
        (2, vec![V(0), F(true), F(false), V(1)]), // gate column extraction
        (1, vec![F(true), F(false), F(true), V(0)]),
        (4, vec![C(0), V(1), C(2), C(3)]),
        (3, vec![F(true), C(0), V(1), C(2)]),
    ];
    let relations = specifications
        .into_iter()
        .enumerate()
        .map(|(i, (d, mut map))| {
            map.push(F(false)); // Absent last source coordinate is fixed explicitly.
            let mut relation = NativeRelation::new(d);
            let left = relation.source("masked", map.clone());
            let right = relation.source("bare", map);
            relation.expression = left
                .minus(right)
                .times(Expr::constant(1).minus(Expr::Variable(0)));
            relation.weight = f((i + 2) as u64);
            relation.tau = if i == 6 {
                None
            } else {
                Some((0..d).map(|a| f((a + i + 3) as u64)).collect())
            };
            relation
        })
        .collect();
    let mut helper_terms = BTreeMap::new();
    let inv2 = f(2).inverse().unwrap();
    for axis in 0..l {
        for power in if axis == 0 { 2..=4 } else { 1..=3 } {
            let coefficient = f((17 + axis * 5 + power) as u64);
            let mut a = vec![0; l];
            a[axis] = power;
            *helper_terms.entry(a).or_default() += coefficient;
            let mut low = vec![0; l];
            if axis == 0 {
                low[0] = 1;
            }
            *helper_terms.entry(low).or_default() -=
                coefficient * if axis == 0 { Fr::one() } else { inv2 };
        }
    }
    (
        l,
        relations,
        polys,
        StructuredPolynomial::new(l, vec![], helper_terms).unwrap(),
        f(23),
    )
}

fn global_value(
    point: &[Fr],
    relations: &[NativeRelation],
    polys: &BTreeMap<String, StructuredPolynomial>,
    helper: &StructuredPolynomial,
    rho: Fr,
) -> Fr {
    let mut value = rho * helper.evaluate(point).unwrap();
    for relation in relations {
        let offset = point.len() - relation.dimension;
        let pad: Fr = point[..offset].iter().map(|x| Fr::one() - x).product();
        let mut get = |handle: &str, p: &[Fr]| polys[handle].evaluate(p);
        value += pad * relation.evaluate(&point[offset..], &mut get).unwrap();
    }
    value
}

#[test]
fn native_suffix_folding_matches_independent_full_global_enumeration() {
    let (l, relations, polys, helper, rho) = fixture();
    let mut sumcheck =
        NativeSumcheck::new(l, relations.clone(), &polys, helper.clone(), rho).unwrap();
    let mut prefix = vec![];
    let challenges = [f(3), f(5), Fr::zero(), Fr::one(), f(13)];
    let mut previous = Fr::zero();
    for axis in 0..l {
        assert_eq!(
            sumcheck.round_value(Fr::zero()) + sumcheck.round_value(Fr::one()),
            previous
        );
        if axis == 0 {
            assert!(sumcheck.round_value(Fr::zero()).is_zero());
            assert!(sumcheck.round_value(Fr::one()).is_zero());
        }
        for x in [Fr::zero(), Fr::one(), f(2), -f(7), f(19)] {
            let expected: Fr = (0..1usize << (l - axis - 1))
                .map(|i| {
                    let mut point = prefix.clone();
                    point.push(x);
                    point.extend(bits(i, l - axis - 1));
                    global_value(&point, &relations, &polys, &helper, rho)
                })
                .sum();
            assert_eq!(sumcheck.round_value(x), expected, "round {axis}");
        }
        previous = sumcheck.round_value(challenges[axis]);
        sumcheck.fold(challenges[axis]);
        prefix.push(challenges[axis]);
    }
    assert_eq!(
        previous,
        global_value(&prefix, &relations, &polys, &helper, rho)
    );
    // Each mapped dense table is folded exactly once down its geometric suffix
    // sequence. There are two sources per relation and no padded 2^L tables.
    let expected_pairs: usize = relations
        .iter()
        .map(|r| {
            r.sources
                .iter()
                .map(|s| {
                    let active = s
                        .map
                        .iter()
                        .filter(|b| matches!(b, Binding::Variable(_) | Binding::Complement(_)))
                        .count();
                    (1usize << active) - 1
                })
                .sum::<usize>()
        })
        .sum();
    assert_eq!(sumcheck.fold_pairs, expected_pairs);
}

#[test]
fn invalid_witness_is_prover_rejected_and_is_not_counted_as_verifier_test() {
    let (l, relations, mut polys, helper, rho) = fixture();
    let constant =
        StructuredPolynomial::new(l, vec![], BTreeMap::from([(vec![0; l], Fr::one())])).unwrap();
    polys.insert("masked".into(), polys["masked"].add(&constant).unwrap());
    assert!(NativeSumcheck::new(l, relations, &polys, helper, rho).is_err());
}

#[test]
fn interpolation_recovers_sparse_coefficients_including_zero_leading_terms() {
    let coefficients = vec![f(2), -f(3), Fr::zero(), f(7), Fr::zero(), f(11), Fr::zero()];
    let samples = (0..coefficients.len())
        .map(|i| univariate(&coefficients, f(i as u64)))
        .collect::<Vec<_>>();
    assert_eq!(interpolate(&samples).unwrap(), coefficients);
    let recovered = interpolate(&samples).unwrap();
    for x in [f(9), -f(2), Fr::zero()] {
        assert_eq!(univariate(&recovered, x), univariate(&coefficients, x));
    }
}

#[test]
fn malformed_native_dimensions_and_maps_are_errors() {
    let (l, relations, polys, helper, rho) = fixture();
    assert!(NativeSumcheck::new(0, relations.clone(), &polys, helper.clone(), rho).is_err());
    assert!(NativeSumcheck::new(l - 1, relations.clone(), &polys, helper.clone(), rho).is_err());
    let mut invalid = relations.clone();
    invalid[0].dimension = l + 1;
    assert!(NativeSumcheck::new(l, invalid, &polys, helper.clone(), rho).is_err());
    let mut invalid = relations.clone();
    invalid[0].dimension = 0;
    assert!(NativeSumcheck::new(l, invalid, &polys, helper.clone(), rho).is_err());
    let mut invalid = relations.clone();
    invalid[0].tau = Some(vec![]);
    assert!(NativeSumcheck::new(l, invalid, &polys, helper.clone(), rho).is_err());
    let mut invalid = relations.clone();
    invalid[0].sources[0].map[4] = Binding::Variable(99);
    assert!(NativeSumcheck::new(l, invalid, &polys, helper.clone(), rho).is_err());
    let mut invalid = relations.clone();
    invalid[0].sources[0].map.pop();
    assert!(NativeSumcheck::new(l, invalid, &polys, helper.clone(), rho).is_err());
    let mut invalid = relations.clone();
    invalid[0].sources[0].map.swap(0, 1);
    assert!(NativeSumcheck::new(l, invalid, &polys, helper.clone(), rho).is_err());
    let mut invalid = relations;
    invalid[0].sources[0].handle = "missing".into();
    assert!(NativeSumcheck::new(l, invalid, &polys, helper, rho).is_err());
}
