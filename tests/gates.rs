use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};
use hyperplonk_repair::{
    gates::{semantic_witness, virtualize_witness_uses, GateDescriptor, GateFamily},
    native::{bits, eq, Binding, NativeRelation},
    tables::{DenseMle, StructuredPolynomial},
};
use std::collections::{BTreeMap, BTreeSet};

fn sources(gate: &GateDescriptor, nu: usize, seed: u64) -> BTreeMap<String, StructuredPolynomial> {
    let c = gate.width().trailing_zeros() as usize;
    let l = nu + c + 1;
    let fixture = gate.fixture(nu, seed, false).unwrap();
    let mut map = BTreeMap::new();
    for (name, values) in fixture.selectors {
        map.insert(
            name,
            StructuredPolynomial::from_table(l, l - nu, DenseMle::new(values).unwrap()).unwrap(),
        );
    }
    let mut values = fixture.witness;
    values.resize(values.len() * 2, Fr::zero());
    map.insert(
        "W".into(),
        StructuredPolynomial::from_table(l, 0, DenseMle::new(values).unwrap()).unwrap(),
    );
    map
}

#[test]
fn degree_width_and_dense_fixtures_keep_circuit_fixed() {
    for degree in [2, 3, 5, 9, 17, 33] {
        for width in [2, 4, 8, 16, 32] {
            let descriptor = GateDescriptor::new(GateFamily::PowerCopy, width, degree).unwrap();
            let first = descriptor.fixture(3, 17, false).unwrap();
            let second = descriptor.fixture(3, 18, false).unwrap();
            let again = descriptor.fixture(3, 17, false).unwrap();
            assert_eq!(first.selectors, second.selectors);
            assert_eq!(first.wiring, second.wiring);
            assert_eq!(first.witness, again.witness);
            assert_eq!(first.instance_id, again.instance_id);
            assert_ne!(first.witness, second.witness);
            assert_eq!(descriptor.active_columns(), vec![0, 1]);
            assert_eq!(descriptor.cost().selector_count, 2);
            for row in 0..8 {
                assert!(descriptor
                    .row_value(&first.selectors, &first.witness, 8, row)
                    .unwrap()
                    .is_zero());
            }
            for (i, sigma) in first.wiring.iter().enumerate() {
                assert_eq!(first.witness[i], first.witness[*sigma]);
            }
        }
    }
    for terms in [1, 4, 16, 64] {
        let descriptor = GateDescriptor::new(GateFamily::Dense { terms }, 8, 5).unwrap();
        let first = descriptor.fixture(2, 200, false).unwrap();
        let second = descriptor.fixture(2, 201, false).unwrap();
        assert_eq!(descriptor.cost().monomial_terms, terms);
        assert_eq!(descriptor.cost().selector_count, terms + 1);
        assert_eq!(first.selectors, second.selectors);
        assert_ne!(first.witness, second.witness);
        let unique = descriptor
            .terms()
            .iter()
            .map(|t| t.powers.clone())
            .collect::<BTreeSet<_>>();
        assert_eq!(unique.len(), terms);
        assert!(unique
            .iter()
            .all(|e| e.iter().sum::<usize>() == 5 && e[7] == 0));
        for row in 0..4 {
            assert!(descriptor
                .row_value(&first.selectors, &first.witness, 4, row)
                .unwrap()
                .is_zero());
        }
    }
}

#[test]
fn native_gate_maps_match_independent_row_relations() {
    for (family, width, degree) in [
        (GateFamily::PowerCopy, 2, 33),
        (GateFamily::PowerCopy, 32, 5),
        (GateFamily::Dense { terms: 16 }, 8, 5),
        (GateFamily::SingleColumnBoolean, 1, 5),
    ] {
        let descriptor = GateDescriptor::new(family, width, degree).unwrap();
        let c = width.trailing_zeros() as usize;
        let nu = 2;
        let map = sources(&descriptor, nu, 17);
        let relation = descriptor.native_relation(nu + c + 1, nu, c).unwrap();
        for i in 0..1 << (nu + 1) {
            assert!(relation
                .evaluate(&bits(i, nu + 1), &mut |h, z| map[h].evaluate(z))
                .unwrap()
                .is_zero());
        }
        let fixture = descriptor.fixture(nu, 17, false).unwrap();
        let row_point = vec![Fr::from(7), Fr::from(11)];
        let z = Fr::from(13);
        let mut native = vec![z];
        native.extend(&row_point);
        let mut independent = Fr::zero();
        for term in descriptor.terms() {
            let mut value = DenseMle::new(fixture.selectors[&term.selector].clone())
                .unwrap()
                .evaluate(&row_point)
                .unwrap();
            for (a, power) in term.powers.iter().enumerate().filter(|(_, e)| **e > 0) {
                let mut point = vec![z];
                point.extend(bits(a, c));
                point.extend(&row_point);
                value *= map["W"].evaluate(&point).unwrap().pow([*power as u64]);
            }
            independent += value;
        }
        let mut out_point = vec![z];
        out_point.extend(bits(descriptor.output_column(), c));
        out_point.extend(&row_point);
        independent -= map["W"].evaluate(&out_point).unwrap();
        independent -= DenseMle::new(fixture.selectors["qout"].clone())
            .unwrap()
            .evaluate(&row_point)
            .unwrap();
        independent *= Fr::one() - z;
        assert_eq!(
            relation
                .evaluate(&native, &mut |h, z| map[h].evaluate(z))
                .unwrap(),
            independent
        );
    }
}

#[test]
fn core6_compiler_uses_public_semantics_at_every_source_map() {
    let l = 5;
    let stored = (0..16)
        .map(|i| Fr::from((i + 31) as u64))
        .collect::<Vec<_>>();
    for public_log in 0..=4 {
        let public = (0..1 << public_log)
            .map(|i| Fr::from((i + 999) as u64))
            .collect::<Vec<_>>();
        let semantic = semantic_witness(&stored, &public).unwrap();
        assert_eq!(&semantic[..public.len()], public.as_slice());
        assert_ne!(&stored[..public.len()], public.as_slice());
        let mut w = stored.clone();
        w.resize(32, Fr::zero());
        let wp = StructuredPolynomial::from_table(l, 0, DenseMle::new(w).unwrap()).unwrap();
        let pi = StructuredPolynomial::from_table(
            l,
            l - public_log,
            DenseMle::new(public.clone()).unwrap(),
        )
        .unwrap();
        let mut rel = NativeRelation::new(l);
        rel.expression = rel.source("W", (0..l).map(Binding::Variable).collect());
        virtualize_witness_uses(std::slice::from_mut(&mut rel), l, public_log).unwrap();
        for i in 0..16 {
            let point = bits(i, l);
            let value = rel
                .evaluate(&point, &mut |h, z| {
                    if h == "W" {
                        wp.evaluate(z)
                    } else {
                        pi.evaluate(z)
                    }
                })
                .unwrap();
            assert_eq!(value, semantic[i]);
        }
        let point = (0..l).map(|i| Fr::from((i + 3) as u64)).collect::<Vec<_>>();
        let chi = eq(&point[..l - public_log], &vec![Fr::zero(); l - public_log]);
        let expected =
            (Fr::one() - chi) * wp.evaluate(&point).unwrap() + chi * pi.evaluate(&point).unwrap();
        assert_eq!(
            rel.evaluate(&point, &mut |h, z| if h == "W" {
                wp.evaluate(z)
            } else {
                pi.evaluate(z)
            })
            .unwrap(),
            expected
        );
        // A mapped copy-style use with Z fixed to zero and a mixed gate column.
        for leading in [Binding::Fixed(false), Binding::Fixed(true)] {
            let mut r = NativeRelation::new(l - 1);
            r.expression = r.source(
                "W",
                std::iter::once(leading.clone())
                    .chain((0..l - 1).map(Binding::Variable))
                    .collect(),
            );
            virtualize_witness_uses(std::slice::from_mut(&mut r), l, public_log).unwrap();
            let local = point[1..].to_vec();
            let mut full = vec![Fr::from(matches!(leading, Binding::Fixed(true)) as u64)];
            full.extend(&local);
            let chi = eq(&full[..l - public_log], &vec![Fr::zero(); l - public_log]);
            assert_eq!(
                r.evaluate(&local, &mut |h, z| if h == "W" {
                    wp.evaluate(z)
                } else {
                    pi.evaluate(z)
                })
                .unwrap(),
                (Fr::one() - chi) * wp.evaluate(&full).unwrap() + chi * pi.evaluate(&full).unwrap()
            );
        }
    }
}

#[test]
fn k1_and_no_row_fixture_boundaries_are_explicit() {
    let single = GateDescriptor::new(GateFamily::SingleColumnBoolean, 1, 5).unwrap();
    for nu in [0, 1, 4] {
        let f = single.fixture(nu, 77, false).unwrap();
        for row in 0..1 << nu {
            assert!(single
                .row_value(&f.selectors, &f.witness, 1 << nu, row)
                .unwrap()
                .is_zero());
        }
        if nu == 0 {
            assert_eq!(f.wiring, vec![0]);
        }
    }
    let no_rows = GateDescriptor::new(GateFamily::PowerCopy, 4, 5)
        .unwrap()
        .fixture(0, 7, false)
        .unwrap();
    assert_eq!(no_rows.wiring, vec![0, 1, 2, 3]);
    assert!(GateDescriptor::new(GateFamily::PowerCopy, 1, 5).is_err());
    assert!(GateDescriptor::new(GateFamily::SingleColumnBoolean, 2, 5).is_err());
    assert!(GateDescriptor::new(GateFamily::Dense { terms: 2 }, 2, 5).is_err());
    assert!(GateDescriptor::new(GateFamily::Dense { terms: 0 }, 8, 5).is_err());
    assert!(GateDescriptor::new(GateFamily::PowerCopy, 3, 5).is_err());
    assert!(GateDescriptor::new(GateFamily::PowerCopy, 2, 1).is_err());
    assert!(semantic_witness(&[Fr::one(); 4], &[Fr::zero(); 3]).is_err());
    assert!(virtualize_witness_uses(&mut [], 4, 4).is_err());
}
