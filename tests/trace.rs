use ark_bls12_381::Fr;
use ark_ff::{One, PrimeField, Zero};
use hyperplonk_repair::trace::{is_irreducible, ExtensionField, TraceMask};
use std::sync::Arc;

fn values(n: usize, start: u64) -> Vec<Fr> {
    (0..n).map(|i| Fr::from(start + i as u64)).collect()
}
fn uni(coefficients: &[Fr], x: Fr) -> Fr {
    coefficients.iter().rev().fold(Fr::zero(), |v, c| v * x + c)
}

#[test]
fn certified_extension_arithmetic_and_matrix_trace_match_frobenius() {
    for degree in [1, 2, 3, 4, 5] {
        let field = ExtensionField::new(degree).unwrap();
        assert!(is_irreducible(field.modulus()));
        let (a, b, c) = (values(degree, 3), values(degree, 11), values(degree, 19));
        assert_eq!(field.mul(&a, &field.one()).unwrap(), a);
        assert_eq!(
            field.mul(&field.mul(&a, &b).unwrap(), &c).unwrap(),
            field.mul(&a, &field.mul(&b, &c).unwrap()).unwrap()
        );
        let mut sum = field.zero();
        let mut conjugate = a.clone();
        for _ in 0..degree {
            sum = field.add(&sum, &conjugate).unwrap();
            conjugate = field.pow(&conjugate, Fr::MODULUS.as_ref()).unwrap();
        }
        assert_eq!(conjugate, a);
        assert_eq!(sum[0], field.trace(&a).unwrap());
        assert!(sum[1..].iter().all(Zero::is_zero));
        assert_eq!(field.trace(&field.one()).unwrap(), Fr::from(degree as u64));
    }
    assert!(!is_irreducible(&[-Fr::one(), Fr::zero(), Fr::one()]));
    assert!(!is_irreducible(&[Fr::one(), Fr::zero(), Fr::from(2)]));
    assert!(ExtensionField::new(0).is_err());
    assert!(ExtensionField::new(26).is_err());
}

#[test]
fn trace_masks_boolean_vanishing_line_and_quotient_identity() {
    for degree in [1, 2, 3, 4, 5] {
        let field = Arc::new(ExtensionField::new(degree).unwrap());
        for budget in [1, 3, 6] {
            let coefficients = (0..budget)
                .map(|k| values(degree, 2 + 7 * k as u64))
                .collect();
            let mask = TraceMask::from_coefficients(field.clone(), coefficients).unwrap();
            for bits in 0..1 << degree {
                let point = (0..degree)
                    .map(|i| Fr::from(((bits >> i) & 1) as u64))
                    .collect::<Vec<_>>();
                assert_eq!(mask.evaluate(&point).unwrap(), Fr::zero());
            }
            for point in [
                vec![Fr::zero(); degree],
                vec![Fr::one(); degree],
                values(degree, 7),
            ] {
                let quotients = mask.quotients(&point).unwrap();
                for x in [
                    values(degree, 13),
                    values(degree, 29),
                    vec![Fr::one(); degree],
                ] {
                    let rhs: Fr = quotients
                        .iter()
                        .enumerate()
                        .map(|(i, q)| (x[i] - point[i]) * q.evaluate(&field, &x).unwrap())
                        .sum();
                    assert_eq!(
                        mask.evaluate(&x).unwrap() - mask.evaluate(&point).unwrap(),
                        rhs
                    );
                }
                for axis in 0..degree {
                    let line = mask.line_coefficients(&point, axis).unwrap();
                    assert_eq!(line.len(), budget + 2);
                    for x in [Fr::zero(), Fr::one(), Fr::from(17), -Fr::one()] {
                        let mut p = point.clone();
                        p[axis] = x;
                        assert_eq!(uni(&line, x), mask.evaluate(&p).unwrap());
                    }
                }
            }
        }
    }
}

#[test]
fn trace_shape_boundaries_rejected() {
    let f = Arc::new(ExtensionField::new(2).unwrap());
    assert!(TraceMask::from_coefficients(f.clone(), vec![]).is_err());
    assert!(TraceMask::from_coefficients(f.clone(), vec![vec![Fr::one()]]).is_err());
    let mask = TraceMask::from_coefficients(f, vec![values(2, 1)]).unwrap();
    assert!(mask.evaluate(&[Fr::one()]).is_err());
    assert!(mask.quotients(&[]).is_err());
    assert!(mask.line_coefficients(&values(2, 1), 2).is_err());
}

#[test]
#[ignore = "explicit offline modulus certificate sweep for all scale dimensions"]
fn export_all_extension_certificates() {
    let path = std::env::var("HP7_TRACE_CERTIFICATES").expect("set certificate output path");
    let mut certificates = vec![];
    for degree in 1..=25 {
        let started = std::time::Instant::now();
        let field = ExtensionField::new(degree).unwrap();
        let mut certificate = field.certificate();
        certificate["seconds"] = serde_json::json!(started.elapsed().as_secs_f64());
        eprintln!("degree {degree}: {} candidates", field.tested_candidates());
        certificates.push(certificate);
        std::fs::write(&path, serde_json::to_vec_pretty(&certificates).unwrap()).unwrap();
    }
    assert_eq!(certificates.len(), 25);
}

#[test]
#[ignore = "explicit independent Python trace-vector bridge"]
fn export_trace_vectors() {
    use hyperplonk_repair::codec::scalar_bytes;
    let path = std::env::var("HP7_TRACE_VECTORS").expect("set trace vector output path");
    let encode = |v: &[Fr]| {
        v.iter()
            .map(|x| hex::encode(scalar_bytes(x)))
            .collect::<Vec<_>>()
    };
    let mut cases = vec![];
    for degree in 1..=5 {
        let field = Arc::new(ExtensionField::new(degree).unwrap());
        let coefficients = (0..6)
            .map(|i| values(degree, 3 + 9 * i as u64))
            .collect::<Vec<_>>();
        let mask = TraceMask::from_coefficients(field.clone(), coefficients.clone()).unwrap();
        let point = values(degree, 7);
        let x = values(degree, 19);
        let quotients = mask.quotients(&point).unwrap();
        cases.push(serde_json::json!({"certificate":field.certificate(),"coefficients":coefficients.iter().map(|v|encode(v)).collect::<Vec<_>>(),"point":encode(&point),"x":encode(&x),"point_value":hex::encode(scalar_bytes(&mask.evaluate(&point).unwrap())),"x_value":hex::encode(scalar_bytes(&mask.evaluate(&x).unwrap())),"quotient_values":encode(&quotients.iter().map(|q|q.evaluate(&field,&x).unwrap()).collect::<Vec<_>>()),"lines":(0..degree).map(|a|encode(&mask.line_coefficients(&point,a).unwrap())).collect::<Vec<_>>() }));
    }
    std::fs::write(path, serde_json::to_vec_pretty(&cases).unwrap()).unwrap();
}
