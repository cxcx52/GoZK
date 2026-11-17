use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{One, Zero};
use hyperplonk_repair::{
    pcs::*,
    profile::ValidatedProfile,
    tables::{DenseMle, MleTerm, StructuredPolynomial},
};
use rand::{rngs::StdRng, SeedableRng};
use std::{collections::BTreeMap, io::Cursor};

fn profile() -> ValidatedProfile {
    ValidatedProfile::new(1, 1, 1, 5, None, true).unwrap()
}
fn source(p: &ValidatedProfile) -> StructuredPolynomial {
    let table = DenseMle::new(
        (0..1usize << p.l())
            .map(|i| Fr::from((i * i + 3) as u64))
            .collect(),
    )
    .unwrap();
    let extras = p
        .v_extras()
        .into_iter()
        .enumerate()
        .map(|(i, e)| (e, Fr::from((i + 1) as u64)))
        .collect();
    StructuredPolynomial::new(
        p.l(),
        vec![MleTerm {
            start: 0,
            table,
            scale: Fr::one(),
        }],
        extras,
    )
    .unwrap()
}
fn helper(p: &ValidatedProfile) -> StructuredPolynomial {
    let table = DenseMle::new(
        (0..1usize << (p.l() - 1))
            .map(|i| Fr::from((2 * i + 9) as u64))
            .collect(),
    )
    .unwrap();
    let extras = p
        .u_extras()
        .into_iter()
        .enumerate()
        .map(|(i, e)| (e, Fr::from((i + 2) as u64)))
        .collect();
    StructuredPolynomial::new(
        p.l(),
        vec![MleTerm {
            start: 1,
            table,
            scale: Fr::one(),
        }],
        extras,
    )
    .unwrap()
}
fn opening(
    srs: &PublicSrs,
    poly: &StructuredPolynomial,
    kind: SourceKind,
    blind: Fr,
    z: Vec<Fr>,
    rng: &mut StdRng,
) -> Opening {
    Opening {
        commitment: commit(srs, poly, kind, blind).unwrap(),
        value: poly.evaluate(&z).unwrap(),
        proof: open_polynomial(srs, poly, kind, &z, blind, rng).unwrap(),
        point: z,
    }
}

#[test]
fn mixed_groups_all_extra_directions_and_boundaries() {
    let p = profile();
    let mut rng = StdRng::seed_from_u64(831);
    let srs = setup(&p, &mut rng).unwrap();
    assert_eq!(
        srs.primary_point_counts(),
        (p.u_count() + 1, p.v_count() + 1)
    );
    let source = source(&p);
    let helper = helper(&p);
    for point in [
        vec![Fr::zero(); p.l()],
        vec![Fr::one(); p.l()],
        vec![Fr::from(19u64); p.l()],
    ] {
        let a = opening(
            &srs,
            &source,
            SourceKind::Source,
            Fr::from(7u64),
            point.clone(),
            &mut rng,
        );
        let b = opening(
            &srs,
            &helper,
            SourceKind::Helper,
            Fr::from(11u64),
            point,
            &mut rng,
        );
        assert!(verify_opening(srs.vk(), &a));
        assert!(verify_opening(srs.vk(), &b));
        assert!(cross_bucket_verify(
            srs.vk(),
            &[a.clone(), b.clone()],
            &[Fr::from(3u64), Fr::from(5u64)]
        ));
        let mut invalid = b.clone();
        invalid.value += Fr::one();
        assert!(!verify_opening(srs.vk(), &invalid));
        assert!(!cross_bucket_verify(
            srs.vk(),
            &[a, invalid],
            &[Fr::from(3u64), Fr::from(5u64)]
        ));
    }
}

#[test]
fn public_srs_roundtrip_rebuilds_caches_and_rejects_damage() {
    let p = profile();
    let mut rng = StdRng::seed_from_u64(832);
    let srs = setup(&p, &mut rng).unwrap();
    let mut bytes = Vec::new();
    srs.write_to(&mut bytes).unwrap();
    let loaded = PublicSrs::read_from(&mut Cursor::new(&bytes), 10000).unwrap();
    assert_eq!(srs.vk().srs_digest(), loaded.vk().srs_digest());
    assert_eq!(srs.cached_point_counts(), loaded.cached_point_counts());
    for (poly, kind) in [
        (source(&p), SourceKind::Source),
        (helper(&p), SourceKind::Helper),
    ] {
        assert_eq!(
            commit(&srs, &poly, kind, Fr::from(9u64)).unwrap(),
            commit(&loaded, &poly, kind, Fr::from(9u64)).unwrap()
        );
        let op = opening(
            &loaded,
            &poly,
            kind,
            Fr::from(9u64),
            vec![Fr::from(23u64); p.l()],
            &mut rng,
        );
        assert!(verify_opening(srs.vk(), &op));
    }
    assert!(PublicSrs::read_from(&mut Cursor::new(&bytes), 1).is_err());
    let mut tail = bytes.clone();
    tail.push(0);
    assert!(PublicSrs::read_from(&mut Cursor::new(tail), 10000).is_err());
    assert!(PublicSrs::read_from(&mut Cursor::new(&bytes[..bytes.len() - 1]), 10000).is_err());
    let mut damaged = bytes;
    damaged[56] ^= 1; // stored digest, after header+parameters
    assert!(PublicSrs::read_from(&mut Cursor::new(damaged), 10000).is_err());
}

#[test]
fn commitments_are_linear_and_reject_wrong_support() {
    let p = profile();
    let mut rng = StdRng::seed_from_u64(833);
    let srs = setup(&p, &mut rng).unwrap();
    let f = source(&p);
    let g = StructuredPolynomial::from_table(
        p.l(),
        p.l() - 1,
        DenseMle::new(vec![Fr::from(6u64), Fr::from(8u64)]).unwrap(),
    )
    .unwrap();
    let cf = commit(&srs, &f, SourceKind::Source, Fr::from(3u64)).unwrap();
    let cg = commit(&srs, &g, SourceKind::Source, Fr::from(5u64)).unwrap();
    let sum = f.scaled(Fr::from(7u64)).add(&g).unwrap();
    assert_eq!(
        cf.scale(Fr::from(7u64)).add(&cg).unwrap(),
        commit(&srs, &sum, SourceKind::Source, Fr::from(26u64)).unwrap()
    );
    assert!(commit(&srs, &f, SourceKind::Helper, Fr::zero()).is_err());
    let mut bad_exp = vec![0; p.l()];
    bad_exp[0] = 3;
    let bad =
        StructuredPolynomial::new(p.l(), vec![], BTreeMap::from([(bad_exp, Fr::one())])).unwrap();
    assert!(commit(&srs, &bad, SourceKind::Source, Fr::zero()).is_err());
    let bad_point = vec![Fr::zero(); p.l() - 1];
    assert!(open_polynomial(
        &srs,
        &f,
        SourceKind::Source,
        &bad_point,
        Fr::zero(),
        &mut rng
    )
    .is_err());
    assert!(cf.add(&Commitment::Helper(G1Affine::zero())).is_err());
}

#[test]
fn zero_polynomial_identity_commitment_and_malformed_openings() {
    let p = profile();
    let mut rng = StdRng::seed_from_u64(834);
    let srs = setup(&p, &mut rng).unwrap();
    let zero = StructuredPolynomial::zero(p.l()).unwrap();
    let op = opening(
        &srs,
        &zero,
        SourceKind::Helper,
        Fr::zero(),
        vec![Fr::zero(); p.l()],
        &mut rng,
    );
    assert_eq!(op.commitment, Commitment::Helper(G1Affine::zero()));
    assert!(verify_opening(srs.vk(), &op));
    let mut short = op.clone();
    short.proof.points.pop();
    assert!(!verify_opening(srs.vk(), &short));
    let mut wrong = op.clone();
    wrong.proof.points[0] = (wrong.proof.points[0] + G1Affine::generator()).into_affine();
    assert!(!verify_opening(srs.vk(), &wrong));
    assert!(!cross_bucket_verify(srs.vk(), &[], &[]));
    assert!(!cross_bucket_verify(srs.vk(), &[op], &[]));
}

#[test]
fn predictable_weights_can_cancel_bad_equations() {
    let p = profile();
    let mut rng = StdRng::seed_from_u64(835);
    let srs = setup(&p, &mut rng).unwrap();
    let f = source(&p);
    let a = opening(
        &srs,
        &f,
        SourceKind::Source,
        Fr::zero(),
        vec![Fr::from(29u64); p.l()],
        &mut rng,
    );
    let mut bad_a = a.clone();
    let mut bad_b = a;
    bad_a.value += Fr::one();
    bad_b.value -= Fr::one();
    assert!(!verify_opening(srs.vk(), &bad_a));
    assert!(!verify_opening(srs.vk(), &bad_b));
    assert!(cross_bucket_verify(
        srs.vk(),
        &[bad_a.clone(), bad_b.clone()],
        &[Fr::one(), Fr::one()]
    ));
    assert!(!cross_bucket_verify(
        srs.vk(),
        &[bad_a, bad_b],
        &[Fr::one(), Fr::from(2u64)]
    ));
}

#[test]
fn non_suffix_embedded_table_commitment() {
    let p = ValidatedProfile::new(2, 2, 1, 5, Some(1), true).unwrap();
    let mut rng = StdRng::seed_from_u64(836);
    let srs = setup(&p, &mut rng).unwrap();
    let table = DenseMle::new(vec![
        Fr::from(2u64),
        Fr::from(8u64),
        Fr::from(5u64),
        Fr::from(17u64),
    ])
    .unwrap();
    let f = StructuredPolynomial::from_table(p.l(), 1, table).unwrap();
    for kind in [SourceKind::Source, SourceKind::Helper] {
        let op = opening(
            &srs,
            &f,
            kind,
            Fr::from(41u64),
            vec![Fr::from(31u64); p.l()],
            &mut rng,
        );
        assert!(verify_opening(srs.vk(), &op));
    }
}

/// Optional artifact for the independent Python oracle. Deterministic seeds
/// are exclusively fixture generation, not production private randomness.
#[test]
#[ignore = "requires explicit cross-language vector output path"]
fn export_cross_language_vector() {
    let Some(path) = std::env::var_os("HP7_PCS_VECTOR_OUT") else {
        return;
    };
    use hyperplonk_repair::codec::{g1_bytes, scalar_bytes};
    let p = profile();
    let mut rng = StdRng::seed_from_u64(837);
    let srs = setup(&p, &mut rng).unwrap();
    let mut encoded = Vec::new();
    srs.write_to(&mut encoded).unwrap();
    let mut cases = Vec::new();
    for (f, kind, blind) in [
        (source(&p), SourceKind::Source, Fr::from(7u64)),
        (helper(&p), SourceKind::Helper, Fr::from(11u64)),
    ] {
        let op = opening(
            &srs,
            &f,
            kind,
            blind,
            vec![Fr::from(37u64); p.l()],
            &mut rng,
        );
        let terms:Vec<_>=f.terms().iter().map(|t|serde_json::json!({"start":t.start,"scale":hex::encode(scalar_bytes(&t.scale)),"table":t.table.values().iter().map(|v|hex::encode(scalar_bytes(v))).collect::<Vec<_>>()})).collect();
        let extras:Vec<_>=f.extras().iter().map(|(e,v)|serde_json::json!({"exponent":e,"coefficient":hex::encode(scalar_bytes(v))})).collect();
        cases.push(serde_json::json!({"group":if kind==SourceKind::Source{2}else{1},"terms":terms,"extras":extras,
            "blind":hex::encode(scalar_bytes(&blind)),"commitment":hex::encode(op.commitment.bytes()),
            "point":op.point.iter().map(|v|hex::encode(scalar_bytes(v))).collect::<Vec<_>>(),"value":hex::encode(scalar_bytes(&op.value)),
            "proof":op.proof.points.iter().map(|v|hex::encode(g1_bytes(v))).collect::<Vec<_>>() }));
    }
    std::fs::write(
        path,
        serde_json::to_vec_pretty(&serde_json::json!({"srs":hex::encode(encoded),"cases":cases}))
            .unwrap(),
    )
    .unwrap();
}

#[test]
#[ignore = "requires independent Python-generated openings"]
fn verify_independent_python_openings() {
    let Some(path) = std::env::var_os("HP7_PCS_PYTHON_OUT") else {
        return;
    };
    use hyperplonk_repair::codec::{g1_from_bytes, g2_from_bytes, scalar_from_bytes};
    let v: serde_json::Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let bytes = hex::decode(v["srs"].as_str().unwrap()).unwrap();
    let srs = PublicSrs::read_from(&mut Cursor::new(bytes), 10000).unwrap();
    let mut openings = Vec::new();
    for case in v["cases"].as_array().unwrap() {
        let raw = hex::decode(case["commitment"].as_str().unwrap()).unwrap();
        let commitment = if case["group"] == 2 {
            Commitment::Source(g2_from_bytes(&raw).unwrap())
        } else {
            Commitment::Helper(g1_from_bytes(&raw).unwrap())
        };
        let point = case["point"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| scalar_from_bytes(&hex::decode(x.as_str().unwrap()).unwrap()).unwrap())
            .collect();
        let value =
            scalar_from_bytes(&hex::decode(case["value"].as_str().unwrap()).unwrap()).unwrap();
        let points = case["proof"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| g1_from_bytes(&hex::decode(x.as_str().unwrap()).unwrap()).unwrap())
            .collect();
        let op = Opening {
            commitment,
            point,
            value,
            proof: OpeningProof { points },
        };
        assert!(verify_opening(srs.vk(), &op));
        openings.push(op);
    }
    assert_eq!(openings.len(), 2);
    assert!(cross_bucket_verify(
        srs.vk(),
        &openings,
        &[Fr::from(3u64), Fr::from(5u64)]
    ));
}
