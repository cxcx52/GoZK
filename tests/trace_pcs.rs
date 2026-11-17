use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{One, Zero};
use hyperplonk_repair::{
    pcs::{verify_opening, Commitment, Opening},
    tables::{DenseMle, StructuredPolynomial},
    trace::{ExtensionField, TraceMask},
    trace_pcs::*,
};
use rand::{rngs::StdRng, SeedableRng};
use std::{collections::BTreeMap, io::Cursor, sync::Arc};

#[test]
fn genuine_trace_sources_helpers_batch_and_public_key_roundtrip() {
    let mut rng = StdRng::seed_from_u64(51001);
    for l in 1..=4 {
        let field = Arc::new(ExtensionField::new(l).unwrap());
        let par = TraceParameters::new(l, 5, 14).unwrap();
        let srs = ValidatedTraceSrs::setup(par.clone(), field.clone(), &mut rng, 100_000).unwrap();
        let table = DenseMle::new(
            (0..1usize << l)
                .map(|i| Fr::from((3 + i * i) as u64))
                .collect(),
        )
        .unwrap();
        let source = TraceSource::new(
            StructuredPolynomial::from_table(l, 0, table).unwrap(),
            Some(TraceMask::sample(field, 5, &mut rng).unwrap()),
        )
        .unwrap();
        let blind = Fr::from(23u64);
        let commitment = Commitment::Source(commit_source(&srs, &source, blind).unwrap());
        for point in [
            vec![Fr::zero(); l],
            vec![Fr::one(); l],
            (0..l).map(|i| Fr::from((7 + 3 * i) as u64)).collect(),
        ] {
            let op = Opening {
                commitment,
                point: point.clone(),
                value: source.evaluate(&point).unwrap(),
                proof: open_source(&srs, &source, &point, blind, &mut rng).unwrap(),
            };
            assert!(verify_opening(srs.vk(), &op));
            let mut bad = op.clone();
            bad.value += Fr::one();
            assert!(!verify_opening(srs.vk(), &bad));
            let mut bad = op.clone();
            bad.proof.points[0] = (bad.proof.points[0] + G1Affine::generator()).into_affine();
            assert!(!verify_opening(srs.vk(), &bad));
            let mut ex = BTreeMap::new();
            for axis in 0..l {
                let mut e = vec![0; l];
                e[axis] = 14;
                ex.insert(e, Fr::from((axis + 4) as u64));
            }
            let helper = StructuredPolynomial::new(l, vec![], ex).unwrap();
            let hc = Commitment::Helper(commit_helper(&srs, &helper, blind).unwrap());
            let ho = Opening {
                commitment: hc,
                point: point.clone(),
                value: helper.evaluate(&point).unwrap(),
                proof: open_helper(&srs, &helper, &point, blind, &mut rng).unwrap(),
            };
            assert!(verify_opening(srs.vk(), &ho));
            let sum = source.add(&source.scaled(Fr::from(7u64)).unwrap()).unwrap();
            let sumblind = blind * Fr::from(8u64);
            let sc = commit_source(&srs, &sum, sumblind).unwrap();
            assert_eq!(
                sc,
                match commitment.scale(Fr::from(8u64)) {
                    Commitment::Source(c) => c,
                    _ => unreachable!(),
                }
            );
            let so = Opening {
                commitment: Commitment::Source(sc),
                point: point.clone(),
                value: sum.evaluate(&point).unwrap(),
                proof: open_source(&srs, &sum, &point, sumblind, &mut rng).unwrap(),
            };
            assert!(verify_opening(srs.vk(), &so));
        }
        let mut bytes = vec![];
        srs.write_to(&mut bytes).unwrap();
        let loaded = ValidatedTraceSrs::read_from(&mut Cursor::new(&bytes), 100_000).unwrap();
        assert_eq!(loaded.parameters(), &par);
        assert_eq!(loaded.vk().srs_digest(), srs.vk().srs_digest());
        assert_eq!(
            commit_source(&loaded, &source, blind).unwrap(),
            match commitment {
                Commitment::Source(c) => c,
                _ => unreachable!(),
            }
        );
        let mut corrupt = bytes.clone();
        let digest_offset = 8 + 24 + 32 * (l + 1);
        corrupt[digest_offset] ^= 1;
        assert!(ValidatedTraceSrs::read_from(&mut Cursor::new(&corrupt), 100_000).is_err());
        assert!(ValidatedTraceSrs::read_from(&mut Cursor::new(&bytes), 1).is_err());
        let mut extra = bytes;
        extra.push(0);
        assert!(ValidatedTraceSrs::read_from(&mut Cursor::new(&extra), 100_000).is_err());
    }
}

#[test]
fn actual_trace_support_is_checked_before_opening() {
    let mut rng = StdRng::seed_from_u64(51002);
    let field = Arc::new(ExtensionField::new(2).unwrap());
    let srs = ValidatedTraceSrs::setup(
        TraceParameters::new(2, 5, 14).unwrap(),
        field.clone(),
        &mut rng,
        100_000,
    )
    .unwrap();
    let zero = StructuredPolynomial::zero(2).unwrap();
    let wrong = TraceSource::new(
        zero.clone(),
        Some(TraceMask::sample(field, 6, &mut rng).unwrap()),
    )
    .unwrap();
    assert!(commit_source(&srs, &wrong, Fr::zero()).is_err());
    assert!(open_source(&srs, &wrong, &[Fr::zero(); 2], Fr::zero(), &mut rng).is_err());
    let helper = StructuredPolynomial::new(2, vec![], [(vec![1, 1], Fr::one())].into()).unwrap();
    assert!(commit_helper(&srs, &helper, Fr::zero()).is_err());
    assert!(open_helper(&srs, &helper, &[Fr::zero(); 2], Fr::zero(), &mut rng).is_err());
    let degree = StructuredPolynomial::new(2, vec![], [(vec![15, 0], Fr::one())].into()).unwrap();
    assert!(commit_helper(&srs, &degree, Fr::zero()).is_err());
    assert!(TraceParameters::new(26, 5, 14).is_err());
    assert!(TraceParameters::new(2, 5, 5).is_err());
    assert!(ValidatedTraceSrs::setup(
        TraceParameters::new(2, 5, 14).unwrap(),
        Arc::new(ExtensionField::new(1).unwrap()),
        &mut rng,
        1000
    )
    .is_err());
}
