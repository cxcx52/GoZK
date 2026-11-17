use ark_bls12_381::Fr;
use ark_ff::{BigInteger, PrimeField};
use hyperplonk_repair::{
    index::{self, ValidatedIndex},
    pcs::PublicSrs,
    profile::ValidatedProfile,
    protocol,
};
use rand::rngs::OsRng;
use rand::{rngs::StdRng, SeedableRng};

#[test]
fn core7_profiles_and_rejection_paths() {
    for (nu, c, publog, degree, anchor, tight) in [
        (1, 1, 1, 5, 1, false),
        (1, 1, 1, 5, 1, true),
        (2, 1, 0, 5, 1, true),
        (1, 2, 3, 2, 2, true),
        (2, 2, 2, 5, 1, true),
        (2, 2, 2, 5, 2, true),
    ] {
        let p = ValidatedProfile::new(nu, c, publog, degree, Some(anchor), tight).unwrap();
        let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
        let (spec, witness) = index::reference_fixture(&p);
        let ix = ValidatedIndex::certify(&srs, spec).unwrap();
        let public = &witness[..1 << publog];
        let (proof, metrics) = protocol::prove(&srs, &ix, public, &witness, &mut OsRng).unwrap();
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, false).is_ok());
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_ok());
        let expected = 37
            + 336
            + 32 * (p.round_scalar_count() + p.k() + p.k() + 1 + 12)
            + 48 * (p.k() + 7) * (p.l() + 1);
        assert_eq!(proof.len(), expected);
        if nu == 1 && c == 1 && tight {
            for offset in [
                0,
                5,
                metrics.offsets["witness"] + 10,
                metrics.offsets["trees"] + 20,
                metrics.offsets["helper"] + 15,
                metrics.offsets["rounds"] + 31,
                metrics.offsets["values"] + 31,
                metrics.offsets["openings"] + 15,
            ] {
                let mut bad = proof.clone();
                bad[offset] ^= 1;
                assert!(
                    protocol::verify(srs.vk(), &p, &ix, public, &bad, true).is_err(),
                    "accepted mutation at {offset}"
                );
            }
            assert!(
                protocol::verify(srs.vk(), &p, &ix, public, &proof[..proof.len() - 1], true)
                    .is_err()
            );
            let mut extra = proof.clone();
            extra.push(0);
            assert!(protocol::verify(srs.vk(), &p, &ix, public, &extra, true).is_err());
            let mut wrong_public = public.to_vec();
            wrong_public[0] += Fr::from(1);
            assert!(protocol::verify(srs.vk(), &p, &ix, &wrong_public, &proof, true).is_err());
            let mut noncanonical = proof.clone();
            let off = metrics.offsets["rounds"];
            noncanonical[off..off + 32].copy_from_slice(&Fr::MODULUS.to_bytes_be());
            assert!(protocol::verify(srs.vk(), &p, &ix, public, &noncanonical, true).is_err());
            let mut invalid_witness = witness.clone();
            invalid_witness[2] += Fr::from(1);
            assert!(protocol::prove(&srs, &ix, public, &invalid_witness, &mut OsRng).is_err());
        }
    }
}

#[test]
fn fixed_circuit_thirteen_selectors_distinct_witnesses() {
    let p = ValidatedProfile::new(1, 3, 1, 5, Some(3), true).unwrap();
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, w1) = index::fixed_thirteen_fixture(&p, &mut OsRng).unwrap();
    let (spec2, w2) = index::fixed_thirteen_fixture(&p, &mut OsRng).unwrap();
    assert_eq!(spec.selectors, spec2.selectors);
    assert_eq!(spec.wiring, spec2.wiring);
    assert_eq!(&w1[..2], &w2[..2]);
    assert_ne!(w1, w2);
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let ix2 = ValidatedIndex::certify(&srs, spec2).unwrap();
    assert_eq!(ix.digest(), ix2.digest());
    for w in [&w1, &w2] {
        let (proof, m) = protocol::prove(&srs, &ix, &w[..2], w, &mut OsRng).unwrap();
        assert_eq!(m.source_values, 8 + 13 + 12);
        assert_eq!(m.opening_count, 15);
        assert!(protocol::verify(srs.vk(), &p, &ix, &w[..2], &proof, true).is_ok());
        assert!(protocol::verify(srs.vk(), &p, &ix, &w[..2], &proof, false).is_ok());
    }
}

#[test]
fn index_rejects_bad_definition_and_wrong_key() {
    let p = ValidatedProfile::new(1, 1, 1, 5, None, true).unwrap();
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (mut spec, _) = index::reference_fixture(&p);
    spec.wiring[1] = spec.wiring[0];
    assert!(ValidatedIndex::certify(&srs, spec).is_err());
    let (mut spec, _) = index::reference_fixture(&p);
    spec.selectors.get_mut("q0").unwrap().push(Fr::from(7));
    assert!(ValidatedIndex::certify(&srs, spec).is_err());
    let (spec, witness) = index::reference_fixture(&p);
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let other = PublicSrs::setup(p, &mut OsRng).unwrap();
    assert!(protocol::prove(&other, &ix, &witness[..2], &witness, &mut OsRng).is_err());
}

#[test]
fn quotient_cache_preserves_entire_proof_and_transcript() {
    let p = ValidatedProfile::new(2, 3, 2, 5, Some(3), true).unwrap();
    let srs = PublicSrs::setup(p.clone(), &mut OsRng).unwrap();
    let (spec, witness) = index::fixed_thirteen_fixture(&p, &mut OsRng).unwrap();
    let index = ValidatedIndex::certify(&srs, spec).unwrap();
    let mut direct_rng = StdRng::seed_from_u64(90210);
    let mut cached_rng = StdRng::seed_from_u64(90210);
    let (direct, _) = protocol::prove_with_options(
        &srs,
        &index,
        &witness[..4],
        &witness,
        &mut direct_rng,
        protocol::ProverOptions {
            cache_openings: false,
        },
    )
    .unwrap();
    let (cached, metrics) =
        protocol::prove(&srs, &index, &witness[..4], &witness, &mut cached_rng).unwrap();
    assert_eq!(direct, cached);
    assert!(metrics.opening_cache["hits"] > 0);
    assert!(protocol::verify(srs.vk(), &p, &index, &witness[..4], &cached, true).is_ok());
    let stage_sum: f64 = metrics.stages.values().sum();
    assert!(stage_sum <= metrics.seconds && metrics.seconds - stage_sum < 0.01);
}
