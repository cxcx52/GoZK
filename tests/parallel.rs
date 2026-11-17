#![cfg(feature = "parallel")]
use ark_bls12_381::Fr;
use hyperplonk_repair::{
    index::{self, ValidatedIndex},
    parallel,
    pcs::PublicSrs,
    profile::ValidatedProfile,
    protocol,
};
use rand::{rngs::StdRng, SeedableRng};

#[test]
fn parallel_fold_and_sum_preserve_field_arithmetic() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();
    let mut values = (0..16384)
        .map(|i| Fr::from((i * i + 3) as u64))
        .collect::<Vec<_>>();
    let original = values.clone();
    let r = Fr::from(19);
    let mut diff = vec![Fr::from(0); 8192];
    pool.install(|| parallel::fold_pairs(&mut values, r, Some(&mut diff)));
    for i in 0..8192 {
        assert_eq!(diff[i], original[i + 8192] - original[i]);
        assert_eq!(values[i], original[i] + r * diff[i]);
    }
    let expected: Fr = original.iter().copied().sum();
    assert_eq!(
        pool.install(|| parallel::sum_indices(original.len(), |i| original[i])),
        expected
    );
}

#[test]
fn full_proof_identical_with_one_and_four_threads() {
    let one = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    let four = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();
    let p = ValidatedProfile::new(7, 3, 7, 5, Some(3), true).unwrap();
    let mut setup_rng = StdRng::seed_from_u64(97);
    let srs = one
        .install(|| PublicSrs::setup(p.clone(), &mut setup_rng))
        .unwrap();
    let (spec, witness) = index::fixed_thirteen_fixture(&p, &mut setup_rng).unwrap();
    let index = one.install(|| ValidatedIndex::certify(&srs, spec)).unwrap();
    let (mut r1, mut r4) = (StdRng::seed_from_u64(123), StdRng::seed_from_u64(123));
    let a = one
        .install(|| protocol::prove(&srs, &index, &witness[..128], &witness, &mut r1))
        .unwrap()
        .0;
    let b = four
        .install(|| protocol::prove(&srs, &index, &witness[..128], &witness, &mut r4))
        .unwrap()
        .0;
    assert_eq!(a, b);
    assert!(four
        .install(|| protocol::verify(srs.vk(), &p, &index, &witness[..128], &b, true))
        .is_ok());
}
