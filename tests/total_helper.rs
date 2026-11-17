use ark_bls12_381::Fr;
use ark_ff::Zero;
use hyperplonk_repair::{
    codec::{scalar_bytes, scalar_from_bytes},
    index::{self, ValidatedIndex},
    pcs::PublicSrs,
    profile::ValidatedProfile,
    protocol::{self, ProverOptions},
};
use rand::{rngs::StdRng, RngCore, SeedableRng};

#[derive(Default)]
struct FieldTape(u64);

impl RngCore for FieldTape {
    fn next_u32(&mut self) -> u32 {
        unreachable!()
    }

    fn next_u64(&mut self) -> u64 {
        unreachable!()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0 += 1;
        dest.copy_from_slice(&scalar_bytes(&Fr::from(self.0)));
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

#[test]
fn total_helper_consumes_one_more_field_and_authenticates_the_extra_round_coordinate() {
    let p = ValidatedProfile::new(1, 3, 1, 5, Some(3), false).unwrap();
    let mut setup_rng = StdRng::seed_from_u64(3177);
    let srs = PublicSrs::setup(p.clone(), &mut setup_rng).unwrap();
    let (spec, witness) = index::fixed_thirteen_fixture(&p, &mut setup_rng).unwrap();
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let public = &witness[..2];
    let mut half_tape = FieldTape::default();
    let mut total_tape = FieldTape::default();
    let (half, base) = protocol::prove(&srs, &ix, public, &witness, &mut half_tape).unwrap();
    let (total, metrics) = protocol::prove_total(
        &srs,
        &ix,
        public,
        &witness,
        &mut total_tape,
        ProverOptions::default(),
    )
    .unwrap();
    assert_eq!(&total[..5], protocol::TOTAL_HEADER);
    assert_eq!(&half[..5], protocol::HEADER);
    assert_ne!(
        protocol::context_bytes(&p, &ix, public).unwrap(),
        protocol::total_context_bytes(&p, &ix, public).unwrap()
    );
    assert_eq!(total_tape.0, half_tape.0 + 1);
    assert_eq!(total.len(), half.len() + 32);
    assert_eq!(metrics.proof_bytes, total.len());
    assert_eq!(metrics.round_scalars, base.round_scalars + 1);
    assert_eq!(metrics.round_scalars, p.e().iter().sum::<usize>());
    assert_eq!(metrics.hash_packets, base.hash_packets);
    assert_eq!(metrics.source_values, base.source_values);
    assert_eq!(metrics.opening_count, base.opening_count);
    assert_eq!(metrics.fold_pairs, base.fold_pairs);
    assert_eq!(metrics.sample_points, base.sample_points);
    for field in ["witness", "trees", "helper", "rounds"] {
        assert_eq!(metrics.offsets[field], base.offsets[field]);
    }
    for field in ["values", "openings"] {
        assert_eq!(metrics.offsets[field], base.offsets[field] + 32);
    }
    let start = metrics.offsets["rounds"];
    let first = &total[start..start + 32 * p.e()[0]];
    let slope_sum: Fr = first
        .chunks_exact(32)
        .map(|s| scalar_from_bytes(s).unwrap())
        .sum();
    // h(1)-h(0) = rho * 2^(L-1) * eta, with eta nonzero on this tape.
    assert!(!slope_sum.is_zero());
    let mut changed = total.clone();
    let slope = scalar_from_bytes(&first[..32]).unwrap();
    changed[start..start + 32].copy_from_slice(&scalar_bytes(&(slope + Fr::from(1))));
    let mut swapped = total.clone();
    swapped[..5].copy_from_slice(protocol::HEADER);
    let mut half_as_total = half.clone();
    half_as_total[..5].copy_from_slice(protocol::TOTAL_HEADER);
    let high_end = start + (p.e()[0] - 1) * 32;
    let half_linear: Fr = -half[start..high_end]
        .chunks_exact(32)
        .map(|s| scalar_from_bytes(s).unwrap())
        .sum::<Fr>();
    half_as_total.splice(start..start, scalar_bytes(&half_linear));
    let mut trailing = total.clone();
    trailing.push(0);
    let mut wrong_public = public.to_vec();
    wrong_public[0] += Fr::from(1);
    for aggregate in [false, true] {
        let checked = protocol::verify_total(srs.vk(), &p, &ix, public, &total, aggregate).unwrap();
        assert_eq!(checked.round_scalars, metrics.round_scalars);
        assert_eq!(checked.source_values, metrics.source_values);
        assert_eq!(checked.opening_count, metrics.opening_count);
        protocol::verify(srs.vk(), &p, &ix, public, &half, aggregate).unwrap();
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &total, aggregate).is_err());
        assert!(protocol::verify(srs.vk(), &p, &ix, public, &swapped, aggregate).is_err());
        for malformed in [
            &half[..],
            &half_as_total,
            &changed,
            &trailing,
            &total[..total.len() - 1],
        ] {
            assert!(
                protocol::verify_total(srs.vk(), &p, &ix, public, malformed, aggregate).is_err()
            );
        }
        assert!(
            protocol::verify_total(srs.vk(), &p, &ix, &wrong_public, &total, aggregate).is_err()
        );
    }
    let (direct, _) = protocol::prove_total(
        &srs,
        &ix,
        public,
        &witness,
        &mut FieldTape::default(),
        ProverOptions {
            cache_openings: false,
        },
    )
    .unwrap();
    assert_eq!(direct, total);
    let mut invalid = witness;
    invalid[0] += Fr::from(1);
    let changed_public = invalid[..2].to_vec();
    assert!(protocol::prove_total(
        &srs,
        &ix,
        &changed_public,
        &invalid,
        &mut FieldTape::default(),
        ProverOptions::default(),
    )
    .is_err());
}
