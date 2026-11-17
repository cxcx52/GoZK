use ark_bls12_381::Fr;
use hyperplonk_repair::{
    index::{self, ValidatedIndex},
    multi,
    pcs::PublicSrs,
    profile::ValidatedProfile,
    protocol,
};
use rand::{rngs::StdRng, SeedableRng};

#[test]
fn native_sumchecks_preserve_source_geometry_and_have_separate_helper_claims() {
    let p = ValidatedProfile::new(2, 3, 1, 5, Some(3), false).unwrap();
    let mut rng = StdRng::seed_from_u64(738522);
    let srs = PublicSrs::setup(p.clone(), &mut rng).unwrap();
    let (spec, w) = index::fixed_thirteen_fixture(&p, &mut rng).unwrap();
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let public = &w[..2];
    let ledger = multi::ledger(&p, &ix).unwrap();
    let checks = ledger["checks"].as_array().unwrap();
    assert_eq!(checks.len(), 7);
    let mut independent_count = 0;
    for c in checks {
        let e = c["honest_caps"].as_array().unwrap();
        let d = c["soundness_caps"].as_array().unwrap();
        let off = c["suffix_offset"].as_u64().unwrap() as usize;
        assert_eq!(e.len() + off, p.l());
        assert_eq!(
            c["first_round_free"].as_u64(),
            Some(e[0].as_u64().unwrap() - 1)
        );
        let count = e.iter().map(|v| v.as_u64().unwrap()).sum::<u64>() - 1;
        assert_eq!(count, c["helper_coefficients"].as_u64().unwrap());
        for (a, (wire, actual)) in e.iter().zip(d).enumerate() {
            assert!(wire.as_u64().unwrap() <= actual.as_u64().unwrap());
            assert!(actual.as_u64().unwrap() >= p.e()[off + a] as u64);
        }
        independent_count += count as usize;
    }
    assert_eq!(ledger["helper_opening_buckets"].as_u64(), Some(3));
    let (proof, m) =
        multi::prove_with_options(&srs, &ix, public, &w, &mut rng, Default::default()).unwrap();
    let (global, g) = protocol::prove(&srs, &ix, public, &w, &mut rng).unwrap();
    assert_eq!(m.round_scalars, independent_count);
    assert_eq!(m.source_values, g.source_values);
    assert_eq!(m.opening_count, g.opening_count + 2);
    assert_eq!(m.fold_pairs, g.fold_pairs);
    assert_eq!(
        m.proof_bytes,
        37 + 288
            + 48 * 7
            + 32 * (m.round_scalars + m.source_values)
            + 48 * m.opening_count * (p.l() + 1)
    );
    assert_eq!(proof.len(), m.proof_bytes);
    for agg in [false, true] {
        let verified = multi::verify(srs.vk(), &p, &ix, public, &proof, agg).unwrap();
        assert_eq!(m.round_scalars, verified.round_scalars);
        assert_eq!(m.opening_count, verified.opening_count);
    }
    assert!(protocol::verify(srs.vk(), &p, &ix, public, &proof, true).is_err());
    assert!(multi::verify(srs.vk(), &p, &ix, public, &global, true).is_err());

    // Swap two valid helper commitments; subgroup checks alone cannot detect this.
    let mut swapped = proof.clone();
    let off = m.offsets["helper"];
    let (first, rest) = swapped[off..off + 96].split_at_mut(48);
    first.swap_with_slice(rest);
    assert!(multi::verify(srs.vk(), &p, &ix, public, &swapped, true).is_err());
    for field in ["rounds", "values"] {
        let mut other = proof.clone();
        let pos = m.offsets[field] + 31;
        other[pos] ^= 1;
        assert!(multi::verify(srs.vk(), &p, &ix, public, &other, false).is_err());
    }
    assert!(multi::verify(srs.vk(), &p, &ix, public, &proof[..proof.len() - 1], true).is_err());
    let mut extra = proof.clone();
    extra.push(0);
    assert!(multi::verify(srs.vk(), &p, &ix, public, &extra, true).is_err());
}

#[test]
fn native_sumchecks_handle_a_virtual_slice_and_reject_an_invalid_witness() {
    let p = ValidatedProfile::from_flags(2, 1, 1, 3, Some(1), 2).unwrap();
    let mut rng = StdRng::seed_from_u64(203991);
    let srs = PublicSrs::setup(p.clone(), &mut rng).unwrap();
    let (spec, w) = index::reference_fixture(&p);
    let ix = ValidatedIndex::certify(&srs, spec).unwrap();
    let public = w[..2].to_vec();
    let mut stored = w.clone();
    stored[0] += Fr::from(11);
    let mut a = StdRng::seed_from_u64(14114);
    let mut b = a.clone();
    let (bytes, sm) = multi::prove_with_options(
        &srs,
        &ix,
        &public,
        &stored,
        &mut a,
        protocol::ProverOptions {
            cache_openings: false,
        },
    )
    .unwrap();
    let (cached, _) = multi::prove_with_options(
        &srs,
        &ix,
        &public,
        &stored,
        &mut b,
        protocol::ProverOptions {
            cache_openings: true,
        },
    )
    .unwrap();
    assert_eq!(bytes, cached);
    assert_eq!(
        multi::ledger(&p, &ix).unwrap()["helper_count"].as_u64(),
        Some(6)
    );
    assert_eq!(sm.proof_bytes, bytes.len());
    multi::verify(srs.vk(), &p, &ix, &public, &bytes, true).unwrap();
    let mut wrong_public = public.clone();
    wrong_public[0] += Fr::from(1);
    assert!(multi::verify(srs.vk(), &p, &ix, &wrong_public, &bytes, true).is_err());
    stored[2] += Fr::from(7);
    assert!(
        multi::prove_with_options(&srs, &ix, &public, &stored, &mut a, Default::default()).is_err()
    );
}
