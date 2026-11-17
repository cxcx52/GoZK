//! Private field sampling. Exact only under independent uniform input bytes.
//! OsRng is the deployed computational source; no information-theoretic claim
//! is made about an operating system RNG or a short seed expanded by a PRG.
use ark_bls12_381::Fr;
use rand::RngCore;

pub fn sample_fr(rng: &mut impl RngCore) -> crate::Result<Fr> {
    loop {
        let mut bytes = [0u8; 32];
        rng.try_fill_bytes(&mut bytes).map_err(|e| e.to_string())?;
        if let Ok(value) = crate::codec::scalar_from_bytes(&bytes) {
            return Ok(value);
        }
    }
}

pub fn sample_nonzero(rng: &mut impl RngCore) -> crate::Result<Fr> {
    loop {
        let value = sample_fr(rng)?;
        if value != Fr::from(0u64) {
            return Ok(value);
        }
    }
}
