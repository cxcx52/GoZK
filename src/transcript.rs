//! Byte-for-byte compatible with the independent Python transcript_v7.py.
//! Challenge reduction is biased; this is never a private-randomness sampler.
use crate::{
    codec::{pack_bytes, scalar_bytes},
    Result,
};
use ark_bls12_381::Fr;
use ark_ff::{BigInteger, PrimeField};
use num_bigint::{BigInt, BigUint, Sign};
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::collections::BTreeMap;

const PREFIX: &[u8] = b"HyperPlonk-repair-v7/transcript/v1\0";
const CONTEXT_PREFIX: &[u8] = b"HyperPlonk-repair-v7/context/v1\0";

// Unit-test-only legal challenge injection for completeness at zero leaves.
// It does not exist in release libraries or experiment binaries.
#[cfg(test)]
thread_local! { static TEST_OVERRIDE: std::cell::RefCell<Option<(String,Vec<Fr>)>>=const{std::cell::RefCell::new(None)}; }
#[cfg(test)]
pub(crate) struct TestOverrideGuard(Option<(String, Vec<Fr>)>);
#[cfg(test)]
pub(crate) fn test_override(label: &str, values: Vec<Fr>) -> TestOverrideGuard {
    TestOverrideGuard(TEST_OVERRIDE.with(|slot| slot.replace(Some((label.into(), values)))))
}
#[cfg(test)]
impl Drop for TestOverrideGuard {
    fn drop(&mut self) {
        TEST_OVERRIDE.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContextValue {
    Null,
    Bool(bool),
    Int(BigInt),
    Bytes(Vec<u8>),
    Text(String),
    List(Vec<ContextValue>),
    Map(BTreeMap<String, ContextValue>),
}
impl From<u64> for ContextValue {
    fn from(x: u64) -> Self {
        Self::Int(x.into())
    }
}
impl From<usize> for ContextValue {
    fn from(x: usize) -> Self {
        Self::Int(x.into())
    }
}
impl From<Fr> for ContextValue {
    fn from(x: Fr) -> Self {
        Self::Int(BigInt::from_bytes_be(Sign::Plus, &scalar_bytes(&x)))
    }
}

fn encode(value: &ContextValue, depth: usize, out: &mut Vec<u8>) -> Result<()> {
    if depth > 64 {
        return Err("context nesting exceeds 64 levels".into());
    }
    match value {
        ContextValue::Null => out.push(b'n'),
        ContextValue::Bool(x) => out.push(if *x { b't' } else { b'f' }),
        ContextValue::Int(x) => {
            let (sign, mut magnitude) = x.to_bytes_be();
            if magnitude.is_empty() {
                magnitude.push(0);
            }
            out.push(b'i');
            out.push(if sign == Sign::Minus { b'-' } else { b'+' });
            out.extend_from_slice(&pack_bytes(&magnitude));
        }
        ContextValue::Bytes(x) => {
            out.push(b'b');
            out.extend_from_slice(&pack_bytes(x));
        }
        ContextValue::Text(x) => {
            out.push(b's');
            out.extend_from_slice(&pack_bytes(x.as_bytes()));
        }
        ContextValue::List(xs) => {
            out.push(b'l');
            out.extend_from_slice(&(xs.len() as u64).to_be_bytes());
            for x in xs {
                encode(x, depth + 1, out)?;
            }
        }
        ContextValue::Map(xs) => {
            out.push(b'm');
            out.extend_from_slice(&(xs.len() as u64).to_be_bytes());
            // Rust String lexicographic order equals UTF-8 byte order.
            for (key, x) in xs {
                encode(&ContextValue::Text(key.clone()), depth + 1, out)?;
                encode(x, depth + 1, out)?;
            }
        }
    }
    Ok(())
}

pub fn canonical_context(context: &BTreeMap<String, ContextValue>) -> Result<Vec<u8>> {
    for key in [
        "E",
        "D",
        "anchor",
        "dimensions",
        "public_index_commitments",
        "public_input",
    ] {
        if !context.contains_key(key) {
            return Err(format!("missing context field: {key}"));
        }
    }
    let mut out = CONTEXT_PREFIX.to_vec();
    encode(&ContextValue::Map(context.clone()), 0, &mut out)?;
    Ok(out)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Domain {
    Field,
    Nonzero,
    Nonboolean,
}
impl Domain {
    fn label(self) -> &'static [u8] {
        match self {
            Self::Field => b"field",
            Self::Nonzero => b"nonzero",
            Self::Nonboolean => b"nonboolean",
        }
    }
    fn offset(self) -> u32 {
        match self {
            Self::Field => 0,
            Self::Nonzero => 1,
            Self::Nonboolean => 2,
        }
    }
}

#[derive(Clone)]
pub struct Transcript {
    history: Vec<u8>,
    sequence: u64,
    query_count: u64,
}
impl Transcript {
    pub fn new(context: &[u8], salt: [u8; 32]) -> Self {
        let mut history = PREFIX.to_vec();
        history.extend_from_slice(&pack_bytes(context));
        history.extend_from_slice(&salt);
        Self {
            history,
            sequence: 0,
            query_count: 0,
        }
    }
    pub fn query_count(&self) -> u64 {
        self.query_count
    }
    pub fn event_count(&self) -> u64 {
        self.sequence
    }
    fn label(label: &str) -> Result<Vec<u8>> {
        if label.is_empty() {
            return Err("stage label must be nonempty".into());
        }
        Ok(pack_bytes(label.as_bytes()))
    }
    pub fn absorb(&mut self, label: &str, payload: &[u8]) -> Result<()> {
        let label = Self::label(label)?;
        let next = self.sequence.checked_add(1).ok_or("event count overflow")?;
        self.history.push(b'A');
        self.history.extend_from_slice(&self.sequence.to_be_bytes());
        self.history.extend_from_slice(&label);
        self.history.extend_from_slice(&pack_bytes(payload));
        self.sequence = next;
        Ok(())
    }
    pub fn challenge(&mut self, label: &str, count: usize, domain: Domain) -> Result<Vec<Fr>> {
        if count == 0 || count >= (1u64 << 32) as usize {
            return Err("invalid challenge count".into());
        }
        self.challenge_mixed(label, &vec![domain; count])
    }
    pub fn challenge_mixed(&mut self, label: &str, domains: &[Domain]) -> Result<Vec<Fr>> {
        if domains.is_empty() || domains.len() as u64 >= 1u64 << 32 {
            return Err("invalid challenge count".into());
        }
        let encoded_label = Self::label(label)?;
        let next_sequence = self.sequence.checked_add(1).ok_or("event count overflow")?;
        let next_query = self
            .query_count
            .checked_add(1)
            .ok_or("query count overflow")?;
        let mut request = vec![b'C'];
        request.extend_from_slice(&self.sequence.to_be_bytes());
        request.extend_from_slice(&encoded_label);
        request.extend_from_slice(&(domains.len() as u64).to_be_bytes());
        for domain in domains {
            request.extend_from_slice(&pack_bytes(domain.label()));
        }
        let mut hasher = Shake256::default();
        hasher.update(PREFIX);
        hasher.update(b"challenge\0");
        hasher.update(&(self.history.len() as u64).to_be_bytes());
        hasher.update(&self.history);
        hasher.update(&request);
        let mut xof = hasher.finalize_xof();
        let modulus = BigUint::from_bytes_be(&Fr::MODULUS.to_bytes_be());
        let mut result = Vec::with_capacity(domains.len());
        for domain in domains {
            let mut raw = [0u8; 64];
            xof.read(&mut raw);
            let offset = domain.offset();
            let integer = BigUint::from_bytes_be(&raw) % (&modulus - offset) + offset;
            result.push(Fr::from_be_bytes_mod_order(&integer.to_bytes_be()));
        }
        #[cfg(test)]
        TEST_OVERRIDE.with(|slot| -> Result<()> {
            if let Some((target, values)) = &*slot.borrow() {
                if target == label {
                    if values.len() != domains.len()
                        || values.iter().zip(domains).any(|(v, d)| match d {
                            Domain::Field => false,
                            Domain::Nonzero => *v == Fr::from(0u64),
                            Domain::Nonboolean => *v == Fr::from(0u64) || *v == Fr::from(1u64),
                        })
                    {
                        return Err("test override outside challenge domain".into());
                    }
                    result = values.clone();
                }
            }
            Ok(())
        })?;
        self.history.extend_from_slice(&request);
        self.history.push(b'R');
        for value in &result {
            self.history.extend_from_slice(&scalar_bytes(value));
        }
        self.sequence = next_sequence;
        self.query_count = next_query;
        Ok(result)
    }
}
