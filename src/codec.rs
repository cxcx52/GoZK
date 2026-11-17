//! Canonical Python-compatible wire codec, deliberately independent of ark's
//! native serialization. Every decoded point is checked before it is returned.
use crate::Result;
use ark_bls12_381::{Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, Field, PrimeField, Zero};

fn field_bytes<F: PrimeField, const N: usize>(value: &F) -> [u8; N] {
    let bytes = value.into_bigint().to_bytes_be();
    let mut output = [0u8; N];
    output[N - bytes.len()..].copy_from_slice(&bytes);
    output
}

pub fn scalar_bytes(value: &Fr) -> [u8; 32] {
    field_bytes(value)
}

pub fn scalar_from_bytes(bytes: &[u8]) -> Result<Fr> {
    if bytes.len() != 32 {
        return Err("scalar must have 32 bytes".into());
    }
    let value = Fr::from_be_bytes_mod_order(bytes);
    if scalar_bytes(&value) != bytes {
        return Err("noncanonical scalar".into());
    }
    Ok(value)
}

fn fq_from_bytes(bytes: &[u8]) -> Result<Fq> {
    if bytes.len() != 48 {
        return Err("base-field element must have 48 bytes".into());
    }
    let value = Fq::from_be_bytes_mod_order(bytes);
    if field_bytes::<_, 48>(&value) != bytes {
        return Err("noncanonical base-field element".into());
    }
    Ok(value)
}

fn high(value: &Fq) -> bool {
    value.into_bigint() > (-*value).into_bigint()
}
fn high2(value: &Fq2) -> bool {
    high(if value.c1.is_zero() {
        &value.c0
    } else {
        &value.c1
    })
}

pub fn g1_bytes(point: &G1Affine) -> [u8; 48] {
    if point.is_zero() {
        let mut out = [0u8; 48];
        out[0] = 0xc0;
        return out;
    }
    let mut out = field_bytes::<_, 48>(&point.x);
    out[0] |= 0x80 | if high(&point.y) { 0x20 } else { 0 };
    out
}

pub fn g2_bytes(point: &G2Affine) -> [u8; 96] {
    let mut out = [0u8; 96];
    if point.is_zero() {
        out[0] = 0xc0;
        return out;
    }
    out[..48].copy_from_slice(&field_bytes::<_, 48>(&point.x.c1));
    out[48..].copy_from_slice(&field_bytes::<_, 48>(&point.x.c0));
    out[0] |= 0x80 | if high2(&point.y) { 0x20 } else { 0 };
    out
}

fn flags(bytes: &[u8], width: usize) -> Result<(bool, bool, [u8; 48])> {
    if bytes.len() != width {
        return Err(format!("point must have {width} bytes"));
    }
    if bytes[0] & 0x80 == 0 {
        return Err("compression flag missing".into());
    }
    let infinity = bytes[0] & 0x40 != 0;
    let sign = bytes[0] & 0x20 != 0;
    let mut first = [0u8; 48];
    first.copy_from_slice(&bytes[..48]);
    first[0] &= 0x1f;
    let zero_coordinates = first.iter().all(|x| *x == 0) && bytes[48..].iter().all(|x| *x == 0);
    if infinity != zero_coordinates || (infinity && sign) {
        return Err("noncanonical infinity flags".into());
    }
    Ok((infinity, sign, first))
}

pub fn g1_from_bytes(bytes: &[u8]) -> Result<G1Affine> {
    let (infinity, sign, first) = flags(bytes, 48)?;
    if infinity {
        return Ok(G1Affine::identity());
    }
    let x = fq_from_bytes(&first)?;
    let mut y = (x.square() * x + Fq::from(4u64))
        .sqrt()
        .ok_or("point is not on G1")?;
    if high(&y) != sign {
        y = -y;
    }
    // Construct an intermediate value only; it never escapes these checks.
    let point = G1Affine::new_unchecked(x, y);
    if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve() {
        return Err("G1 curve/subgroup check failed".into());
    }
    if g1_bytes(&point) != bytes {
        return Err("noncanonical G1 encoding".into());
    }
    Ok(point)
}

pub fn g2_from_bytes(bytes: &[u8]) -> Result<G2Affine> {
    let (infinity, sign, first) = flags(bytes, 96)?;
    if infinity {
        return Ok(G2Affine::identity());
    }
    let x = Fq2::new(fq_from_bytes(&bytes[48..])?, fq_from_bytes(&first)?);
    let mut y = (x.square() * x + Fq2::new(Fq::from(4u64), Fq::from(4u64)))
        .sqrt()
        .ok_or("point is not on G2")?;
    if high2(&y) != sign {
        y = -y;
    }
    let point = G2Affine::new_unchecked(x, y);
    if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve() {
        return Err("G2 curve/subgroup check failed".into());
    }
    if g2_bytes(&point) != bytes {
        return Err("noncanonical G2 encoding".into());
    }
    Ok(point)
}

pub fn pack_bytes(bytes: &[u8]) -> Vec<u8> {
    let mut output = Vec::with_capacity(8 + bytes.len());
    output.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    output.extend_from_slice(bytes);
    output
}

pub struct Reader<'a> {
    data: &'a [u8],
    position: usize,
}
impl<'a> Reader<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self { data, position: 0 }
    }
    pub fn position(&self) -> usize {
        self.position
    }
    pub fn remaining(&self) -> usize {
        self.data.len() - self.position
    }
    pub fn bytes(&mut self, length: usize) -> Result<&'a [u8]> {
        if length > self.remaining() {
            return Err("truncated encoding".into());
        }
        let start = self.position;
        self.position += length;
        Ok(&self.data[start..self.position])
    }
    pub fn framed_bytes(&mut self) -> Result<&'a [u8]> {
        let length = u64::from_be_bytes(self.bytes(8)?.try_into().unwrap());
        let length = usize::try_from(length).map_err(|_| "length overflows address space")?;
        self.bytes(length)
    }
    pub fn scalar(&mut self) -> Result<Fr> {
        scalar_from_bytes(self.bytes(32)?)
    }
    pub fn g1(&mut self) -> Result<G1Affine> {
        g1_from_bytes(self.bytes(48)?)
    }
    pub fn g2(&mut self) -> Result<G2Affine> {
        g2_from_bytes(self.bytes(96)?)
    }
    pub fn finish(&self) -> Result<()> {
        if self.remaining() != 0 {
            Err("trailing bytes".into())
        } else {
            Ok(())
        }
    }
}
