//! General extension-field trace masks for the historical repair baseline.
//! The field is certified by Rabin's irreducibility criterion, not assumed from
//! its dimension. Dense witness tables remain outside this small algebra layer.
use crate::{codec::scalar_bytes, random::sample_fr, Result};
use ark_bls12_381::Fr;
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use num_bigint::BigUint;
use rand::RngCore;
use std::sync::Arc;

type Poly = Vec<Fr>;
pub type ExtensionElement = Vec<Fr>;

fn trim(p: &mut Poly) {
    while p.last().is_some_and(Zero::is_zero) {
        p.pop();
    }
}
fn subtract(a: &[Fr], b: &[Fr]) -> Poly {
    let mut p = a.to_vec();
    p.resize(a.len().max(b.len()), Fr::zero());
    for (x, y) in p.iter_mut().zip(b) {
        *x -= y;
    }
    trim(&mut p);
    p
}
fn remainder(mut a: Poly, modulus: &[Fr]) -> Poly {
    let lead_inv = modulus.last().unwrap().inverse().unwrap();
    trim(&mut a);
    while a.len() >= modulus.len() {
        let shift = a.len() - modulus.len();
        let c = *a.last().unwrap() * lead_inv;
        for (j, v) in modulus.iter().enumerate() {
            a[shift + j] -= c * v;
        }
        trim(&mut a);
    }
    a
}
fn multiply_mod(a: &[Fr], b: &[Fr], modulus: &[Fr]) -> Poly {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut p = vec![Fr::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        if !x.is_zero() {
            for (j, y) in b.iter().enumerate() {
                p[i + j] += *x * y;
            }
        }
    }
    remainder(p, modulus)
}
fn power_mod(a: &[Fr], exponent: &[u64], modulus: &[Fr]) -> Poly {
    let mut value = vec![Fr::one()];
    for bit in ark_ff::BitIteratorBE::without_leading_zeros(exponent) {
        value = multiply_mod(&value, &value, modulus);
        if bit {
            value = multiply_mod(&value, a, modulus);
        }
    }
    value
}
fn gcd(mut a: Poly, mut b: Poly) -> Poly {
    trim(&mut a);
    trim(&mut b);
    while !b.is_empty() {
        let r = remainder(a, &b);
        a = b;
        b = r;
    }
    if let Some(c) = a.last().and_then(|v| v.inverse()) {
        for v in &mut a {
            *v *= c;
        }
    }
    a
}
fn prime_divisors(mut n: usize) -> Vec<usize> {
    let mut out = vec![];
    let mut d = 2;
    while d * d <= n {
        if n % d == 0 {
            out.push(d);
            while n % d == 0 {
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        out.push(n);
    }
    out
}

/// Rabin certificate conditions: X^(q^ell)=X mod f and
/// gcd(f,X^(q^(ell/p))-X)=1 for every prime p dividing ell.
pub fn is_irreducible(modulus: &[Fr]) -> bool {
    if modulus.len() < 2 || modulus.last() != Some(&Fr::one()) {
        return false;
    }
    let degree = modulus.len() - 1;
    if degree == 1 {
        return true;
    }
    if modulus[0].is_zero() {
        return false;
    }
    let checkpoints = prime_divisors(degree)
        .into_iter()
        .map(|p| degree / p)
        .collect::<Vec<_>>();
    let x = vec![Fr::zero(), Fr::one()];
    let mut current = x.clone();
    for i in 1..=degree {
        current = power_mod(&current, Fr::MODULUS.as_ref(), modulus);
        if checkpoints.contains(&i) && gcd(modulus.to_vec(), subtract(&current, &x)).len() != 1 {
            return false;
        }
    }
    subtract(&current, &x).is_empty()
}

#[derive(Clone, Debug)]
pub struct ExtensionField {
    degree: usize,
    modulus: Poly,
    trace_basis: Vec<Fr>,
    tested_candidates: usize,
}
impl ExtensionField {
    /// Deterministic search. Every accepted candidate is independently checked;
    /// a bounded-search failure is an explicit error, never a false certificate.
    pub fn new(degree: usize) -> Result<Self> {
        if !(1..=25).contains(&degree) {
            return Err("trace baseline extension degree must be 1..25".into());
        }
        if degree == 1 {
            return Self::from_modulus(vec![Fr::zero(), Fr::one()]);
        }
        let mut tested = 0;
        // Binomials preserve compatibility with the old ell<=4 reference when
        // available; then try sparse polynomials of increasing coefficients.
        let order = BigUint::from_bytes_be(&Fr::MODULUS.to_bytes_be()) - BigUint::from(1u64);
        // A binomial cannot be irreducible unless every prime factor of ell
        // divides q-1. Avoid hundreds of provably impossible Rabin candidates.
        let binomial_possible = prime_divisors(degree)
            .iter()
            .all(|p| &order % BigUint::from(*p) == BigUint::from(0u64))
            && (degree % 4 != 0 || &order % BigUint::from(4u64) == BigUint::from(0u64));
        for family in if binomial_possible { 0 } else { 1 }..2 {
            for constant in 2..=257u64 {
                let mut modulus = vec![Fr::zero(); degree + 1];
                modulus[degree] = Fr::one();
                modulus[0] = -Fr::from(constant);
                if family == 1 {
                    modulus[1] = Fr::one();
                }
                tested += 1;
                if is_irreducible(&modulus) {
                    let mut f = Self::from_certified(modulus);
                    f.tested_candidates = tested;
                    return Ok(f);
                }
            }
        }
        Err(format!(
            "no irreducible degree-{degree} polynomial in bounded sparse search"
        ))
    }
    pub fn from_modulus(modulus: Poly) -> Result<Self> {
        if modulus.len() < 2 || modulus.len() > 26 || !is_irreducible(&modulus) {
            return Err("invalid or reducible extension modulus".into());
        }
        Ok(Self::from_certified(modulus))
    }
    fn from_certified(modulus: Poly) -> Self {
        let degree = modulus.len() - 1;
        let mut powers = vec![vec![Fr::one()]];
        for _ in 1..=(2 * degree - 2) {
            powers.push(multiply_mod(
                powers.last().unwrap(),
                &[Fr::zero(), Fr::one()],
                &modulus,
            ));
        }
        // Trace of the multiplication matrix. Unlike an unsupported binomial
        // shortcut, this is valid for every certified polynomial basis.
        let trace_basis = (0..degree)
            .map(|i| {
                (0..degree)
                    .map(|j| powers[i + j].get(j).copied().unwrap_or_default())
                    .sum()
            })
            .collect();
        Self {
            degree,
            modulus,
            trace_basis,
            tested_candidates: 1,
        }
    }
    pub fn degree(&self) -> usize {
        self.degree
    }
    pub fn modulus(&self) -> &[Fr] {
        &self.modulus
    }
    pub fn tested_candidates(&self) -> usize {
        self.tested_candidates
    }
    pub fn zero(&self) -> ExtensionElement {
        vec![Fr::zero(); self.degree]
    }
    pub fn one(&self) -> ExtensionElement {
        let mut p = self.zero();
        p[0] = Fr::one();
        p
    }
    pub fn basis(&self, axis: usize) -> Result<ExtensionElement> {
        if axis >= self.degree {
            return Err("basis axis outside extension".into());
        }
        let mut p = self.zero();
        p[axis] = Fr::one();
        Ok(p)
    }
    fn checked(&self, a: &[Fr]) -> Result<()> {
        if a.len() != self.degree {
            Err("extension element dimension".into())
        } else {
            Ok(())
        }
    }
    pub fn add(&self, a: &[Fr], b: &[Fr]) -> Result<ExtensionElement> {
        self.checked(a)?;
        self.checked(b)?;
        Ok(a.iter().zip(b).map(|(x, y)| *x + y).collect())
    }
    pub fn scale(&self, a: &[Fr], c: Fr) -> Result<ExtensionElement> {
        self.checked(a)?;
        Ok(a.iter().map(|x| *x * c).collect())
    }
    pub fn mul(&self, a: &[Fr], b: &[Fr]) -> Result<ExtensionElement> {
        self.checked(a)?;
        self.checked(b)?;
        let mut p = multiply_mod(a, b, &self.modulus);
        p.resize(self.degree, Fr::zero());
        Ok(p)
    }
    pub fn pow(&self, a: &[Fr], exponent: &[u64]) -> Result<ExtensionElement> {
        self.checked(a)?;
        let mut p = power_mod(a, exponent, &self.modulus);
        p.resize(self.degree, Fr::zero());
        Ok(p)
    }
    pub fn trace(&self, a: &[Fr]) -> Result<Fr> {
        self.checked(a)?;
        Ok(a.iter().zip(&self.trace_basis).map(|(a, t)| *a * t).sum())
    }
    pub fn trace_basis(&self) -> &[Fr] {
        &self.trace_basis
    }
    pub fn certificate(&self) -> serde_json::Value {
        serde_json::json!({"degree":self.degree,"field":"BLS12-381 Fr","modulus_coefficients_be":self.modulus.iter().map(|x|hex::encode(scalar_bytes(x))).collect::<Vec<_>>(),"trace_basis_be":self.trace_basis.iter().map(|x|hex::encode(scalar_bytes(x))).collect::<Vec<_>>(),"criterion":"Rabin: Frobenius closure and prime-divisor gcds","prime_divisors":prime_divisors(self.degree),"tested_candidates":self.tested_candidates})
    }
}

fn add_scaled(target: &mut [Fr], source: &[Fr], scale: Fr) {
    for (a, b) in target.iter_mut().zip(source) {
        *a += *b * scale;
    }
}
fn evaluate_extension_polynomial(
    field: &ExtensionField,
    coefficients: &[ExtensionElement],
    point: &[Fr],
) -> Result<ExtensionElement> {
    let mut value = field.zero();
    for c in coefficients.iter().rev() {
        value = field.mul(&value, point)?;
        add_scaled(&mut value, c, Fr::one());
    }
    Ok(value)
}

#[derive(Clone, Debug)]
pub struct TraceMask {
    field: Arc<ExtensionField>,
    coefficients: Vec<ExtensionElement>,
}
impl TraceMask {
    pub fn from_coefficients(
        field: Arc<ExtensionField>,
        coefficients: Vec<ExtensionElement>,
    ) -> Result<Self> {
        if coefficients.is_empty()
            || coefficients.len() > 4096
            || coefficients.iter().any(|c| c.len() != field.degree())
        {
            return Err("trace mask budget or coefficient shape".into());
        }
        Ok(Self {
            field,
            coefficients,
        })
    }
    pub fn sample(
        field: Arc<ExtensionField>,
        budget: usize,
        rng: &mut impl RngCore,
    ) -> Result<Self> {
        if !(1..=4096).contains(&budget) {
            return Err("trace mask budget".into());
        }
        let coefficients = (0..budget)
            .map(|_| (0..field.degree()).map(|_| sample_fr(rng)).collect())
            .collect::<Result<Vec<_>>>()?;
        Self::from_coefficients(field, coefficients)
    }
    pub fn field(&self) -> &ExtensionField {
        &self.field
    }
    pub fn coefficients(&self) -> &[ExtensionElement] {
        &self.coefficients
    }
    pub fn budget(&self) -> usize {
        self.coefficients.len()
    }
    pub fn evaluate(&self, point: &[Fr]) -> Result<Fr> {
        self.field.checked(point)?;
        let h: Vec<_> = point.iter().map(|x| *x * (Fr::one() - x)).collect();
        self.field.trace(&self.field.mul(
            &h,
            &evaluate_extension_polynomial(&self.field, &self.coefficients, point)?,
        )?)
    }
    /// Coefficients of the mask with one coordinate replaced by an indeterminate.
    /// This is a degree-(T+1) small polynomial, never a full tensor expansion.
    pub fn line_coefficients(&self, point: &[Fr], axis: usize) -> Result<Vec<Fr>> {
        self.field.checked(point)?;
        if axis >= self.field.degree() {
            return Err("line axis".into());
        }
        let mut base = point.to_vec();
        base[axis] = Fr::zero();
        let e = self.field.basis(axis)?;
        let mut poly: Vec<ExtensionElement> = vec![];
        for coefficient in self.coefficients.iter().rev() {
            let mut next = vec![self.field.zero(); poly.len() + 1];
            for (j, value) in poly.iter().enumerate() {
                add_scaled(&mut next[j], &self.field.mul(value, &base)?, Fr::one());
                add_scaled(&mut next[j + 1], &self.field.mul(value, &e)?, Fr::one());
            }
            add_scaled(&mut next[0], coefficient, Fr::one());
            poly = next;
        }
        let h0 = base
            .iter()
            .map(|x| *x * (Fr::one() - x))
            .collect::<Vec<_>>();
        let mut result = vec![self.field.zero(); poly.len() + 2];
        for (j, value) in poly.iter().enumerate() {
            add_scaled(&mut result[j], &self.field.mul(value, &h0)?, Fr::one());
            let v = self.field.mul(value, &e)?;
            add_scaled(&mut result[j + 1], &v, Fr::one());
            add_scaled(&mut result[j + 2], &v, -Fr::one());
        }
        result.iter().map(|v| self.field.trace(v)).collect()
    }
    /// Noncanonical but explicit quotient decomposition in the historical U:
    /// Tr(pure(L(X))) + X_i Tr(times_axis(L(X))). The PCS equation requires
    /// a valid decomposition, not prefix-canonical quotients specifically.
    pub fn quotients(&self, point: &[Fr]) -> Result<Vec<TraceQuotient>> {
        self.field.checked(point)?;
        let h = point
            .iter()
            .map(|x| *x * (Fr::one() - x))
            .collect::<Vec<_>>();
        let mut powers = vec![self.field.one()];
        for k in 1..self.budget() {
            powers.push(self.field.mul(&powers[k - 1], point)?);
        }
        let mut out = vec![];
        for (i, z) in point.iter().enumerate() {
            let e = self.field.basis(i)?;
            let mut pure = vec![self.field.zero(); self.budget()];
            let mut times_axis = pure.clone();
            for (k, coefficient) in self.coefficients.iter().enumerate() {
                let a = self.field.mul(&e, coefficient)?;
                add_scaled(&mut pure[k], &a, Fr::one() - z);
                add_scaled(&mut times_axis[k], &a, -Fr::one());
                if k > 0 {
                    let h = self.field.mul(&a, &h)?;
                    for j in 0..k {
                        add_scaled(
                            &mut pure[j],
                            &self.field.mul(&h, &powers[k - 1 - j])?,
                            Fr::one(),
                        );
                    }
                }
            }
            out.push(TraceQuotient {
                axis: i,
                pure,
                times_axis,
            });
        }
        Ok(out)
    }
}

#[derive(Clone, Debug)]
pub struct TraceQuotient {
    pub axis: usize,
    pub pure: Vec<ExtensionElement>,
    pub times_axis: Vec<ExtensionElement>,
}
impl TraceQuotient {
    pub fn evaluate(&self, field: &ExtensionField, point: &[Fr]) -> Result<Fr> {
        field.checked(point)?;
        if self.axis >= field.degree() {
            return Err("trace quotient axis".into());
        }
        Ok(
            field.trace(&evaluate_extension_polynomial(field, &self.pure, point)?)?
                + point[self.axis]
                    * field.trace(&evaluate_extension_polynomial(
                        field,
                        &self.times_axis,
                        point,
                    )?)?,
        )
    }
}
