//! Single-table scalar lookup from the V6 five-relation construction.
//! Cycles are certified algebraically over GF(2); no small-dimension feedback
//! polynomial is silently extrapolated to larger tables.
use crate::{
    codec::scalar_bytes,
    native::{eq_zero, Binding, Expr, NativeRelation},
    profile::ValidatedProfile,
    random::sample_fr,
    tables::{DenseMle, StructuredPolynomial},
    Result,
};
use ark_bls12_381::Fr;
use ark_ff::{One, Zero};
use rand::RngCore;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LookupFunction {
    SumColumns,
    FirstColumn,
}
impl LookupFunction {
    pub fn name(self) -> &'static str {
        match self {
            Self::SumColumns => "sum-columns",
            Self::FirstColumn => "first-column",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimitiveCycle {
    dimension: usize,
    polynomial: u64,
    order_factors: Vec<u64>,
    feedback: Vec<bool>,
    step_mask: usize,
}
fn degree(f: u64) -> usize {
    (63 - f.leading_zeros()) as usize
}
fn remainder(mut a: u64, b: u64) -> u64 {
    let d = degree(b);
    while a != 0 && degree(a) >= d {
        a ^= b << (degree(a) - d);
    }
    a
}
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = remainder(a, b);
        a = b;
        b = r;
    }
    a
}
fn multiply_mod(mut a: u64, mut b: u64, f: u64) -> u64 {
    let mut r = 0;
    let high = 1u64 << degree(f);
    while b != 0 {
        if b & 1 != 0 {
            r ^= a;
        }
        b >>= 1;
        a <<= 1;
        if a & high != 0 {
            a ^= f;
        }
    }
    r
}
fn power_mod(mut a: u64, mut e: u64, f: u64) -> u64 {
    a = remainder(a, f);
    let mut r = 1;
    while e != 0 {
        if e & 1 != 0 {
            r = multiply_mod(r, a, f);
        }
        a = multiply_mod(a, a, f);
        e >>= 1;
    }
    r
}
fn prime_factors(mut n: u64) -> Vec<u64> {
    let mut p = 2;
    let mut out = vec![];
    while p * p <= n {
        if n % p == 0 {
            out.push(p);
            while n % p == 0 {
                n /= p;
            }
        }
        p += 1;
    }
    if n > 1 {
        out.push(n);
    }
    out
}

impl PrimitiveCycle {
    /// Deterministic first primitive monic polynomial, with Rabin irreducibility
    /// and prime-factor order certificates. Complexity is polynomial in degree
    /// per candidate; no period-sized walk is used to certify the polynomial.
    pub fn new(dimension: usize) -> Result<Self> {
        if !(1..=22).contains(&dimension) {
            return Err("certified cycle degree must be in 1..22".into());
        }
        let order = (1u64 << dimension) - 1;
        let order_factors = prime_factors(order);
        for low in (1..1u64 << dimension).step_by(2) {
            let f = (1u64 << dimension) | low;
            if Self::valid_polynomial(dimension, f, &order_factors) {
                return Self::from_polynomial(dimension, f);
            }
        }
        Err("primitive polynomial search failed".into())
    }
    fn valid_polynomial(d: usize, f: u64, factors: &[u64]) -> bool {
        if degree(f) != d || f & 1 == 0 {
            return false;
        }
        let x = remainder(2, f);
        if power_mod(2, 1u64 << d, f) != x {
            return false;
        }
        for p in prime_factors(d as u64) {
            if gcd(power_mod(2, 1u64 << (d / (p as usize)), f) ^ x, f) != 1 {
                return false;
            }
        }
        let order = (1u64 << d) - 1;
        power_mod(2, order, f) == 1 && factors.iter().all(|p| power_mod(2, order / p, f) != 1)
    }
    pub fn from_polynomial(dimension: usize, polynomial: u64) -> Result<Self> {
        if !(1..=22).contains(&dimension) || polynomial == 0 {
            return Err("invalid cycle dimension/polynomial".into());
        }
        let order_factors = prime_factors((1u64 << dimension) - 1);
        if !Self::valid_polynomial(dimension, polynomial, &order_factors) {
            return Err("feedback polynomial is not primitive".into());
        }
        let feedback = (1..dimension)
            .map(|i| (polynomial >> i) & 1 != 0)
            .collect::<Vec<_>>();
        let mut step_mask = 1usize << (dimension - 1);
        for (i, on) in feedback.iter().enumerate() {
            if *on {
                step_mask |= 1 << (dimension - 2 - i);
            }
        }
        Ok(Self {
            dimension,
            polynomial,
            order_factors,
            feedback,
            step_mask,
        })
    }
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    pub fn polynomial(&self) -> u64 {
        self.polynomial
    }
    pub fn order_factors(&self) -> &[u64] {
        &self.order_factors
    }
    pub fn feedback(&self) -> &[bool] {
        &self.feedback
    }
    pub fn step(&self, index: usize) -> usize {
        assert!(index < 1 << self.dimension);
        (index >> 1) ^ if index & 1 != 0 { self.step_mask } else { 0 }
    }
    /// Assign ordered cycle values at the nonzero Boolean addresses. The zero
    /// address is public zero, not an additional physical table entry.
    pub fn embed(&self, values: &[Fr]) -> Result<Vec<Fr>> {
        let n = 1usize << self.dimension;
        if values.len() != n - 1 {
            return Err("cycle table requires exactly 2^r-1 values".into());
        }
        let mut out = vec![Fr::zero(); n];
        let mut point = 1usize << (self.dimension - 1);
        for v in values {
            out[point] = *v;
            point = self.step(point);
        }
        if point != 1usize << (self.dimension - 1) {
            return Err("certified cycle period mismatch".into());
        }
        Ok(out)
    }
}

pub struct LookupWitness {
    pub targets: Vec<Fr>,
    pub addresses: Vec<usize>,
    pub counts: Vec<usize>,
    pub table_embedded: Vec<Fr>,
    pub h_zeroed: Vec<Fr>,
    pub h_source: StructuredPolynomial,
    pub table_cycle: PrimitiveCycle,
    pub h_cycle: PrimitiveCycle,
}
impl LookupWitness {
    /// Address/count construction uses the public table's first occurrence for
    /// duplicates. H repeats each physical entry once plus its query count.
    pub fn new(
        p: &ValidatedProfile,
        physical_table: &[Fr],
        witness: &[Fr],
        function: LookupFunction,
        rng: &mut impl RngCore,
    ) -> Result<Self> {
        if !p.lookup() || physical_table.len() != p.n() - 1 || witness.len() != p.n_total() {
            return Err("lookup input shape/profile mismatch".into());
        }
        let table_cycle = PrimitiveCycle::new(p.nu())?;
        let h_cycle = PrimitiveCycle::new(p.nu() + 1)?;
        let targets = (0..p.n())
            .map(|row| match function {
                LookupFunction::FirstColumn => witness[row],
                LookupFunction::SumColumns => (0..p.k()).map(|a| witness[a * p.n() + row]).sum(),
            })
            .collect::<Vec<Fr>>();
        let mut addresses_by_value = BTreeMap::new();
        for (i, v) in physical_table.iter().enumerate() {
            addresses_by_value.entry(scalar_bytes(v)).or_insert(i);
        }
        let mut addresses = Vec::with_capacity(p.n());
        let mut counts = vec![0usize; p.n() - 1];
        for v in &targets {
            let i = *addresses_by_value
                .get(&scalar_bytes(v))
                .ok_or("lookup target is not in the public table")?;
            addresses.push(i);
            counts[i] += 1;
        }
        let mut repeated = Vec::with_capacity(2 * p.n() - 1);
        for (v, count) in physical_table.iter().zip(&counts) {
            repeated.extend(std::iter::repeat_n(*v, 1 + count));
        }
        let table_embedded = table_cycle.embed(physical_table)?;
        let h_zeroed = h_cycle.embed(&repeated)?;
        let mut raw = h_zeroed.clone();
        raw[0] = sample_fr(rng)?;
        let start = p.l() - p.nu() - 1;
        let last = p.l() - 1;
        let mut extras = BTreeMap::new();
        for (first, last_power) in [(0, 2), (1, 2), (2, 0)] {
            let coin = sample_fr(rng)?;
            let mut e = vec![0; p.l()];
            e[start] = first;
            e[last] = last_power;
            *extras.entry(e.clone()).or_default() += coin;
            if last_power == 2 {
                e[last] = 1
            } else {
                e[start] = 1
            }
            *extras.entry(e).or_default() -= coin;
        }
        let table_poly = StructuredPolynomial::from_table(p.l(), start, DenseMle::new(raw)?)?;
        let h_source = StructuredPolynomial::new(p.l(), table_poly.terms().to_vec(), extras)?;
        Ok(Self {
            targets,
            addresses,
            counts,
            table_embedded,
            h_zeroed,
            h_source,
            table_cycle,
            h_cycle,
        })
    }
    pub fn leaves(&self, beta: Fr, gamma: Fr) -> Result<(Vec<Fr>, Vec<Fr>)> {
        if gamma.is_zero() {
            return Err("lookup gamma must be nonzero".into());
        }
        let n = self.targets.len();
        let mut left = Vec::with_capacity(2 * n);
        left.extend(self.targets.iter().map(|v| (Fr::one() + beta) * v + gamma));
        left.extend((0..n).map(|i| {
            self.table_embedded[i] + beta * self.table_embedded[self.table_cycle.step(i)] + gamma
        }));
        let right = (0..2 * n)
            .map(|i| self.h_zeroed[i] + beta * self.h_zeroed[self.h_cycle.step(i)] + gamma)
            .collect();
        Ok((left, right))
    }
}

/// Additional lookup-W randomness. For c=0 the core witness already has the
/// same last-axis mask, so a second independent copy is unnecessary.
pub fn witness_mask(p: &ValidatedProfile, rng: &mut impl RngCore) -> Result<StructuredPolynomial> {
    if !p.lookup() {
        return Err("lookup mask requested for core profile".into());
    }
    let mut extras = BTreeMap::new();
    if p.c() > 0 {
        for column in 0..p.k() {
            let coin = sample_fr(rng)?;
            let mut e = vec![0; p.l()];
            for j in 0..p.c() {
                e[p.core_offset() + 1 + j] = (column >> (p.c() - 1 - j)) & 1;
            }
            e[p.l() - 1] = 2;
            *extras.entry(e.clone()).or_default() += coin;
            e[p.l() - 1] = 1;
            *extras.entry(e).or_default() -= coin;
        }
    }
    StructuredPolynomial::new(p.l(), vec![], extras)
}

pub fn masked_tree(
    p: &ValidatedProfile,
    leaves: &[Fr],
    root_noise: bool,
    rng: &mut impl RngCore,
) -> Result<StructuredPolynomial> {
    if leaves.len() != 2 * p.n() {
        return Err("lookup tree leaf length mismatch".into());
    }
    let n = leaves.len();
    let mut heap = vec![Fr::zero(); 2 * n];
    heap[n..].copy_from_slice(leaves);
    for i in (1..n).rev() {
        heap[i] = heap[2 * i] * heap[2 * i + 1];
    }
    let start = p.l() - p.nu() - 2;
    let last = p.l() - 1;
    let mut extras = BTreeMap::new();
    for (first, last_power) in [(0, 2), (1, 2), (2, 0), (2, 1)] {
        let coin = sample_fr(rng)?;
        let mut e = vec![0; p.l()];
        e[start] = first;
        e[last] = last_power;
        *extras.entry(e.clone()).or_default() += coin;
        if last_power == 2 {
            e[last] = 1
        } else {
            e[start] = 1
        }
        *extras.entry(e).or_default() -= coin;
    }
    if root_noise {
        let coin = sample_fr(rng)?;
        for (first, y, sign) in [(2, 2, 1), (2, 1, -1), (1, 2, -1), (1, 1, 1)] {
            let mut e = vec![0; p.l()];
            e[start] = first;
            e[last] = y;
            *extras.entry(e).or_default() += if sign == 1 { coin } else { -coin };
        }
    }
    let poly = StructuredPolynomial::from_table(p.l(), start, DenseMle::new(heap)?)?;
    StructuredPolynomial::new(p.l(), poly.terms().to_vec(), extras)
}

fn coordinate(binding: &Binding) -> Expr {
    match binding {
        Binding::Fixed(v) => Expr::constant(*v as u64),
        Binding::Variable(a) => Expr::Variable(*a),
        Binding::Complement(a) => Expr::constant(1).minus(Expr::Variable(*a)),
    }
}
fn padded(l: usize, map: Vec<Binding>) -> Vec<Binding> {
    std::iter::repeat_n(Binding::Fixed(false), l - map.len())
        .chain(map)
        .collect()
}
fn variables(start: usize, n: usize) -> Vec<Binding> {
    (start..start + n).map(Binding::Variable).collect()
}
fn branches(cycle: &PrimitiveCycle, start: usize) -> (Vec<Binding>, Vec<Binding>) {
    let mut zero = vec![Binding::Fixed(false)];
    zero.extend(variables(start, cycle.dimension() - 1));
    let mut one = vec![Binding::Fixed(true)];
    one.extend(cycle.feedback().iter().enumerate().map(|(a, flip)| {
        if *flip {
            Binding::Complement(start + a)
        } else {
            Binding::Variable(start + a)
        }
    }));
    (zero, one)
}
fn hbar(rel: &mut NativeRelation, p: &ValidatedProfile, map: Vec<Binding>) -> Expr {
    let zero = map.iter().fold(Expr::constant(1), |a, b| {
        a.times(Expr::constant(1).minus(coordinate(b)))
    });
    Expr::constant(1)
        .minus(zero)
        .times(rel.source("H", padded(p.l(), map)))
}
fn witness(rel: &mut NativeRelation, p: &ValidatedProfile, map: Vec<Binding>) -> Expr {
    let map = padded(p.l(), map);
    let w = rel.source("W", map.clone());
    if !p.virtual_public() {
        return w;
    }
    let chi = map[p.core_offset()..p.l() - p.public_log()]
        .iter()
        .fold(Expr::constant(1), |a, b| {
            a.times(Expr::constant(1).minus(coordinate(b)))
        });
    let public = rel.source("__public", map);
    Expr::constant(1)
        .minus(chi.clone())
        .times(w)
        .plus(chi.times(public))
}

/// Order: left leaf, right leaf, internal C, internal E, joint C−E root.
/// The first four get equality weights; the last root gets no random equality.
pub fn relations(
    p: &ValidatedProfile,
    function: LookupFunction,
    table_cycle: &PrimitiveCycle,
    h_cycle: &PrimitiveCycle,
    beta: Fr,
    gamma: Fr,
) -> Result<Vec<NativeRelation>> {
    if !p.lookup() || table_cycle.dimension() != p.nu() || h_cycle.dimension() != p.nu() + 1 {
        return Err("lookup cycle/profile mismatch".into());
    }
    let r = p.nu() + 1;
    let mut out = vec![];
    let mut left = NativeRelation::new(r);
    let mut map = vec![Binding::Fixed(true)];
    map.extend(variables(0, r));
    let tree = left.source("C", padded(p.l(), map));
    let mut f = Expr::constant(0);
    let columns = if function == LookupFunction::FirstColumn {
        1
    } else {
        p.k()
    };
    for a in 0..columns {
        let mut map = vec![Binding::Fixed(false)];
        map.extend((0..p.c()).map(|j| Binding::Fixed(((a >> (p.c() - 1 - j)) & 1) != 0)));
        map.extend(variables(1, p.nu()));
        f = f.plus(witness(&mut left, p, map));
    }
    let t = left.source("table", padded(p.l(), variables(1, p.nu())));
    let (b0, b1) = branches(table_cycle, 1);
    let t0 = left.source("table", padded(p.l(), b0));
    let t1 = left.source("table", padded(p.l(), b1));
    let delta = Expr::constant(1)
        .minus(Expr::Variable(p.nu()))
        .times(t0)
        .plus(Expr::Variable(p.nu()).times(t1));
    let value = Expr::constant(1)
        .minus(Expr::Variable(0))
        .times(Expr::Constant(Fr::one() + beta))
        .times(f)
        .plus(Expr::Variable(0).times(t.plus(Expr::Constant(beta).times(delta))))
        .plus(Expr::Constant(gamma));
    left.expression = tree.minus(value);
    out.push(left);
    let mut right = NativeRelation::new(r);
    let mut map = vec![Binding::Fixed(true)];
    map.extend(variables(0, r));
    let tree = right.source("E", padded(p.l(), map));
    let h = hbar(&mut right, p, variables(0, r));
    let (b0, b1) = branches(h_cycle, 0);
    let h0 = hbar(&mut right, p, b0);
    let h1 = hbar(&mut right, p, b1);
    let delta = Expr::constant(1)
        .minus(Expr::Variable(r - 1))
        .times(h0)
        .plus(Expr::Variable(r - 1).times(h1));
    right.expression = tree.minus(
        h.plus(Expr::Constant(beta).times(delta))
            .plus(Expr::Constant(gamma)),
    );
    out.push(right);
    for name in ["C", "E"] {
        let mut rel = NativeRelation::new(r);
        let mut map = vec![Binding::Fixed(false)];
        map.extend(variables(0, r));
        let parent = rel.source(name, padded(p.l(), map));
        let mut map = variables(0, r);
        map.push(Binding::Fixed(false));
        let child0 = rel.source(name, padded(p.l(), map));
        let mut map = variables(0, r);
        map.push(Binding::Fixed(true));
        let child1 = rel.source(name, padded(p.l(), map));
        rel.expression = Expr::constant(1)
            .minus(eq_zero(0..r))
            .times(parent.minus(child0.times(child1)));
        out.push(rel);
    }
    let mut root = NativeRelation::new(r + 1);
    root.expression = root
        .source("CminusE", padded(p.l(), variables(0, r + 1)))
        .times(eq_zero(0..r))
        .times(Expr::Variable(r));
    out.push(root);
    Ok(out)
}
