//! Native suffix relations. Tables shrink as coordinates are fixed; no relation
//! is padded into a full global Boolean table. This first serial evaluator still
//! has coordinate-indexing overhead; operation counters expose table work.
use crate::{tables::StructuredPolynomial, Result};
use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Binding {
    Fixed(bool),
    Variable(usize),
    Complement(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceUse {
    pub handle: String,
    pub map: Vec<Binding>,
}
impl SourceUse {
    pub fn point(&self, native: &[Fr]) -> Vec<Fr> {
        self.map
            .iter()
            .map(|b| match b {
                Binding::Fixed(v) => Fr::from(*v as u64),
                Binding::Variable(i) => native[*i],
                Binding::Complement(i) => Fr::one() - native[*i],
            })
            .collect()
    }
}

#[derive(Clone)]
pub enum Expr {
    Constant(Fr),
    Variable(usize),
    Source(usize),
    Add(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Pow(Box<Self>, u64),
}
impl Expr {
    fn validate(&self, d: usize, n: usize, depth: usize) -> Result<()> {
        if depth > 2048 {
            return Err("native expression nesting limit".into());
        }
        match self {
            Self::Variable(i) if *i >= d => Err("expression variable outside dimension".into()),
            Self::Source(i) if *i >= n => Err("expression source outside registry".into()),
            Self::Add(a, b) | Self::Mul(a, b) => {
                a.validate(d, n, depth + 1)?;
                b.validate(d, n, depth + 1)
            }
            Self::Pow(a, _) => a.validate(d, n, depth + 1),
            _ => Ok(()),
        }
    }
    pub fn constant(v: u64) -> Self {
        Self::Constant(Fr::from(v))
    }
    pub fn plus(self, b: Self) -> Self {
        Self::Add(Box::new(self), Box::new(b))
    }
    pub fn times(self, b: Self) -> Self {
        Self::Mul(Box::new(self), Box::new(b))
    }
    pub fn minus(self, b: Self) -> Self {
        self.plus(Self::Constant(-Fr::one()).times(b))
    }
    pub fn power(self, e: u64) -> Self {
        Self::Pow(Box::new(self), e)
    }
    fn eval(&self, p: &[Fr], sources: &[Fr]) -> Fr {
        match self {
            Self::Constant(v) => *v,
            Self::Variable(i) => p[*i],
            Self::Source(i) => sources[*i],
            Self::Add(a, b) => a.eval(p, sources) + b.eval(p, sources),
            Self::Mul(a, b) => a.eval(p, sources) * b.eval(p, sources),
            Self::Pow(a, e) => a.eval(p, sources).pow([*e]),
        }
    }
}

pub fn eq(p: &[Fr], q: &[Fr]) -> Fr {
    assert_eq!(p.len(), q.len());
    p.iter()
        .zip(q)
        .map(|(a, b)| (Fr::one() - a) * (Fr::one() - b) + *a * b)
        .product()
}
pub fn bits(i: usize, n: usize) -> Vec<Fr> {
    (0..n)
        .map(|a| Fr::from(((i >> (n - 1 - a)) & 1) as u64))
        .collect()
}
pub fn eq_zero(axes: impl Iterator<Item = usize>) -> Expr {
    axes.fold(Expr::constant(1), |a, i| {
        a.times(Expr::constant(1).minus(Expr::Variable(i)))
    })
}

#[derive(Clone)]
pub struct NativeRelation {
    pub dimension: usize,
    pub sources: Vec<SourceUse>,
    pub expression: Expr,
    pub tau: Option<Vec<Fr>>,
    pub weight: Fr,
}
impl NativeRelation {
    pub fn new(dimension: usize) -> Self {
        Self {
            dimension,
            sources: vec![],
            expression: Expr::constant(0),
            tau: None,
            weight: Fr::one(),
        }
    }
    pub fn source(&mut self, handle: &str, map: Vec<Binding>) -> Expr {
        let source = SourceUse {
            handle: handle.to_owned(),
            map,
        };
        let i = self
            .sources
            .iter()
            .position(|x| x == &source)
            .unwrap_or_else(|| {
                self.sources.push(source);
                self.sources.len() - 1
            });
        Expr::Source(i)
    }
    pub fn evaluate(
        &self,
        p: &[Fr],
        get: &mut impl FnMut(&str, &[Fr]) -> Result<Fr>,
    ) -> Result<Fr> {
        if p.len() != self.dimension {
            return Err("native dimension mismatch".into());
        }
        let values = self
            .sources
            .iter()
            .map(|s| get(&s.handle, &s.point(p)))
            .collect::<Result<Vec<_>>>()?;
        Ok(self.weight
            * self.expression.eval(p, &values)
            * self.tau.as_ref().map_or(Fr::one(), |t| eq(p, t)))
    }
}

struct MappedTable {
    axes: Vec<usize>,
    values: Vec<Fr>,
    scale: Fr,
}
struct MappedPolynomial {
    tables: Vec<MappedTable>,
    extras: Vec<(Vec<usize>, Vec<usize>, Fr)>,
}
struct BooleanSuffixValues {
    axes: Vec<usize>,
    values: Vec<Fr>,
}
impl MappedPolynomial {
    fn new(poly: &StructuredPolynomial, map: &[Binding], d: usize) -> Result<Self> {
        if poly.dimension() != map.len() {
            return Err("source map dimension".into());
        }
        let mut tables = vec![];
        for t in poly.terms() {
            let binding = &map[t.start..t.start + t.table.dimension()];
            let axes: Vec<_> = binding
                .iter()
                .filter_map(|b| {
                    if let Binding::Variable(i) | Binding::Complement(i) = b {
                        Some(*i)
                    } else {
                        None
                    }
                })
                .collect();
            if axes.windows(2).any(|a| a[0] >= a[1]) || axes.iter().any(|a| *a >= d) {
                return Err("source map must preserve variable order".into());
            }
            let mut values = Vec::with_capacity(1 << axes.len());
            for i in 0..1 << axes.len() {
                let mut index = 0;
                let mut j = 0;
                for b in binding {
                    index = (index << 1)
                        | match b {
                            Binding::Fixed(b) => *b as usize,
                            Binding::Variable(_) | Binding::Complement(_) => {
                                let bit = (i >> (axes.len() - 1 - j)) & 1;
                                j += 1;
                                if matches!(b, Binding::Complement(_)) {
                                    1 - bit
                                } else {
                                    bit
                                }
                            }
                        };
                }
                values.push(t.table.values()[index]);
            }
            tables.push(MappedTable {
                axes,
                values,
                scale: t.scale,
            });
        }
        let mut extras = vec![];
        for (exponent, value) in poly.extras() {
            let mut e = vec![0; d];
            let mut complemented = vec![0; d];
            let mut c = *value;
            for (power, b) in exponent.iter().zip(map) {
                if *power > 0 {
                    match b {
                        Binding::Fixed(false) => c = Fr::zero(),
                        Binding::Fixed(true) => {}
                        Binding::Variable(a) => e[*a] += power,
                        Binding::Complement(a) => complemented[*a] += power,
                    }
                }
            }
            if !c.is_zero() {
                extras.push((e, complemented, c));
            }
        }
        Ok(Self { tables, extras })
    }
    fn dense_at(&self, axis: usize, p: &[Fr]) -> Fr {
        let mut value = Fr::zero();
        for t in &self.tables {
            let current = t.axes.first() == Some(&axis);
            let rest = if current { &t.axes[1..] } else { &t.axes[..] };
            let index = rest
                .iter()
                .fold(0, |n, a| (n << 1) | usize::from(p[*a] == Fr::one()));
            value += t.scale
                * if current {
                    let lo = t.values[index];
                    lo + p[axis] * (t.values[index + (t.values.len() / 2)] - lo)
                } else {
                    t.values[index]
                };
        }
        value
    }

    fn extras_at(&self, axis: usize, p: &[Fr]) -> Fr {
        let mut value = Fr::zero();
        for (e, complemented, c) in &self.extras {
            let mut v = *c;
            for a in axis..e.len() {
                if e[a] > 0 {
                    v *= if a == axis {
                        p[a].pow([e[a] as u64])
                    } else {
                        p[a]
                    };
                }
                if complemented[a] > 0 {
                    v *= if a == axis {
                        (Fr::one() - p[a]).pow([complemented[a] as u64])
                    } else {
                        Fr::one() - p[a]
                    };
                }
            }
            value += v;
        }
        value
    }

    fn suffix_values(&self, axis: usize, x: Fr) -> Option<BooleanSuffixValues> {
        let (first, _, _) = self.extras.first()?;
        let axes: Vec<usize> = (axis + 1..first.len())
            .filter(|&a| self.extras.iter().any(|(e, f, _)| e[a] != 0 || f[a] != 0))
            .collect();
        if axes.len() > 8 {
            return None;
        }
        let mut p = vec![Fr::zero(); first.len()];
        p[axis] = x;
        let values = (0..1usize << axes.len())
            .map(|i| {
                for (bit, &a) in axes.iter().enumerate() {
                    p[a] = Fr::from(((i >> bit) & 1) as u64);
                }
                self.extras_at(axis, &p)
            })
            .collect();
        Some(BooleanSuffixValues { axes, values })
    }

    fn evaluate_round(&self, axis: usize, p: &[Fr], slice: &Option<BooleanSuffixValues>) -> Fr {
        let extra = match slice {
            Some(s) => {
                let i = s.axes.iter().enumerate().fold(0, |i, (bit, a)| {
                    i | (usize::from(p[*a] == Fr::one()) << bit)
                });
                s.values[i]
            }
            None => self.extras_at(axis, p),
        };
        self.dense_at(axis, p) + extra
    }
    fn fold(&mut self, axis: usize, r: Fr) -> usize {
        let mut work = 0;
        for t in &mut self.tables {
            if t.axes.first() == Some(&axis) {
                let half = t.values.len() / 2;
                crate::parallel::fold_pairs(&mut t.values, r, None);
                t.values.truncate(half);
                t.axes.remove(0);
                work += half;
            }
        }
        for (e, complemented, c) in &mut self.extras {
            *c *= r.pow([e[axis] as u64]);
            *c *= (Fr::one() - r).pow([complemented[axis] as u64]);
            e[axis] = 0;
            complemented[axis] = 0;
        }
        work
    }
}

struct CompiledRelation {
    native: NativeRelation,
    sources: Vec<MappedPolynomial>,
    path: Vec<Fr>,
    boolean_sum: Fr,
}

pub struct NativeSumcheck {
    dimension: usize,
    relations: Vec<CompiledRelation>,
    helper: StructuredPolynomial,
    rho: Fr,
    path: Vec<Fr>,
    pub fold_pairs: usize,
    pub sample_points: usize,
}
impl NativeSumcheck {
    pub fn new(
        dimension: usize,
        relations: Vec<NativeRelation>,
        polys: &BTreeMap<String, StructuredPolynomial>,
        helper: StructuredPolynomial,
        rho: Fr,
    ) -> Result<Self> {
        Self::new_with_ambient(dimension, dimension, relations, polys, helper, rho)
    }

    /// A single native relation is folded in its own coordinates. Its sources
    /// retain the same full opening-point maps as in the global protocol.
    pub(crate) fn new_native(
        ambient: usize,
        relation: NativeRelation,
        polys: &BTreeMap<String, StructuredPolynomial>,
        helper: StructuredPolynomial,
        rho: Fr,
    ) -> Result<Self> {
        Self::new_with_ambient(
            relation.dimension,
            ambient,
            vec![relation],
            polys,
            helper,
            rho,
        )
    }

    fn new_with_ambient(
        dimension: usize,
        ambient: usize,
        relations: Vec<NativeRelation>,
        polys: &BTreeMap<String, StructuredPolynomial>,
        helper: StructuredPolynomial,
        rho: Fr,
    ) -> Result<Self> {
        if dimension == 0 || dimension >= usize::BITS as usize || helper.dimension() != dimension {
            return Err("global sumcheck dimension".into());
        }
        if !helper.terms().is_empty() {
            return Err("sumcheck helper must be sparse axis powers".into());
        }
        let mut compiled = vec![];
        for native in relations {
            if native.dimension == 0
                || native.dimension > dimension
                || native
                    .tau
                    .as_ref()
                    .is_some_and(|t| t.len() != native.dimension)
            {
                return Err("native relation dimension".into());
            }
            if native.sources.iter().any(|s| {
                s.map.len() != ambient
                    || s.map
                        .iter()
                        .any(|b| matches!(b,Binding::Variable(a)|Binding::Complement(a) if *a>=native.dimension))
            }) {
                return Err("source coordinate map".into());
            }
            native
                .expression
                .validate(native.dimension, native.sources.len(), 0)?;
            let mut sources = vec![];
            for s in &native.sources {
                sources.push(MappedPolynomial::new(
                    polys.get(&s.handle).ok_or("missing source")?,
                    &s.map,
                    native.dimension,
                )?);
            }
            let mut boolean_sum = Fr::zero();
            let precheck_slices = [Fr::zero(), Fr::one()].map(|x| {
                sources
                    .iter()
                    .map(|s| s.suffix_values(0, x))
                    .collect::<Vec<_>>()
            });
            for i in 0..1 << native.dimension {
                let p = bits(i, native.dimension);
                let values = sources
                    .iter()
                    .zip(&precheck_slices[usize::from(p[0] == Fr::one())])
                    .map(|(s, slice)| s.evaluate_round(0, &p, slice))
                    .collect::<Vec<_>>();
                let v = native.expression.eval(&p, &values);
                // Every native relation vanishes on its own Boolean domain for
                // an honest witness. This is a prover precheck, not a verifier test.
                if !v.is_zero() {
                    return Err("witness violates a native Boolean relation".into());
                }
                boolean_sum +=
                    native.weight * v * native.tau.as_ref().map_or(Fr::one(), |t| eq(&p, t));
            }
            compiled.push(CompiledRelation {
                native,
                sources,
                path: vec![],
                boolean_sum,
            });
        }
        Ok(Self {
            dimension,
            relations: compiled,
            helper,
            rho,
            path: vec![],
            fold_pairs: 0,
            sample_points: 0,
        })
    }
    pub fn round_value(&mut self, x: Fr) -> Fr {
        assert!(
            self.path.len() < self.dimension,
            "sumcheck already finished"
        );
        let a = self.path.len();
        let mut total = Fr::zero();
        for rel in &self.relations {
            let offset = self.dimension - rel.native.dimension;
            let mut pad = self.path[..offset.min(a)]
                .iter()
                .map(|r| Fr::one() - r)
                .product::<Fr>();
            if a < offset {
                total += pad * (Fr::one() - x) * rel.boolean_sum;
                continue;
            }
            let local = a - offset;
            // At this point all padding coordinates have already been fixed.
            if offset == 0 {
                pad = Fr::one();
            }
            let count = 1 << (rel.native.dimension - local - 1);
            let slices: Vec<_> = rel
                .sources
                .iter()
                .map(|s| s.suffix_values(local, x))
                .collect();
            total += crate::parallel::sum_indices(count, |i| {
                let mut p = rel.path.clone();
                p.push(x);
                p.extend(bits(i, rel.native.dimension - local - 1));
                let values = rel
                    .sources
                    .iter()
                    .zip(&slices)
                    .map(|(s, slice)| s.evaluate_round(local, &p, slice))
                    .collect::<Vec<_>>();
                pad * rel.native.weight
                    * rel.native.expression.eval(&p, &values)
                    * rel.native.tau.as_ref().map_or(Fr::one(), |t| eq(&p, t))
            });
            self.sample_points += count;
        }
        // Exact Boolean suffix sums for sparse helper monomials.
        for (e, c) in self.helper.extras() {
            let mut value = *c;
            for j in 0..self.dimension {
                value *= if j < a {
                    self.path[j].pow([e[j] as u64])
                } else if j == a {
                    x.pow([e[j] as u64])
                } else if e[j] == 0 {
                    Fr::from(2u64)
                } else {
                    Fr::one()
                };
            }
            total += self.rho * value;
        }
        total
    }
    pub fn fold(&mut self, r: Fr) {
        assert!(
            self.path.len() < self.dimension,
            "sumcheck already finished"
        );
        let a = self.path.len();
        for rel in &mut self.relations {
            let offset = self.dimension - rel.native.dimension;
            if a >= offset {
                let local = a - offset;
                for source in &mut rel.sources {
                    self.fold_pairs += source.fold(local, r);
                }
                rel.path.push(r);
            }
        }
        self.path.push(r);
    }
}

pub fn interpolate(samples: &[Fr]) -> Result<Vec<Fr>> {
    let n = samples.len();
    let mut out = vec![Fr::zero(); n];
    for (i, y) in samples.iter().enumerate() {
        let mut basis = vec![Fr::one()];
        let mut den = Fr::one();
        for j in 0..n {
            if i == j {
                continue;
            }
            let mut next = vec![Fr::zero(); basis.len() + 1];
            for (e, v) in basis.iter().enumerate() {
                next[e] -= Fr::from(j as u64) * v;
                next[e + 1] += v;
            }
            basis = next;
            den *= Fr::from(i as u64) - Fr::from(j as u64);
        }
        let scale = *y * den.inverse().ok_or("interpolation collision")?;
        for (a, b) in out.iter_mut().zip(basis) {
            *a += scale * b;
        }
    }
    Ok(out)
}
pub fn univariate(coeffs: &[Fr], x: Fr) -> Fr {
    coeffs.iter().rev().fold(Fr::zero(), |v, c| v * x + c)
}
