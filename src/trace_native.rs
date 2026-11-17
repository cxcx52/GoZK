//! Prefix-shared, independent sumchecks for the historical trace baseline.
//! Dense restrictions fold linearly; trace masks stay small extension-field
//! line polynomials. The implementation never expands a trace into monomials.
use crate::{
    native::{self, Binding, Expr, NativeRelation},
    tables::StructuredPolynomial,
    trace::TraceMask,
    trace_pcs::TraceSource,
    Result,
};
use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};
use std::collections::BTreeMap;

type Poly = Vec<Fr>;
fn add(a: &[Fr], b: &[Fr]) -> Poly {
    let mut out = a.to_vec();
    out.resize(a.len().max(b.len()), Fr::zero());
    for (x, y) in out.iter_mut().zip(b) {
        *x += y;
    }
    out
}
fn mul(a: &[Fr], b: &[Fr]) -> Poly {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut out = vec![Fr::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        if !x.is_zero() {
            for (j, y) in b.iter().enumerate() {
                out[i + j] += *x * y;
            }
        }
    }
    out
}
fn scale(mut a: Poly, c: Fr) -> Poly {
    for x in &mut a {
        *x *= c;
    }
    a
}
fn expr_line(e: &Expr, axis: usize, p: &[Fr], sources: &[Poly]) -> Poly {
    match e {
        Expr::Constant(c) => vec![*c],
        Expr::Variable(a) => {
            if *a == axis {
                vec![Fr::zero(), Fr::one()]
            } else {
                vec![p[*a]]
            }
        }
        Expr::Source(i) => sources[*i].clone(),
        Expr::Add(a, b) => add(
            &expr_line(a, axis, p, sources),
            &expr_line(b, axis, p, sources),
        ),
        Expr::Mul(a, b) => mul(
            &expr_line(a, axis, p, sources),
            &expr_line(b, axis, p, sources),
        ),
        Expr::Pow(a, n) => {
            let mut out = vec![Fr::one()];
            let mut base = expr_line(a, axis, p, sources);
            let mut n = *n;
            while n > 0 {
                if n & 1 == 1 {
                    out = mul(&out, &base);
                }
                n >>= 1;
                if n > 0 {
                    base = mul(&base, &base);
                }
            }
            out
        }
    }
}
fn expr_value(e: &Expr, p: &[Fr], sources: &[Fr]) -> Fr {
    match e {
        Expr::Constant(c) => *c,
        Expr::Variable(a) => p[*a],
        Expr::Source(i) => sources[*i],
        Expr::Add(a, b) => expr_value(a, p, sources) + expr_value(b, p, sources),
        Expr::Mul(a, b) => expr_value(a, p, sources) * expr_value(b, p, sources),
        Expr::Pow(a, n) => expr_value(a, p, sources).pow([*n]),
    }
}
struct Table {
    axes: Vec<usize>,
    values: Vec<Fr>,
    scale: Fr,
}
struct Mapped {
    map: Vec<Binding>,
    tables: Vec<Table>,
    mask: Option<TraceMask>,
}
impl Mapped {
    fn new(source: &TraceSource, map: &[Binding], dimension: usize) -> Result<Self> {
        if map.len() != source.dense().dimension()
            || map.iter().any(|b| {
                matches!(b,Binding::Variable(i) if *i>=dimension)
                    || matches!(b, Binding::Complement(_))
            })
        {
            return Err("trace baseline source map".into());
        }
        let mut tables = vec![];
        for term in source.dense().terms() {
            let map = &map[term.start..term.start + term.table.dimension()];
            let axes = map
                .iter()
                .filter_map(|b| {
                    if let Binding::Variable(a) = b {
                        Some(*a)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            if axes.windows(2).any(|w| w[0] >= w[1]) {
                return Err("trace dense source map must preserve order".into());
            }
            let values = (0..1usize << axes.len())
                .map(|i| {
                    let mut index = 0;
                    let mut j = 0;
                    for b in map {
                        index = (index << 1)
                            | match b {
                                Binding::Fixed(x) => *x as usize,
                                Binding::Variable(_) => {
                                    let bit = (i >> (axes.len() - 1 - j)) & 1;
                                    j += 1;
                                    bit
                                }
                                _ => unreachable!(),
                            };
                    }
                    term.table.values()[index]
                })
                .collect();
            tables.push(Table {
                axes,
                values,
                scale: term.scale,
            });
        }
        Ok(Self {
            map: map.to_vec(),
            tables,
            mask: source.mask().cloned(),
        })
    }
    fn dense_line(&self, axis: usize, p: &[Fr]) -> Poly {
        let mut out = vec![Fr::zero(); 2];
        for t in &self.tables {
            let active = t.axes.first() == Some(&axis);
            let rest = if active { &t.axes[1..] } else { &t.axes };
            let index = rest
                .iter()
                .fold(0, |n, a| (n << 1) | usize::from(p[*a] == Fr::one()));
            let lo = t.values[index] * t.scale;
            out[0] += lo;
            if active {
                out[1] += t.values[index + t.values.len() / 2] * t.scale - lo;
            }
        }
        out
    }
    fn line(&self, axis: usize, p: &[Fr]) -> Result<Poly> {
        let dense = self.dense_line(axis, p);
        let Some(mask) = &self.mask else {
            return Ok(dense);
        };
        let point = self
            .map
            .iter()
            .map(|b| match b {
                Binding::Fixed(x) => Fr::from(*x as u64),
                Binding::Variable(i) => p[*i],
                _ => unreachable!(),
            })
            .collect::<Vec<_>>();
        let axes = self
            .map
            .iter()
            .enumerate()
            .filter_map(|(i, b)| {
                if b == &Binding::Variable(axis) {
                    Some(i)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let line = match axes.as_slice() {
            [] => vec![mask.evaluate(&point)?],
            [a] => mask.line_coefficients(&point, *a)?,
            _ => return Err("trace line maps one native axis more than once".into()),
        };
        Ok(add(&dense, &line))
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
        work
    }
}
pub struct TraceSumcheck {
    relation: NativeRelation,
    sources: Vec<Mapped>,
    helper: StructuredPolynomial,
    rho: Fr,
    path: Vec<Fr>,
    cap: usize,
    pub fold_pairs: usize,
    pub line_points: usize,
}
impl TraceSumcheck {
    pub fn new(
        relation: NativeRelation,
        cap: usize,
        sources: &BTreeMap<String, TraceSource>,
        helper: StructuredPolynomial,
        rho: Fr,
    ) -> Result<Self> {
        if relation.dimension == 0
            || relation.dimension > helper.dimension()
            || !helper.terms().is_empty()
        {
            return Err("trace sumcheck dimension/helper".into());
        }
        let mapped = relation
            .sources
            .iter()
            .map(|s| {
                Mapped::new(
                    sources.get(&s.handle).ok_or("trace source missing")?,
                    &s.map,
                    relation.dimension,
                )
            })
            .collect::<Result<Vec<_>>>()?;
        // Check the same Boolean relation before invoking its random compression.
        // Trace masks vanish here, so the precheck reads only the dense tables.
        for i in 0..1usize << relation.dimension {
            let p = native::bits(i, relation.dimension);
            let values = mapped
                .iter()
                .map(|m| native::univariate(&m.dense_line(0, &p), p[0]))
                .collect::<Vec<_>>();
            if !expr_value(&relation.expression, &p, &values).is_zero() {
                return Err("witness violates historical Boolean relation".into());
            }
        }
        Ok(Self {
            relation,
            sources: mapped,
            helper,
            rho,
            path: vec![],
            cap,
            fold_pairs: 0,
            line_points: 0,
        })
    }
    pub fn round_coefficients(&mut self) -> Result<Poly> {
        let a = self.path.len();
        let d = self.relation.dimension;
        if a >= d {
            return Err("trace sumcheck complete".into());
        }
        let count = 1usize << (d - a - 1);
        let mut out = vec![Fr::zero()];
        for i in 0..count {
            let mut p = self.path.clone();
            p.push(Fr::zero());
            p.extend(native::bits(i, d - a - 1));
            let lines = self
                .sources
                .iter()
                .map(|s| s.line(a, &p))
                .collect::<Result<Vec<_>>>()?;
            let mut line = expr_line(&self.relation.expression, a, &p, &lines);
            if let Some(tau) = &self.relation.tau {
                let factor = (0..d)
                    .filter(|j| *j != a)
                    .map(|j| (Fr::one() - p[j]) * (Fr::one() - tau[j]) + p[j] * tau[j])
                    .product::<Fr>();
                line = mul(
                    &line,
                    &[
                        factor * (Fr::one() - tau[a]),
                        factor * (Fr::from(2u64) * tau[a] - Fr::one()),
                    ],
                );
            }
            out = add(&out, &scale(line, self.relation.weight));
        }
        self.line_points += count;
        let offset = self.helper.dimension() - d;
        for (e, c) in self.helper.extras() {
            if e[..offset].iter().any(|d| *d != 0) {
                return Err("helper outside native suffix".into());
            }
            let mut v = *c * self.rho;
            for j in 0..d {
                if j < a {
                    v *= self.path[j].pow([e[offset + j] as u64]);
                } else if j > a {
                    v *= if e[offset + j] == 0 {
                        Fr::from(2u64)
                    } else {
                        Fr::one()
                    };
                }
            }
            let degree = e[offset + a];
            if out.len() <= degree {
                out.resize(degree + 1, Fr::zero());
            }
            out[degree] += v;
        }
        while out.last().is_some_and(Zero::is_zero) {
            out.pop();
        }
        if out.len() > self.cap + 1 {
            return Err("historical honest line exceeds cap".into());
        }
        out.resize(self.cap + 1, Fr::zero());
        Ok(out)
    }
    pub fn fold(&mut self, r: Fr) -> Result<()> {
        let axis = self.path.len();
        if axis >= self.relation.dimension {
            return Err("trace sumcheck complete".into());
        }
        for s in &mut self.sources {
            self.fold_pairs += s.fold(axis, r);
        }
        self.path.push(r);
        Ok(())
    }
}
