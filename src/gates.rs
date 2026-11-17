//! Fixed-circuit families for degree, expression-size and width experiments.
//! Fixture seeds generate application inputs only. They must never be reused
//! as the prover's private mask/blinding randomness.
use crate::{
    codec::scalar_bytes,
    native::{Binding, Expr, NativeRelation},
    random::sample_fr,
    Result,
};
use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};
use rand::{rngs::StdRng, RngCore, SeedableRng};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GateFamily {
    /// q0 W0^degree - W1 - qout; two active witness columns at every width.
    PowerCopy,
    /// Sum of distinct degree-d monomials on columns 0..k-2, minus W_(k-1).
    Dense { terms: usize },
    /// Separate k=1 relation W0^degree-W0=0; witnesses 0/1 satisfy it.
    SingleColumnBoolean,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateTerm {
    pub selector: String,
    pub powers: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct GateDescriptor {
    family: GateFamily,
    width: usize,
    degree: usize,
    terms: Vec<GateTerm>,
    output_column: usize,
}

#[derive(Clone, Debug)]
pub struct GateFixture {
    pub selectors: BTreeMap<String, Vec<Fr>>,
    pub wiring: Vec<usize>,
    pub witness: Vec<Fr>,
    pub input_seed: u64,
    pub instance_id: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateCost {
    pub total_degree: usize,
    pub monomial_terms: usize,
    pub selector_count: usize,
    pub active_columns: usize,
    /// Binary square-and-multiply for each positive power, excluding an initial
    /// multiply by one. The current native Expr backend may do redundant work.
    pub power_multiplications: usize,
    pub within_monomial_multiplications: usize,
    pub selector_multiplications: usize,
}

fn compositions(
    total: usize,
    slots: usize,
    prefix: &mut Vec<usize>,
    limit: usize,
    out: &mut Vec<Vec<usize>>,
) {
    if out.len() >= limit {
        return;
    }
    if slots == 1 {
        prefix.push(total);
        out.push(prefix.clone());
        prefix.pop();
        return;
    }
    // Deterministic descending lexicographic order; early limit avoids building
    // all binomially many monomials when the experiment requests only a few.
    for first in (0..=total).rev() {
        prefix.push(first);
        compositions(total - first, slots - 1, prefix, limit, out);
        prefix.pop();
        if out.len() >= limit {
            break;
        }
    }
}

fn witness_map(dimension: usize, nu: usize, c: usize, column: usize) -> Vec<Binding> {
    std::iter::repeat(Binding::Fixed(false))
        .take(dimension - (1 + c + nu))
        .chain(std::iter::once(Binding::Variable(0)))
        .chain((0..c).map(|i| Binding::Fixed(((column >> (c - 1 - i)) & 1) != 0)))
        .chain((1..=nu).map(Binding::Variable))
        .collect()
}

impl GateDescriptor {
    pub fn new(family: GateFamily, width: usize, degree: usize) -> Result<Self> {
        if width == 0 || !width.is_power_of_two() || width > 1024 || !(2..=256).contains(&degree) {
            return Err(
                "experiment gate requires power-of-two width<=1024 and degree in 2..256".into(),
            );
        }
        let (powers, output_column) = match family {
            GateFamily::PowerCopy => {
                if width < 2 {
                    return Err("power-copy gate needs at least two columns".into());
                }
                let mut powers = vec![0; width];
                powers[0] = degree;
                (vec![powers], 1)
            }
            GateFamily::Dense { terms } => {
                if width < 2 || terms == 0 || terms > 1024 {
                    return Err("dense gate requires width>=2 and 1..1024 terms".into());
                }
                let mut powers = Vec::new();
                compositions(degree, width - 1, &mut vec![], terms, &mut powers);
                if powers.len() != terms {
                    return Err("requested more distinct homogeneous monomials than this width/degree permits".into());
                }
                for p in &mut powers {
                    p.push(0);
                }
                (powers, width - 1)
            }
            GateFamily::SingleColumnBoolean => {
                if width != 1 {
                    return Err("single-column gate is a separate width-one relation".into());
                }
                (vec![vec![degree]], 0)
            }
        };
        let terms = powers
            .into_iter()
            .enumerate()
            .map(|(i, powers)| GateTerm {
                selector: format!("q{i}"),
                powers,
            })
            .collect();
        Ok(Self {
            family,
            width,
            degree,
            terms,
            output_column,
        })
    }
    pub fn family(&self) -> GateFamily {
        self.family
    }
    pub fn width(&self) -> usize {
        self.width
    }
    pub fn degree(&self) -> usize {
        self.degree
    }
    pub fn terms(&self) -> &[GateTerm] {
        &self.terms
    }
    pub fn output_column(&self) -> usize {
        self.output_column
    }
    pub fn selector_names(&self) -> Vec<String> {
        self.terms
            .iter()
            .map(|t| t.selector.clone())
            .chain(std::iter::once("qout".into()))
            .collect()
    }
    pub fn identity(&self) -> String {
        let family = match self.family {
            GateFamily::PowerCopy => "power-copy".to_owned(),
            GateFamily::Dense { terms } => format!("dense-{terms}"),
            GateFamily::SingleColumnBoolean => "single-column-boolean".to_owned(),
        };
        format!(
            "{family}:width={}:degree={}:homogeneous-desc-lex-v1",
            self.width, self.degree
        )
    }
    pub fn active_columns(&self) -> Vec<usize> {
        let mut columns: BTreeSet<_> = self
            .terms
            .iter()
            .flat_map(|t| {
                t.powers
                    .iter()
                    .enumerate()
                    .filter_map(|(a, e)| (*e > 0).then_some(a))
            })
            .collect();
        columns.insert(self.output_column);
        columns.into_iter().collect()
    }
    pub fn cost(&self) -> GateCost {
        let mut powers = 0;
        let mut products = 0;
        for t in &self.terms {
            let positive = t
                .powers
                .iter()
                .copied()
                .filter(|e| *e > 0)
                .collect::<Vec<_>>();
            for e in &positive {
                powers +=
                    (usize::BITS - 1 - e.leading_zeros()) as usize + e.count_ones() as usize - 1;
            }
            products += positive.len().saturating_sub(1);
        }
        GateCost {
            total_degree: self.degree,
            monomial_terms: self.terms.len(),
            selector_count: self.terms.len() + 1,
            active_columns: self.active_columns().len(),
            power_multiplications: powers,
            within_monomial_multiplications: products,
            selector_multiplications: self.terms.len(),
        }
    }
    pub fn row_value(
        &self,
        selectors: &BTreeMap<String, Vec<Fr>>,
        witness: &[Fr],
        n: usize,
        row: usize,
    ) -> Result<Fr> {
        if n == 0 || row >= n || witness.len() != n * self.width {
            return Err("gate row dimensions".into());
        }
        let mut total = Fr::zero();
        for t in &self.terms {
            let q = selectors
                .get(&t.selector)
                .and_then(|v| v.get(row))
                .ok_or("missing selector row")?;
            let value = t
                .powers
                .iter()
                .enumerate()
                .filter(|(_, e)| **e > 0)
                .fold(*q, |v, (a, e)| v * witness[a * n + row].pow([*e as u64]));
            total += value;
        }
        Ok(total
            - witness[self.output_column * n + row]
            - selectors
                .get("qout")
                .and_then(|v| v.get(row))
                .ok_or("missing qout row")?)
    }
    pub fn fixture(
        &self,
        nu: usize,
        input_seed: u64,
        fixed_first_column: bool,
    ) -> Result<GateFixture> {
        if nu >= usize::BITS as usize - 1 {
            return Err("fixture dimension overflow".into());
        }
        let n = 1usize << nu;
        let cells = n.checked_mul(self.width).ok_or("fixture size overflow")?;
        let mut rng = StdRng::seed_from_u64(input_seed);
        let mut selectors = BTreeMap::new();
        for (i, t) in self.terms.iter().enumerate() {
            selectors.insert(
                t.selector.clone(),
                (0..n)
                    .map(|row| {
                        if self.family == GateFamily::PowerCopy
                            || self.family == GateFamily::SingleColumnBoolean
                        {
                            Fr::one()
                        } else {
                            Fr::from((1 + i + 3 * (row / 2)) as u64)
                        }
                    })
                    .collect::<Vec<_>>(),
            );
        }
        selectors.insert("qout".into(), vec![Fr::zero(); n]);
        let mut witness = vec![Fr::zero(); cells];
        for a in 0..self.width {
            for row in (0..n).step_by(2) {
                let value = if self.family == GateFamily::SingleColumnBoolean {
                    Fr::from((rng.next_u32() & 1) as u64)
                } else if a == 0 && fixed_first_column {
                    Fr::from((11 + row / 2) as u64)
                } else {
                    sample_fr(&mut rng)?
                };
                witness[a * n + row] = value;
                if row + 1 < n {
                    witness[a * n + row + 1] = value;
                }
            }
        }
        if self.family != GateFamily::SingleColumnBoolean {
            for row in 0..n {
                let mut value = Fr::zero();
                for t in &self.terms {
                    value += t
                        .powers
                        .iter()
                        .enumerate()
                        .filter(|(_, e)| **e > 0)
                        .fold(selectors[&t.selector][row], |v, (a, e)| {
                            v * witness[a * n + row].pow([*e as u64])
                        });
                }
                witness[self.output_column * n + row] = value;
            }
        }
        let wiring = (0..cells).map(|i| if n == 1 { i } else { i ^ 1 }).collect();
        let mut digest = Sha256::new();
        digest.update(b"HP7-E4-application-input-v1\0");
        digest.update(self.identity());
        digest.update((nu as u64).to_be_bytes());
        digest.update(input_seed.to_be_bytes());
        digest.update([fixed_first_column as u8]);
        for x in &witness {
            digest.update(scalar_bytes(x));
        }
        Ok(GateFixture {
            selectors,
            wiring,
            witness,
            input_seed,
            instance_id: hex::encode(digest.finalize()),
        })
    }
    /// Build only the gate relation. Other core relations are shared unchanged.
    pub fn native_relation(&self, dimension: usize, nu: usize, c: usize) -> Result<NativeRelation> {
        if c >= usize::BITS as usize || self.width != 1usize << c || dimension < 1 + c + nu {
            return Err("native gate layout mismatch".into());
        }
        let mut relation = NativeRelation::new(nu + 1);
        let qmap = std::iter::repeat(Binding::Fixed(false))
            .take(dimension - nu)
            .chain((1..=nu).map(Binding::Variable))
            .collect::<Vec<_>>();
        let mut registered: BTreeMap<usize, Expr> = BTreeMap::new();
        let mut body = Expr::constant(0);
        for term in &self.terms {
            let mut product = relation.source(&term.selector, qmap.clone());
            for (column, power) in term.powers.iter().enumerate().filter(|(_, e)| **e > 0) {
                let w = if let Some(w) = registered.get(&column) {
                    w.clone()
                } else {
                    let w = relation.source("W", witness_map(dimension, nu, c, column));
                    registered.insert(column, w.clone());
                    w
                };
                product = product.times(if *power == 1 {
                    w
                } else {
                    w.power(*power as u64)
                });
            }
            body = body.plus(product);
        }
        let output = if let Some(w) = registered.get(&self.output_column) {
            w.clone()
        } else {
            relation.source("W", witness_map(dimension, nu, c, self.output_column))
        };
        relation.expression = Expr::constant(1)
            .minus(Expr::Variable(0))
            .times(body.minus(output).minus(relation.source("qout", qmap)));
        Ok(relation)
    }
}

fn indicator(map: &[Binding], public_prefix: usize) -> Expr {
    map[..public_prefix]
        .iter()
        .fold(Expr::constant(1), |value, b| {
            value.times(match b {
                Binding::Fixed(false) => Expr::constant(1),
                Binding::Fixed(true) => Expr::constant(0),
                Binding::Variable(a) => Expr::constant(1).minus(Expr::Variable(*a)),
                Binding::Complement(a) => Expr::Variable(*a),
            })
        })
}

fn substitute(expr: &Expr, replacements: &BTreeMap<usize, Expr>) -> Expr {
    match expr {
        Expr::Source(i) => replacements.get(i).cloned().unwrap_or_else(|| expr.clone()),
        Expr::Add(a, b) => substitute(a, replacements).plus(substitute(b, replacements)),
        Expr::Mul(a, b) => substitute(a, replacements).times(substitute(b, replacements)),
        Expr::Pow(a, e) => substitute(a, replacements).power(*e),
        _ => expr.clone(),
    }
}

/// Apply the same public compiler to every W use (including lookup if present).
/// Caller removes the independent public relation and must supply enlarged
/// virtual degree caps before SRS setup. The committed source remains PW.
pub fn virtualize_witness_uses(
    relations: &mut [NativeRelation],
    dimension: usize,
    public_log: usize,
) -> Result<()> {
    if public_log >= dimension {
        return Err("public suffix exceeds semantic witness slice".into());
    }
    for relation in relations {
        let uses = relation
            .sources
            .iter()
            .enumerate()
            .filter(|(_, s)| s.handle == "W")
            .map(|(i, s)| (i, s.map.clone()))
            .collect::<Vec<_>>();
        let mut replacements = BTreeMap::new();
        for (i, map) in uses {
            if map.len() != dimension {
                return Err("virtual witness mapping dimension".into());
            }
            let chi = indicator(&map, dimension - public_log);
            let public = relation.source("__public", map);
            replacements.insert(
                i,
                Expr::constant(1)
                    .minus(chi.clone())
                    .times(Expr::Source(i))
                    .plus(chi.times(public)),
            );
        }
        relation.expression = substitute(&relation.expression, &replacements);
    }
    Ok(())
}

pub fn semantic_witness(stored: &[Fr], public: &[Fr]) -> Result<Vec<Fr>> {
    if stored.is_empty()
        || !stored.len().is_power_of_two()
        || public.is_empty()
        || !public.len().is_power_of_two()
        || public.len() > stored.len()
    {
        return Err("invalid semantic public prefix".into());
    }
    let mut result = stored.to_vec();
    result[..public.len()].copy_from_slice(public);
    Ok(result)
}
