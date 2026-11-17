//! Boolean evaluation tables and structured, prefix-substitution quotients.
//! Axis zero is the most significant Boolean bit. No monomial expansion of a
//! dense table occurs in this module.

use crate::Result;
use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DenseMle {
    dimension: usize,
    values: Arc<[Fr]>,
}

impl DenseMle {
    pub fn new(values: Vec<Fr>) -> Result<Self> {
        if values.is_empty() || !values.len().is_power_of_two() {
            return Err("MLE table length must be a positive power of two".into());
        }
        Ok(Self {
            dimension: values.len().trailing_zeros() as usize,
            values: values.into(),
        })
    }
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    pub fn values(&self) -> &[Fr] {
        &self.values
    }
    /// Process-local identity of immutable backing storage. A cache using this
    /// value must retain a clone of the table to prevent allocator reuse.
    pub(crate) fn storage_id(&self) -> usize {
        self.values.as_ptr() as usize
    }
    pub fn evaluate(&self, point: &[Fr]) -> Result<Fr> {
        if point.len() != self.dimension {
            return Err("MLE point dimension mismatch".into());
        }
        let mut view = self.fold_view();
        for x in point {
            view.fold(*x)?;
        }
        Ok(view.values()[0])
    }
    /// A mutable folding buffer, allocated once per independent fold path.
    pub fn fold_view(&self) -> FoldView {
        FoldView {
            values: self.values.to_vec(),
            remaining: self.dimension,
            work: FoldWork::default(),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FoldWork {
    /// Each pair reads two values and computes their difference and interpolation.
    pub pairs: usize,
    /// Number of field cells materialized in quotient tables.
    pub quotient_cells: usize,
}

#[derive(Clone, Debug)]
pub struct FoldView {
    values: Vec<Fr>,
    remaining: usize,
    work: FoldWork,
}

impl FoldView {
    pub fn values(&self) -> &[Fr] {
        &self.values
    }
    pub fn remaining(&self) -> usize {
        self.remaining
    }
    pub fn work(&self) -> FoldWork {
        self.work
    }
    pub fn fold(&mut self, coordinate: Fr) -> Result<()> {
        if self.remaining == 0 {
            return Err("cannot fold a scalar table".into());
        }
        let half = self.values.len() / 2;
        crate::parallel::fold_pairs(&mut self.values, coordinate, None);
        self.values.truncate(half);
        self.remaining -= 1;
        self.work.pairs += half;
        Ok(())
    }
    /// Evaluate one current coordinate and a Boolean suffix with O(1) table access.
    pub fn at_current(&self, coordinate: Fr, suffix_index: usize) -> Result<Fr> {
        if self.remaining == 0 || suffix_index >= self.values.len() / 2 {
            return Err("fold view suffix outside table".into());
        }
        let half = self.values.len() / 2;
        Ok(self.values[suffix_index]
            + coordinate * (self.values[half + suffix_index] - self.values[suffix_index]))
    }
}

/// The table occupies consecutive axes [start,start+dimension); other axes
/// are absent, rather than multiplied by a zero-prefix selector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MleTerm {
    pub start: usize,
    pub table: DenseMle,
    pub scale: Fr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuredPolynomial {
    dimension: usize,
    terms: Vec<MleTerm>,
    extras: BTreeMap<Vec<usize>, Fr>,
}

impl StructuredPolynomial {
    pub fn new(
        dimension: usize,
        terms: Vec<MleTerm>,
        extras: BTreeMap<Vec<usize>, Fr>,
    ) -> Result<Self> {
        if dimension == 0 {
            return Err("structured polynomial dimension must be positive".into());
        }
        if terms.iter().any(|t| {
            t.start
                .checked_add(t.table.dimension())
                .map_or(true, |end| end > dimension)
        }) {
            return Err("embedded table exceeds polynomial dimension".into());
        }
        if extras
            .keys()
            .any(|e| e.len() != dimension || e.iter().any(|d| *d > u64::MAX as usize))
        {
            return Err("invalid monomial dimension or exponent".into());
        }
        Ok(Self {
            dimension,
            terms: terms.into_iter().filter(|t| !t.scale.is_zero()).collect(),
            extras: extras.into_iter().filter(|(_, c)| !c.is_zero()).collect(),
        })
    }
    pub fn zero(dimension: usize) -> Result<Self> {
        Self::new(dimension, vec![], BTreeMap::new())
    }
    pub fn from_table(dimension: usize, start: usize, table: DenseMle) -> Result<Self> {
        Self::new(
            dimension,
            vec![MleTerm {
                start,
                table,
                scale: Fr::one(),
            }],
            BTreeMap::new(),
        )
    }
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    pub fn terms(&self) -> &[MleTerm] {
        &self.terms
    }
    pub fn extras(&self) -> &BTreeMap<Vec<usize>, Fr> {
        &self.extras
    }
    pub fn evaluate(&self, point: &[Fr]) -> Result<Fr> {
        if point.len() != self.dimension {
            return Err("structured point dimension mismatch".into());
        }
        let mut value = Fr::zero();
        for term in &self.terms {
            value += term.scale
                * term
                    .table
                    .evaluate(&point[term.start..term.start + term.table.dimension()])?;
        }
        for (exponents, coefficient) in &self.extras {
            let mut monomial = *coefficient;
            for (x, e) in point.iter().zip(exponents) {
                monomial *= x.pow([*e as u64]);
            }
            value += monomial;
        }
        Ok(value)
    }
    pub fn scaled(&self, scalar: Fr) -> Self {
        if scalar.is_zero() {
            return Self {
                dimension: self.dimension,
                terms: vec![],
                extras: BTreeMap::new(),
            };
        }
        Self {
            dimension: self.dimension,
            terms: self
                .terms
                .iter()
                .map(|t| MleTerm {
                    start: t.start,
                    table: t.table.clone(),
                    scale: t.scale * scalar,
                })
                .collect(),
            extras: self
                .extras
                .iter()
                .map(|(e, c)| (e.clone(), *c * scalar))
                .collect(),
        }
    }
    pub fn add(&self, other: &Self) -> Result<Self> {
        if self.dimension != other.dimension {
            return Err("polynomial addition dimension mismatch".into());
        }
        let mut terms = self.terms.clone();
        terms.extend(other.terms.iter().cloned());
        let mut extras = self.extras.clone();
        for (e, c) in &other.extras {
            *extras.entry(e.clone()).or_default() += c;
        }
        Self::new(self.dimension, terms, extras)
    }
    /// Return f(z), then q_i with f(X)-f(z)=sum_i (X_i-z_i)q_i(X).
    /// The q_i depend only on coordinates i..L-1. A dense table of size n
    /// contributes exactly n-1 pairs and n-1 quotient cells across all axes.
    /// Extras are telescoped separately; no division by a point coordinate.
    pub fn canonical_quotients(&self, point: &[Fr]) -> Result<(Fr, Vec<Self>, FoldWork)> {
        if point.len() != self.dimension {
            return Err("quotient point dimension mismatch".into());
        }
        let mut quotients = (0..self.dimension)
            .map(|_| Self::zero(self.dimension))
            .collect::<Result<Vec<_>>>()?;
        let mut value = Fr::zero();
        let mut work = FoldWork::default();
        for term in &self.terms {
            let mut row = term.table.values().to_vec();
            for axis in term.start..term.start + term.table.dimension() {
                let half = row.len() / 2;
                let mut difference = vec![Fr::zero(); half];
                crate::parallel::fold_pairs(&mut row, point[axis], Some(&mut difference));
                row.truncate(half);
                quotients[axis].terms.push(MleTerm {
                    start: axis + 1,
                    table: DenseMle::new(difference)?,
                    scale: term.scale,
                });
                work.pairs += half;
                work.quotient_cells += half;
            }
            value += term.scale * row[0];
        }
        for (exponents, coefficient) in &self.extras {
            let mut prefix = *coefficient;
            for axis in 0..self.dimension {
                let degree = exponents[axis];
                // Accumulate descending powers so the scalar recurrence costs
                // degree multiplications, not repeated modular exponentiation.
                let mut scalar = prefix;
                for power in (0..degree).rev() {
                    let mut exponent = exponents.clone();
                    exponent[..axis].fill(0);
                    exponent[axis] = power;
                    *quotients[axis].extras.entry(exponent).or_default() += scalar;
                    scalar *= point[axis];
                }
                prefix = scalar;
            }
            value += prefix;
        }
        for quotient in &mut quotients {
            quotient.extras.retain(|_, c| !c.is_zero());
        }
        Ok((value, quotients, work))
    }
    /// Number of dense cells represented, with shared backing storage counted
    /// per term. Use this as a work ledger, not as allocator/RSS measurement.
    pub fn table_cells(&self) -> usize {
        self.terms.iter().map(|t| t.table.values().len()).sum()
    }
}
