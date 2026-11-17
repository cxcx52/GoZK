//! Index certification is an offline operation. A ValidatedIndex is constructed
//! only from checked Boolean definitions and commitments recomputed with the
//! public SRS. Hashing supplied definitions alone is not certification.
use crate::{
    codec::{g2_bytes, scalar_bytes},
    pcs::{commit_source, PublicSrs},
    profile::ValidatedProfile,
    random::sample_fr,
    tables::{DenseMle, StructuredPolynomial},
    Result,
};
use crate::{
    gates::{GateDescriptor, GateFamily},
    lookup::{LookupFunction, PrimitiveCycle},
};
use ark_bls12_381::{Fr, G2Affine};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use num_bigint::BigUint;
use rand::RngCore;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Gate {
    ReferencePower,
    FixedThirteen,
    PowerCopy,
    Dense { terms: usize },
    SingleColumnBoolean,
}
impl Gate {
    pub fn name(self) -> String {
        match self {
            Self::ReferencePower => "reference-power".into(),
            Self::FixedThirteen => "fixed-thirteen".into(),
            Self::PowerCopy => "power-copy".into(),
            Self::Dense { terms } => format!("dense-{terms}"),
            Self::SingleColumnBoolean => "single-column-boolean".into(),
        }
    }
    pub fn descriptor(self, p: &ValidatedProfile) -> Result<Option<GateDescriptor>> {
        let family = match self {
            Self::PowerCopy => GateFamily::PowerCopy,
            Self::Dense { terms } => GateFamily::Dense { terms },
            Self::SingleColumnBoolean => GateFamily::SingleColumnBoolean,
            _ => return Ok(None),
        };
        Ok(Some(GateDescriptor::new(family, p.k(), p.degree())?))
    }
}

pub struct LookupIndexSpec {
    pub physical_table: Vec<Fr>,
    pub function: LookupFunction,
}
pub struct CertifiedLookup {
    pub physical_table: Vec<Fr>,
    pub function: LookupFunction,
    pub table_cycle: PrimitiveCycle,
    pub h_cycle: PrimitiveCycle,
}

pub struct IndexSpec {
    pub gate: Gate,
    pub selectors: BTreeMap<String, Vec<Fr>>,
    pub wiring: Vec<usize>,
    pub lookup: Option<LookupIndexSpec>,
}
pub struct ValidatedIndex {
    gate: Gate,
    profile_id: String,
    srs_id: [u8; 32],
    digest: [u8; 32],
    polynomials: BTreeMap<String, StructuredPolynomial>,
    commitments: BTreeMap<String, G2Affine>,
    wiring: Vec<usize>,
    lookup: Option<CertifiedLookup>,
}
impl ValidatedIndex {
    pub fn certify(srs: &PublicSrs, spec: IndexSpec) -> Result<Self> {
        let p = srs.profile();
        if spec.gate == Gate::FixedThirteen && (p.k() != 8 || p.degree() != 5) {
            return Err("13-selector gate requires k=8, degree=5".into());
        }
        let count = if let Some(descriptor) = spec.gate.descriptor(p)? {
            descriptor.terms().len()
        } else if spec.gate == Gate::FixedThirteen {
            12
        } else {
            p.k()
        };
        let expected = (0..count)
            .map(|i| format!("q{i}"))
            .chain(std::iter::once("qout".into()))
            .collect::<std::collections::BTreeSet<_>>();
        if spec
            .selectors
            .keys()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>()
            != expected
            || spec.selectors.values().any(|t| t.len() != p.n())
        {
            return Err("selector shape or handles mismatch".into());
        }
        if spec.wiring.len() != p.n_total() {
            return Err("wiring length mismatch".into());
        }
        let mut seen = vec![false; p.n_total()];
        for label in &spec.wiring {
            if *label >= seen.len() || seen[*label] {
                return Err("wiring is not a permutation".into());
            }
            seen[*label] = true;
        }
        let mut polynomials = BTreeMap::new();
        for (name, table) in &spec.selectors {
            polynomials.insert(
                name.clone(),
                StructuredPolynomial::from_table(
                    p.l(),
                    p.l() - p.nu(),
                    DenseMle::new(table.clone())?,
                )?,
            );
        }
        polynomials.insert(
            "sigma".into(),
            StructuredPolynomial::from_table(
                p.l(),
                p.core_offset() + 1,
                DenseMle::new(spec.wiring.iter().map(|i| Fr::from(*i as u64)).collect())?,
            )?,
        );
        let lookup = match spec.lookup {
            None => {
                if p.lookup() {
                    return Err("lookup profile requires a public table".into());
                }
                None
            }
            Some(raw) => {
                if !p.lookup() || raw.physical_table.len() != p.n() - 1 {
                    return Err("lookup public table/profile mismatch".into());
                }
                let table_cycle = PrimitiveCycle::new(p.nu())?;
                let h_cycle = PrimitiveCycle::new(p.nu() + 1)?;
                polynomials.insert(
                    "table".into(),
                    StructuredPolynomial::from_table(
                        p.l(),
                        p.l() - p.nu(),
                        DenseMle::new(table_cycle.embed(&raw.physical_table)?)?,
                    )?,
                );
                Some(CertifiedLookup {
                    physical_table: raw.physical_table,
                    function: raw.function,
                    table_cycle,
                    h_cycle,
                })
            }
        };
        let mut commitments = BTreeMap::new();
        for (name, poly) in &polynomials {
            commitments.insert(name.clone(), commit_source(srs, poly, Fr::zero())?);
        }
        let srs_id = srs.vk().srs_digest;
        let mut digest = Sha256::new();
        digest.update(b"HP7-Rust-certified-index-v1\0");
        digest.update(srs_id);
        digest.update(p.profile_id());
        digest.update(spec.gate.name());
        for (name, table) in &spec.selectors {
            digest.update((name.len() as u64).to_be_bytes());
            digest.update(name);
            digest.update((table.len() as u64).to_be_bytes());
            for x in table {
                digest.update(scalar_bytes(x));
            }
        }
        for label in &spec.wiring {
            digest.update((*label as u64).to_be_bytes());
        }
        if let Some(lk) = &lookup {
            digest.update(b"lookup-index-v1\0");
            digest.update(lk.function.name());
            digest.update(lk.table_cycle.polynomial().to_be_bytes());
            digest.update(lk.h_cycle.polynomial().to_be_bytes());
            for v in &lk.physical_table {
                digest.update(scalar_bytes(v));
            }
        }
        for (name, c) in &commitments {
            digest.update(name);
            digest.update(g2_bytes(c));
        }
        Ok(Self {
            gate: spec.gate,
            profile_id: p.profile_id().to_owned(),
            srs_id,
            digest: digest.finalize().into(),
            polynomials,
            commitments,
            wiring: spec.wiring,
            lookup,
        })
    }
    pub fn gate(&self) -> Gate {
        self.gate
    }
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }
    pub fn srs_id(&self) -> [u8; 32] {
        self.srs_id
    }
    pub fn polynomials(&self) -> &BTreeMap<String, StructuredPolynomial> {
        &self.polynomials
    }
    pub fn commitments(&self) -> &BTreeMap<String, G2Affine> {
        &self.commitments
    }
    pub fn wiring(&self) -> &[usize] {
        &self.wiring
    }
    pub fn lookup(&self) -> Option<&CertifiedLookup> {
        self.lookup.as_ref()
    }
    pub fn matches(&self, p: &ValidatedProfile, srs_id: &[u8; 32]) -> bool {
        self.profile_id == p.profile_id() && &self.srs_id == srs_id
    }
}

pub fn reference_fixture(p: &ValidatedProfile) -> (IndexSpec, Vec<Fr>) {
    let witness = (0..p.n_total())
        .map(|i| Fr::from((3 + 7 * (i / p.n()) + 2 * ((i % p.n()) / 2)) as u64))
        .collect::<Vec<_>>();
    let mut selectors: BTreeMap<String, Vec<Fr>> = (0..p.k())
        .map(|a| {
            (
                format!("q{a}"),
                (0..p.n())
                    .map(|row| Fr::from((1 + a + row) as u64))
                    .collect(),
            )
        })
        .collect();
    let qout = (0..p.n())
        .map(|row| {
            (0..p.k())
                .map(|a| {
                    selectors[&format!("q{a}")][row]
                        * witness[a * p.n() + row].pow([p.degree() as u64])
                })
                .sum()
        })
        .collect();
    selectors.insert("qout".into(), qout);
    (
        IndexSpec {
            gate: Gate::ReferencePower,
            selectors,
            wiring: (0..p.n_total())
                .map(|i| if p.n() > 1 { i ^ 1 } else { i })
                .collect(),
            lookup: None,
        },
        witness,
    )
}

/// Circuit is fixed before the witness. W0 is fixed across instances so the
/// default public slice (<= n) is also fixed; W1..W6 vary independently by pair.
pub fn fixed_thirteen_fixture(
    p: &ValidatedProfile,
    rng: &mut impl RngCore,
) -> Result<(IndexSpec, Vec<Fr>)> {
    if p.k() != 8 || p.degree() != 5 {
        return Err("fixed gate dimensions".into());
    }
    let selectors: BTreeMap<String, Vec<Fr>> = (0..13)
        .map(|a| {
            (
                (if a == 12 {
                    "qout".into()
                } else {
                    format!("q{a}")
                }),
                (0..p.n())
                    .map(|row| Fr::from((1 + a + 3 * (row / 2)) as u64))
                    .collect(),
            )
        })
        .collect();
    let mut w = vec![Fr::zero(); p.n_total()];
    for a in 0..7 {
        for row in (0..p.n()).step_by(2) {
            let x = if a == 0 {
                Fr::from((9 + row / 2) as u64)
            } else {
                sample_fr(rng)?
            };
            w[a * p.n() + row] = x;
            if row + 1 < p.n() {
                w[a * p.n() + row + 1] = x;
            }
        }
    }
    let q = BigUint::from_bytes_be(&Fr::MODULUS.to_bytes_be());
    let e = (q * BigUint::from(2u64) - BigUint::from(1u64)) / BigUint::from(5u64);
    let exponent = e.to_u64_digits();
    for row in 0..p.n() {
        let mut rest: Fr = (0..7)
            .map(|a| selectors[&format!("q{a}")][row] * w[a * p.n() + row].pow([5]))
            .sum();
        for (i, (a, b)) in [(0, 1), (2, 3), (4, 5), (0, 6)].iter().enumerate() {
            rest +=
                selectors[&format!("q{}", 8 + i)][row] * w[a * p.n() + row] * w[b * p.n() + row];
        }
        let rhs = (selectors["qout"][row] - rest)
            * selectors["q7"][row].inverse().ok_or("zero fixed q7")?;
        let value = rhs.pow(exponent.as_slice());
        if value.pow([5]) != rhs {
            return Err("fifth-root generation mismatch".into());
        }
        w[7 * p.n() + row] = value;
    }
    Ok((
        IndexSpec {
            gate: Gate::FixedThirteen,
            selectors,
            wiring: (0..p.n_total())
                .map(|i| if p.n() > 1 { i ^ 1 } else { i })
                .collect(),
            lookup: None,
        },
        w,
    ))
}

pub fn gate_fixture(
    p: &ValidatedProfile,
    gate: Gate,
    input_seed: u64,
) -> Result<(IndexSpec, Vec<Fr>)> {
    if gate == Gate::ReferencePower {
        return Ok(reference_fixture(p));
    }
    if gate == Gate::FixedThirteen {
        use rand::SeedableRng;
        return fixed_thirteen_fixture(p, &mut rand::rngs::StdRng::seed_from_u64(input_seed));
    }
    let fixture = gate
        .descriptor(p)?
        .ok_or("missing experiment gate")?
        .fixture(p.nu(), input_seed, false)?;
    Ok((
        IndexSpec {
            gate,
            selectors: fixture.selectors,
            wiring: fixture.wiring,
            lookup: None,
        },
        fixture.witness,
    ))
}

/// Correctness fixture helper: derive a public table containing all queries.
/// This may change the index with the input and is not a fixed-table benchmark.
pub fn attach_lookup(
    mut spec: IndexSpec,
    p: &ValidatedProfile,
    witness: &[Fr],
    function: LookupFunction,
) -> Result<IndexSpec> {
    if !p.lookup() || witness.len() != p.n_total() {
        return Err("lookup fixture dimensions".into());
    }
    let mut unique = BTreeMap::new();
    for row in 0..p.n() {
        let v = match function {
            LookupFunction::FirstColumn => witness[row],
            LookupFunction::SumColumns => (0..p.k()).map(|a| witness[a * p.n() + row]).sum(),
        };
        unique.entry(scalar_bytes(&v)).or_insert(v);
    }
    if unique.len() > p.n() - 1 {
        return Err("query fixture has more distinct values than physical lookup table".into());
    }
    let mut physical_table = unique.into_values().collect::<Vec<_>>();
    physical_table.resize(p.n() - 1, Fr::zero());
    spec.lookup = Some(LookupIndexSpec {
        physical_table,
        function,
    });
    Ok(spec)
}
