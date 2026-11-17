//! Reproducible application inputs for the formal experiment runner.
//! StdRng is used ONLY to sample application inputs. Protocol masks, commitment
//! blinds and opening randomness remain the caller's separate OsRng stream.
use crate::{
    codec::scalar_bytes,
    index::{self, Gate, IndexSpec, LookupIndexSpec},
    lookup::{LookupFunction, PrimitiveCycle},
    profile::ValidatedProfile,
    Result,
};
use ark_bls12_381::Fr;
use ark_ff::Field;
use rand::{rngs::StdRng, Rng, SeedableRng};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

fn one() -> usize {
    1
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupWorkload {
    pub distinct: usize,
    pub distribution: String,
    pub include_zero: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct WorkloadConfig {
    pub nu: usize,
    pub c: usize,
    pub public_log: usize,
    pub degree: usize,
    #[serde(default)]
    pub anchor: Option<usize>,
    pub flags: u64,
    pub gate: String,
    #[serde(default = "one")]
    pub dense_terms: usize,
    #[serde(default)]
    pub lookup: Option<LookupWorkload>,
    #[serde(default)]
    pub input_seed: u64,
}

pub struct Instance {
    pub spec: IndexSpec,
    pub witness: Vec<Fr>,
    pub public: Vec<Fr>,
    pub instance_id: String,
    /// Hash only the actual witness values, so repeated identical fixtures are
    /// not mistaken for distinct input values merely because seeds differ.
    pub witness_id: String,
    pub seed: u64,
    /// Public circuit/lookup definition hash, excluding witness and public input.
    /// The runner can compare this before reusing a previously certified index.
    pub definition_id: String,
    /// ReferencePower is a deterministic correctness fixture, not an independent
    /// application-input sampling family. Other families may have degenerate
    /// distributions, e.g. a lookup table containing only a single value.
    pub samples_application_inputs: bool,
}

impl WorkloadConfig {
    pub fn gate(&self) -> Result<Gate> {
        match self.gate.as_str() {
            "reference" | "diagonal" | "reference-power" => Ok(Gate::ReferencePower),
            "fixed13" | "fixed-thirteen" => Ok(Gate::FixedThirteen),
            "power" | "power-copy" => Ok(Gate::PowerCopy),
            "dense" => Ok(Gate::Dense {
                terms: self.dense_terms,
            }),
            "single" | "single-column-boolean" => Ok(Gate::SingleColumnBoolean),
            name if name.starts_with("dense-") => {
                let terms = name[6..]
                    .parse::<usize>()
                    .map_err(|_| "invalid dense gate term count")?;
                if self.dense_terms != 1 && self.dense_terms != terms {
                    return Err("dense gate name and dense_terms disagree".into());
                }
                Ok(Gate::Dense { terms })
            }
            _ => Err("unknown workload gate".into()),
        }
    }
    pub fn profile(&self) -> Result<ValidatedProfile> {
        let p = ValidatedProfile::from_flags(
            self.nu,
            self.c,
            self.public_log,
            self.degree,
            self.anchor,
            self.flags,
        )?;
        let gate = self.gate()?;
        if (self.lookup.is_some()) != p.lookup() {
            return Err("lookup config and profile flag disagree".into());
        }
        if gate == Gate::FixedThirteen && (p.k() != 8 || p.degree() != 5) {
            return Err("fixed13 workload requires width=8, degree=5".into());
        }
        gate.descriptor(&p)?;
        if let Some(lk) = &self.lookup {
            if lk.distinct == 0 || lk.distinct > p.n() - 1 {
                return Err("lookup distinct count must be in 1..n-1".into());
            }
            if !matches!(lk.distribution.as_str(), "uniform" | "skewed") {
                return Err("lookup distribution must be uniform or skewed".into());
            }
            match gate {
                Gate::PowerCopy if p.k() >= 2 => {}
                Gate::SingleColumnBoolean if p.k() == 1 => {
                    if lk.distinct > 2 || (!lk.include_zero && lk.distinct > 1) {
                        return Err(
                            "single-column lookup table must contain only Boolean values".into(),
                        );
                    }
                }
                _ => return Err(
                    "fixed-table lookup workload supports power-copy or single-column-boolean only"
                        .into(),
                ),
            }
        }
        Ok(p)
    }
    /// `seed` overrides the template's input_seed for this instance. The seed
    /// belongs to application input generation and is safe to record publicly.
    pub fn instance(&self, seed: u64) -> Result<Instance> {
        let p = self.profile()?;
        let gate = self.gate()?;
        let (mut spec, mut witness) = index::gate_fixture(&p, gate, seed)?;
        if let Some(lk) = &self.lookup {
            let offset = usize::from(!lk.include_zero);
            let table = (0..p.n() - 1)
                .map(|i| Fr::from((offset + i % lk.distinct) as u64))
                .collect::<Vec<_>>();
            let mut hash = Sha256::new();
            hash.update(b"HP-workload-targets-v1\0");
            hash.update(seed.to_be_bytes());
            hash.update(serde_json::to_vec(self).map_err(|e| e.to_string())?);
            let mut target_rng = StdRng::from_seed(hash.finalize().into());
            let function = if p.k() >= 4 {
                LookupFunction::SumColumns
            } else {
                LookupFunction::FirstColumn
            };
            for row in (0..p.n()).step_by(2) {
                // Uniform means uniform over distinct values, not over physical
                // duplicate entries. Skewed puts 80% on the first value plus
                // a 20% uniform component (including that first value).
                let address = if lk.distribution == "skewed" && target_rng.gen_ratio(4, 5) {
                    0
                } else {
                    target_rng.gen_range(0..lk.distinct)
                };
                let target = Fr::from((offset + address) as u64);
                for r in row..(row + 2).min(p.n()) {
                    match function {
                        LookupFunction::SumColumns => {
                            // PowerCopy uses only W0,W1. The final column is
                            // unconstrained by the gate and balances the sum.
                            let total: Fr = (0..p.k() - 1).map(|a| witness[a * p.n() + r]).sum();
                            witness[(p.k() - 1) * p.n() + r] = target - total;
                        }
                        LookupFunction::FirstColumn => {
                            witness[r] = target;
                            if p.k() == 2 {
                                witness[p.n() + r] = target.pow([p.degree() as u64]);
                            }
                        }
                    }
                }
            }
            spec.lookup = Some(LookupIndexSpec {
                physical_table: table,
                function,
            });
        }
        let public = witness[..1 << p.public_log()].to_vec();
        let definition_id = definition_id(&p, &spec)?;
        let mut witness_hash = Sha256::new();
        witness_hash.update(b"HP-workload-witness-values-v1\0");
        witness_hash.update((witness.len() as u64).to_be_bytes());
        for v in &witness {
            witness_hash.update(scalar_bytes(v));
        }
        let witness_id = hex::encode(witness_hash.finalize());
        let mut identity = Sha256::new();
        identity.update(b"HP-workload-instance-v1\0");
        let config = serde_json::to_vec(self).map_err(|e| e.to_string())?;
        identity.update((config.len() as u64).to_be_bytes());
        identity.update(config);
        identity.update(seed.to_be_bytes());
        identity.update(&definition_id);
        identity.update(&witness_id);
        identity.update((public.len() as u64).to_be_bytes());
        for v in &public {
            identity.update(scalar_bytes(v));
        }
        Ok(Instance {
            spec,
            witness,
            public,
            instance_id: hex::encode(identity.finalize()),
            witness_id,
            seed,
            definition_id,
            samples_application_inputs: gate != Gate::ReferencePower,
        })
    }
    pub fn configured_instance(&self) -> Result<Instance> {
        self.instance(self.input_seed)
    }
}

/// No group secrets are used. This digest authenticates definitions for local
/// index reuse bookkeeping; it is not a replacement for SRS-backed certification.
pub fn definition_id(p: &ValidatedProfile, spec: &IndexSpec) -> Result<String> {
    let mut h = Sha256::new();
    h.update(b"HP-workload-public-definition-v1\0");
    h.update((p.profile_id().len() as u64).to_be_bytes());
    h.update(p.profile_id().as_bytes());
    hash_relation_tables(h, p, spec)
}

fn hash_relation_tables(mut h: Sha256, p: &ValidatedProfile, spec: &IndexSpec) -> Result<String> {
    fn bytes(h: &mut Sha256, v: &[u8]) {
        h.update((v.len() as u64).to_be_bytes());
        h.update(v);
    }
    bytes(&mut h, spec.gate.name().as_bytes());
    h.update((spec.selectors.len() as u64).to_be_bytes());
    for (name, table) in &spec.selectors {
        bytes(&mut h, name.as_bytes());
        h.update((table.len() as u64).to_be_bytes());
        for v in table {
            h.update(scalar_bytes(v));
        }
    }
    h.update((spec.wiring.len() as u64).to_be_bytes());
    for i in &spec.wiring {
        h.update((*i as u64).to_be_bytes());
    }
    match &spec.lookup {
        None => h.update([0]),
        Some(lk) => {
            h.update([1]);
            bytes(&mut h, lk.function.name().as_bytes());
            h.update(PrimitiveCycle::new(p.nu())?.polynomial().to_be_bytes());
            h.update(PrimitiveCycle::new(p.nu() + 1)?.polynomial().to_be_bytes());
            h.update((lk.physical_table.len() as u64).to_be_bytes());
            for v in &lk.physical_table {
                h.update(scalar_bytes(v));
            }
        }
    }
    Ok(hex::encode(h.finalize()))
}

/// Compact, serializable input-generation metadata; no private prover coins.
pub fn metadata(
    config: &WorkloadConfig,
    instance: &Instance,
) -> Result<BTreeMap<String, serde_json::Value>> {
    let mut out = BTreeMap::new();
    let p = config.profile()?;
    let mut relation = Sha256::new();
    relation.update(b"HP-matched-circuit-v1\0");
    for parameter in [p.nu(), p.c(), p.public_log(), p.degree()] {
        relation.update((parameter as u64).to_be_bytes());
    }
    out.insert(
        "relation_id".into(),
        hash_relation_tables(relation, &p, &instance.spec)?.into(),
    );
    let mut public = Sha256::new();
    public.update(b"HP-matched-public-input-v1\0");
    public.update((instance.public.len() as u64).to_be_bytes());
    for value in &instance.public {
        public.update(scalar_bytes(value));
    }
    out.insert(
        "public_input_id".into(),
        hex::encode(public.finalize()).into(),
    );
    out.insert(
        "config".into(),
        serde_json::to_value(config).map_err(|e| e.to_string())?,
    );
    out.insert("instance_id".into(), instance.instance_id.clone().into());
    out.insert("witness_id".into(), instance.witness_id.clone().into());
    out.insert(
        "definition_id".into(),
        instance.definition_id.clone().into(),
    );
    out.insert("input_seed".into(), instance.seed.into());
    out.insert(
        "samples_application_inputs".into(),
        instance.samples_application_inputs.into(),
    );
    if let Some(lk) = &instance.spec.lookup {
        out.insert("lookup_function".into(), lk.function.name().into());
    }
    Ok(out)
}
