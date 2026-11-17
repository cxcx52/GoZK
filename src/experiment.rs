//! Shared experiment contract. Seeds describe public application generation;
//! secret prover randomness always comes from a separate OsRng.
use crate::{workload::WorkloadConfig, Result};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::path::Path;
fn default_threads() -> usize {
    1
}
fn default_repeats() -> usize {
    10
}
fn default_engine() -> String {
    "cached".into()
}
fn default_cap() -> usize {
    1 << 26
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExperimentConfig {
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub ablation: bool,
    pub workload: WorkloadConfig,
    #[serde(default = "default_threads")]
    pub threads: usize,
    #[serde(default = "default_repeats")]
    pub repeats: usize,
    #[serde(default = "default_engine")]
    pub engine: String,
    #[serde(default)]
    pub seed_start: u64,
    #[serde(default)]
    pub label: String,
    #[serde(default = "default_cap")]
    pub max_primary_points: usize,
}
impl ExperimentConfig {
    pub fn read(path: impl AsRef<Path>) -> Result<Self> {
        let result: Self = serde_json::from_slice(&std::fs::read(path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        result.validate()?;
        Ok(result)
    }
    pub fn validate(&self) -> Result<()> {
        if self.ablation
            && (self.workload.gate()? != crate::index::Gate::FixedThirteen
                || self.repeats != 1
                || self.workload.public_log != self.workload.nu
                || self.workload.anchor != Some(3)
                || !matches!(
                    (self.engine.as_str(), self.workload.flags),
                    ("cached", 0 | 8) | ("multi" | "total", 0)
                ))
        {
            return Err("ablation requires a single matched fixed13 run in a certified arm".into());
        }
        if !(1..=18).contains(&self.threads) || !(1..=100).contains(&self.repeats) {
            return Err("experiment threads/repeats outside declared budget".into());
        }
        if !matches!(
            self.engine.as_str(),
            "cached" | "direct" | "trace" | "multi" | "total"
        ) {
            return Err("unknown experiment engine".into());
        }
        if self.engine == "total" && !self.ablation {
            return Err("the total-sum helper control requires an ablation configuration".into());
        }
        if self.max_primary_points > 1 << 27 {
            return Err("experiment point allocation cap exceeds reviewed limit".into());
        }
        let p = self.workload.profile()?;
        if p.v_count()
            .checked_add(p.u_count())
            .ok_or("point count overflow")?
            > self.max_primary_points
        {
            return Err("experiment SRS allocation cap exceeded".into());
        }
        self.seed_start
            .checked_add(self.repeats as u64)
            .ok_or("input seed overflow")?;
        Ok(())
    }
}
pub fn current_executable_sha256() -> Result<String> {
    use std::io::Read;
    let mut f = std::fs::File::open(std::env::current_exe().map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let mut h = Sha256::new();
    let mut block = [0u8; 65536];
    loop {
        let n = f.read(&mut block).map_err(|e| e.to_string())?;
        if n == 0 {
            break;
        }
        h.update(&block[..n]);
    }
    Ok(hex::encode(h.finalize()))
}
pub fn cargo_lock_sha256() -> String {
    hex::encode(Sha256::digest(include_bytes!("../Cargo.lock")))
}
pub fn provenance() -> Result<serde_json::Value> {
    Ok(serde_json::json!({
        "binary_sha256":current_executable_sha256()?,"cargo_lock_sha256":cargo_lock_sha256(),
        "source_manifest_sha256":std::env::var("HP_SOURCE_MANIFEST_SHA256").ok(),
        "git_commit":std::env::var("HP_GIT_COMMIT").ok(),
        "parallel_feature":cfg!(feature="parallel"),
        "logical_cpus_available":std::thread::available_parallelism().map(|x|x.get()).unwrap_or(0)
    }))
}
