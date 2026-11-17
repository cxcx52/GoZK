//! Formal experiment driver. SRS setup is a distinct process; repeated online
//! measurements reuse one checked SRS and one certified, fixed public circuit.
use hyperplonk_repair::{
    codec::{g2_bytes, scalar_bytes},
    experiment::{self, ExperimentConfig},
    general_mask,
    index::ValidatedIndex,
    multi,
    pcs::PublicSrs,
    protocol, resources,
    workload::{self, Instance},
    Result,
};
use rand::rngs::OsRng;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{
    env,
    fs::{File, OpenOptions},
    io::{BufReader, Write},
    path::Path,
    time::Instant,
};

fn new_output(path: &str) -> Result<File> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|e| e.to_string())
}
fn record(out: &mut File, value: &Value) -> Result<()> {
    serde_json::to_writer(&mut *out, value).map_err(|e| e.to_string())?;
    out.write_all(b"\n").map_err(|e| e.to_string())?;
    out.flush().map_err(|e| e.to_string())
}
fn fixture(
    srs: &PublicSrs,
    index: &ValidatedIndex,
    instance: &Instance,
    proof: &[u8],
    observations: Value,
) -> Result<Value> {
    let p = srs.profile();
    let lookup=index.lookup().map(|lk|json!({"physical_table":lk.physical_table.iter().map(|v|hex::encode(scalar_bytes(v))).collect::<Vec<_>>(),"function":lk.function.name(),"table_polynomial":lk.table_cycle.polynomial(),"h_polynomial":lk.h_cycle.polynomial()}));
    Ok(
        json!({"schema":"hyperplonk-rust-profiles-fixture-v1","profile":{"nu":p.nu(),"c":p.c(),"public_log":p.public_log(),"degree":p.degree(),"anchor":p.anchor(),"tight":p.tight(),"flags":p.flags()},"profile_id":p.profile_id(),"E":p.e(),"D":p.d(),"gate":index.gate().name(),"lookup":lookup,"context_hex":hex::encode(protocol::context_bytes(p,index,&instance.public)?),"public_input":instance.public.iter().map(|v|hex::encode(scalar_bytes(v))).collect::<Vec<_>>(),"index_commitments":index.commitments().iter().map(|(n,c)|(n.clone(),hex::encode(g2_bytes(c)))).collect::<std::collections::BTreeMap<_,_>>(),"tau_g2":srs.vk().tau_g2().iter().map(|c|hex::encode(g2_bytes(c))).collect::<Vec<_>>(),"zeta_g2":hex::encode(g2_bytes(srs.vk().zeta_g2())),"srs_id":hex::encode(srs.vk().srs_digest()),"index_id":hex::encode(index.digest()),"proof_hex":hex::encode(proof),"observations":observations,"scope":"independent verification fixture; not a formal performance sample"}),
    )
}
fn execute(args: &[String], config: &ExperimentConfig) -> Result<()> {
    if config.engine == "trace" {
        return Err("use hp5 for the trace baseline".into());
    }
    let p = config.workload.profile()?;
    let provenance = experiment::provenance()?;
    if args[1] == "setup" {
        if args.len() != 4 {
            return Err("setup requires CONFIG SRS".into());
        }
        if Path::new(&args[3]).exists() {
            return Err("SRS output already exists".into());
        }
        let before = resources::snapshot()?;
        let start = Instant::now();
        let srs = PublicSrs::setup(p, &mut OsRng)?;
        let setup_seconds = start.elapsed().as_secs_f64();
        let mut out = new_output(&args[3])?;
        let start = Instant::now();
        srs.write_to(&mut out)?;
        out.sync_all().map_err(|e| e.to_string())?;
        println!(
            "{}",
            json!({"operation":"setup","config":config,"provenance":provenance,"setup_seconds":setup_seconds,"serialization_seconds":start.elapsed().as_secs_f64(),"file_bytes":out.metadata().map_err(|e|e.to_string())?.len(),"srs_id":hex::encode(srs.vk().srs_digest()),"primary_points":srs.primary_point_counts(),"cached_points":srs.cached_point_counts(),"resources_before":before,"resources_after":resources::snapshot()?,"private_rng":"OsRng plus rejection sampling; computational byte source"})
        );
        return Ok(());
    }
    if args.len() != 5 || !matches!(args[1].as_str(), "bench" | "fixture" | "replay") {
        return Err("usage: hp8 setup CONFIG SRS | hp8 bench CONFIG SRS OUTPUT.jsonl | hp8 fixture CONFIG SRS OUTPUT.json".into());
    }
    let start = Instant::now();
    let mut reader = BufReader::new(File::open(&args[3]).map_err(|e| e.to_string())?);
    let srs = PublicSrs::read_from(&mut reader, config.max_primary_points)?;
    let loading_seconds = start.elapsed().as_secs_f64();
    if srs.profile() != &p {
        return Err("config/SRS profile mismatch".into());
    }
    let start = Instant::now();
    let first = config.workload.instance(config.seed_start)?;
    let first_input_seconds = start.elapsed().as_secs_f64();
    let definition_id = first.definition_id.clone();
    let start = Instant::now();
    let index = ValidatedIndex::certify(&srs, first.spec)?;
    let indexing_seconds = start.elapsed().as_secs_f64();
    drop(first.witness);
    drop(first.public);
    let verify = match config.engine.as_str() {
        "multi" => multi::verify,
        "total" => protocol::verify_total,
        _ => protocol::verify,
    };
    if args[1] == "replay" {
        let public = config.workload.instance(config.seed_start)?.public;
        let proof = std::fs::read(&args[4]).map_err(|e| e.to_string())?;
        for aggregate in [false, true] {
            verify(srs.vk(), &p, &index, &public, &proof, aggregate)?;
        }
        println!(
            "{}",
            json!({"status":"pass","verifiers":["individual","aggregate"],"proof_bytes":proof.len(),"proof_sha256":hex::encode(Sha256::digest(&proof))})
        );
        return Ok(());
    }
    if args[1] == "fixture" && matches!(config.engine.as_str(), "multi" | "total") {
        return Err("use the ablation bench export for this proof format".into());
    }
    let mut output = new_output(&args[4])?;
    let metadata = json!({"schema":"hyperplonk-experiment-v2","record":"initialization","config":config,"provenance":provenance,"N":p.n_total(),"n":p.n(),"k":p.k(),"E":p.e(),"D":p.d(),"profile_id":p.profile_id(),"srs_id":hex::encode(srs.vk().srs_digest()),"index_id":hex::encode(index.digest()),"definition_id":definition_id,"loading_seconds":loading_seconds,"first_input_generation_seconds":first_input_seconds,"indexing_seconds":indexing_seconds,"srs_bytes":std::fs::metadata(&args[3]).map_err(|e|e.to_string())?.len(),"primary_points":srs.primary_point_counts(),"cached_points":srs.cached_point_counts(),"resources":resources::snapshot()?,"timing_scope":"warm SRS and certified fixed index; input generation and indexing separate; protocol includes helper/address/table witness construction","memory_scope":"whole-process VmHWM after exec, including SRS loading and indexing; RSS before/after are snapshots"});
    let mut metadata = metadata;
    let ledger = if config.ablation {
        let mut data = if config.engine == "multi" {
            multi::ledger(&p, &index)?
        } else {
            let first_round_saving = usize::from(config.engine != "total");
            json!({"checks":[{"name":"global","dimension":p.l(),"honest_caps":p.e(),"soundness_caps":p.d()}],"helper_count":1,"helper_coefficients":p.e().iter().sum::<usize>()-first_round_saving})
        };
        data["source_mask_coefficients"] = json!(general_mask::source_mask_counts(&p)?);
        data["helper_policy"] = json!(if config.engine == "total" {
            "total_sum"
        } else {
            "half_cube"
        });
        data["dim_v"] = json!(p.v_count());
        data["dim_u"] = json!(p.u_count());
        metadata["ablation"] = data.clone();
        Some(data)
    } else {
        None
    };
    if args[1] == "bench" {
        record(&mut output, &metadata)?;
    }
    let repetitions = if args[1] == "fixture" {
        1
    } else {
        config.repeats
    };
    // No discarded warmup. The first execution remains visible and labelled.
    for run in 0..repetitions {
        let start = Instant::now();
        let instance = config.workload.instance(config.seed_start + run as u64)?;
        let input_seconds = start.elapsed().as_secs_f64();
        if instance.definition_id != definition_id {
            return Err("public circuit changed between input seeds".into());
        }
        let before = resources::snapshot()?;
        let prove = match config.engine.as_str() {
            "multi" => multi::prove_with_options,
            "total" => protocol::prove_total,
            _ => protocol::prove_with_options,
        };
        let (proof, prover) = prove(
            &srs,
            &index,
            &instance.public,
            &instance.witness,
            &mut OsRng,
            protocol::ProverOptions {
                cache_openings: config.engine != "direct",
            },
        )?;
        let after_prover = resources::snapshot()?;
        let individual_first = if config.ablation {
            instance.seed % 2 == 0
        } else {
            run % 2 == 0
        };
        let (individual, aggregate) = if individual_first {
            let i = verify(srs.vk(), &p, &index, &instance.public, &proof, false)?;
            let a = verify(srs.vk(), &p, &index, &instance.public, &proof, true)?;
            (i, a)
        } else {
            let a = verify(srs.vk(), &p, &index, &instance.public, &proof, true)?;
            let i = verify(srs.vk(), &p, &index, &instance.public, &proof, false)?;
            (i, a)
        };
        let after = resources::snapshot()?;
        let observation = json!({"record":"sample","run":run,"first_execution":run==0,"input":workload::metadata(&config.workload,&instance)?,"input_generation_seconds":input_seconds,"prover":prover,"individual_verifier":individual,"aggregate_verifier":aggregate,"verification_order":if run%2==0{"individual_then_aggregate"}else{"aggregate_then_individual"},"prover_cpu_seconds":after_prover.user_seconds+after_prover.system_seconds-before.user_seconds-before.system_seconds,"verifiers_cpu_seconds":after.user_seconds+after.system_seconds-after_prover.user_seconds-after_prover.system_seconds,"resources_before":before,"resources_after_prover":after_prover,"resources_after":after,"proof_sha256":hex::encode(Sha256::digest(&proof)),"status":"pass"});
        let mut observation = observation;
        if let Some(data) = &ledger {
            let source = general_mask::source_mask_counts(&p)?.iter().sum::<usize>();
            let helpers = data["helper_count"]
                .as_u64()
                .ok_or("missing helper count")? as usize;
            let coefficients = data["helper_coefficients"]
                .as_u64()
                .ok_or("missing helper coefficients")? as usize;
            let blinds = 3 + helpers;
            let opening = prover.opening_count * p.l();
            observation["ablation_randomness"] = json!({"source_coefficients":source,"helper_coefficients":coefficients,"commitment_blinds":blinds,"opening_coefficients":opening,"total_field_samples":source+coefficients+blinds+opening,"salt_bytes":32});
            observation["verification_order"] = json!(if individual_first {
                "individual_then_aggregate"
            } else {
                "aggregate_then_individual"
            });
            if args[1] == "bench" {
                let mut saved = new_output(&format!("{}.proof", &args[4]))?;
                saved.write_all(&proof).map_err(|e| e.to_string())?;
                saved.sync_all().map_err(|e| e.to_string())?;
            }
        }
        if args[1] == "fixture" {
            let value = fixture(
                &srs,
                &index,
                &instance,
                &proof,
                json!({"initialization":metadata,"sample":observation}),
            )?;
            record(&mut output, &value)?;
        } else {
            record(&mut output, &observation)?;
        }
        eprintln!(
            "sample {run}: {} bytes; prover {:.6}s; verifier {:.6}/{:.6}s",
            proof.len(),
            prover.seconds,
            individual.seconds,
            aggregate.seconds
        );
    }
    output.sync_all().map_err(|e| e.to_string())?;
    Ok(())
}
fn run() -> Result<()> {
    let args = env::args().collect::<Vec<_>>();
    if args.len() < 4 {
        return Err("usage: hp8 setup|bench|fixture CONFIG SRS [OUTPUT]".into());
    }
    let config = ExperimentConfig::read(&args[2])?;
    #[cfg(feature = "parallel")]
    {
        rayon::ThreadPoolBuilder::new()
            .num_threads(config.threads)
            .build()
            .map_err(|e| e.to_string())?
            .install(|| execute(&args, &config))
    }
    #[cfg(not(feature = "parallel"))]
    {
        if config.threads != 1 {
            return Err("parallel feature is required for threads>1".into());
        }
        execute(&args, &config)
    }
}
fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e}");
        std::process::exit(1)
    }
}
