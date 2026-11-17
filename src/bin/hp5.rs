//! Same-backend historical trace repair benchmark. Setup runs in a separate
//! process; benchmark rows use the shared workload and fresh OsRng coins.
use hyperplonk_repair::{
    experiment::{self, ExperimentConfig},
    index::Gate,
    resources,
    trace_pcs::ValidatedTraceSrs,
    trace_protocol::{self, TraceIndex, TraceProfile},
    workload, Result,
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

fn provenance() -> Result<Value> {
    let mut out = experiment::provenance()?;
    out["protocol"] = json!("B1-seven-trace-prefix-full-round-coefficients-rust-v1");
    out["private_rng"] = json!("OsRng plus exact rejection; OS byte source is computational");
    out["timing_scope"]=json!("prover includes proof encoding; verifier includes full canonical bytes decoding and subgroup checks");
    out["pairing_mode"] = json!("historical individual equations after same-point aggregation");
    Ok(out)
}
fn output(path: &str) -> Result<File> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|e| e.to_string())
}
fn emit(file: &mut File, value: &Value) -> Result<()> {
    serde_json::to_writer(&mut *file, value).map_err(|e| e.to_string())?;
    file.write_all(b"\n").map_err(|e| e.to_string())?;
    file.flush().map_err(|e| e.to_string())?;
    file.sync_data().map_err(|e| e.to_string())
}
fn trace_profile(config: &ExperimentConfig) -> Result<TraceProfile> {
    config.workload.profile()?;
    if config.workload.lookup.is_some() || config.workload.flags >= 2 {
        return Err("B1 historical driver supports core7 workloads only".into());
    }
    if !matches!(
        config.workload.gate()?,
        Gate::ReferencePower | Gate::FixedThirteen
    ) {
        return Err(
            "B1 matched baseline currently supports reference and fixed13 workloads".into(),
        );
    }
    if config.engine != "trace" {
        return Err("hp5 requires engine=trace; no geometry engine is silently substituted".into());
    }
    TraceProfile::new(
        config.workload.nu,
        config.workload.c,
        config.workload.public_log,
        config.workload.degree,
    )
}
fn setup(config: &ExperimentConfig, path: &str) -> Result<()> {
    let p = trace_profile(config)?;
    if Path::new(path).exists() {
        return Err("SRS output exists".into());
    }
    let provenance = provenance()?;
    let before = resources::snapshot()?;
    let start = Instant::now();
    let srs = p.setup(&mut OsRng, config.max_primary_points)?;
    let setup_seconds = start.elapsed().as_secs_f64();
    let serialization = Instant::now();
    let mut file = output(path)?;
    srs.write_to(&mut file)?;
    file.sync_all().map_err(|e| e.to_string())?;
    let serialization_seconds = serialization.elapsed().as_secs_f64();
    println!(
        "{}",
        json!({"operation":"setup","backend":"trace","configuration":config,"setup_seconds":setup_seconds,"serialization_seconds":serialization_seconds,"file_bytes":file.metadata().map_err(|e|e.to_string())?.len(),"primary_points":srs.parameters().primary_counts(),"cached_points":srs.cached_point_counts(),"srs_id":hex::encode(srs.vk().srs_digest()),"trace_parameters":{"L":p.l(),"T":p.parameters().t(),"D":p.parameters().d()},"extension_certificate":srs.field().certificate(),"resources_before":before,"resources_after":resources::snapshot()?,"provenance":provenance})
    );
    Ok(())
}
fn load(config: &ExperimentConfig, path: &str) -> Result<(ValidatedTraceSrs, f64)> {
    let start = Instant::now();
    let srs = ValidatedTraceSrs::read_from(
        &mut BufReader::new(File::open(path).map_err(|e| e.to_string())?),
        config.max_primary_points,
    )?;
    if srs.parameters() != trace_profile(config)?.parameters() {
        return Err("configured workload does not match trace SRS".into());
    }
    Ok((srs, start.elapsed().as_secs_f64()))
}
fn bench(config: &ExperimentConfig, srs_path: &str, path: &str) -> Result<()> {
    let p = trace_profile(config)?;
    let mut file = output(path)?;
    let provenance = provenance()?;
    let (srs, loading_seconds) = load(config, srs_path)?;
    let input_start = Instant::now();
    let initial = config.workload.instance(config.seed_start)?;
    let first_input_seconds = input_start.elapsed().as_secs_f64();
    let definition = initial.definition_id.clone();
    let start = Instant::now();
    let index = TraceIndex::certify(&srs, p.clone(), initial.spec)?;
    let indexing_seconds = start.elapsed().as_secs_f64();
    drop(initial.witness);
    drop(initial.public);
    let s = p.parameters().t() + 1;
    emit(
        &mut file,
        &json!({"schema":"hyperplonk-experiment-v2","record":"initialization","backend":"trace","config":config,"provenance":provenance,"N":p.n_total(),"n":p.n(),"k":p.k(),"T":p.parameters().t(),"D":p.parameters().d(),"E":{"gate":p.degree()*s+2,"public":s+2,"leaf_A":s+1,"leaf_B":s+1,"internal_A":2*s+2,"internal_B":2*s+2,"root":s+1},"srs_id":hex::encode(srs.vk().srs_digest()),"index_id":hex::encode(index.digest()),"definition_id":definition,"loading_seconds":loading_seconds,"first_input_generation_seconds":first_input_seconds,"indexing_seconds":indexing_seconds,"srs_bytes":std::fs::metadata(srs_path).map_err(|e|e.to_string())?.len(),"primary_points":srs.parameters().primary_counts(),"cached_points":srs.cached_point_counts(),"resources":resources::snapshot()?,"timing_scope":"warm SRS and certified fixed index; input generation and indexing separate; protocol includes trace-mask sampling and historical independent helpers","memory_scope":"whole-process VmHWM after exec, including SRS loading and indexing; RSS before/after are snapshots"}),
    )?;
    for repetition in 0..config.repeats {
        let seed = config
            .seed_start
            .checked_add(repetition as u64)
            .ok_or("input seed overflow")?;
        let input_start = Instant::now();
        let instance = config.workload.instance(seed)?;
        let input_seconds = input_start.elapsed().as_secs_f64();
        if instance.definition_id != definition {
            return Err("workload changed the fixed public index across repetitions".into());
        }
        let inputs = workload::metadata(&config.workload, &instance)?;
        let before = resources::snapshot()?;
        let (proof, prover) = trace_protocol::prove(
            &srs,
            &index,
            &instance.public,
            &instance.witness,
            &mut OsRng,
        )?;
        let after_prover = resources::snapshot()?;
        let verifier = trace_protocol::verify(srs.vk(), &index, &instance.public, &proof)?;
        let after = resources::snapshot()?;
        let row = json!({"record":"sample","run":repetition,"first_execution":repetition==0,"status":"pass","operation":"bench","backend":"trace","label":config.label,"repetition":repetition,"threads":config.threads,"engine":"trace","input":inputs,"input_generation_seconds":input_seconds,"prover":prover,"individual_verifier":verifier,"verification_order":"historical_individual_only","proof_sha256":hex::encode(Sha256::digest(&proof)),"resources_before":before,"resources_after_prover":after_prover,"resources_after":after,"prover_cpu_seconds":(after_prover.user_seconds-before.user_seconds)+(after_prover.system_seconds-before.system_seconds),"verifiers_cpu_seconds":(after.user_seconds-after_prover.user_seconds)+(after.system_seconds-after_prover.system_seconds),"process_hwm_kib":after.hwm_kib});
        emit(&mut file, &row)?;
        println!(
            "{}",
            json!({"event":"repetition_complete","backend":"trace","label":config.label,"repetition":repetition,"output":path,"proof_bytes":proof.len(),"prove_seconds":row["prover"]["seconds"],"verify_seconds":row["individual_verifier"]["seconds"]})
        );
    }
    Ok(())
}
fn fixture(config: &ExperimentConfig, srs_path: &str, path: &str) -> Result<()> {
    let p = trace_profile(config)?;
    if p.l() > 10 {
        return Err("public integration fixture restricted to L<=10".into());
    }
    let mut out = output(path)?;
    let (srs, loading_seconds) = load(config, srs_path)?;
    let input_start = Instant::now();
    let instance = config.workload.instance(config.seed_start)?;
    let input_seconds = input_start.elapsed().as_secs_f64();
    let inputs = workload::metadata(&config.workload, &instance)?;
    let index_start = Instant::now();
    let index = TraceIndex::certify(&srs, p, instance.spec)?;
    let indexing_seconds = index_start.elapsed().as_secs_f64();
    let (proof, prover) = trace_protocol::prove(
        &srs,
        &index,
        &instance.public,
        &instance.witness,
        &mut OsRng,
    )?;
    let verifier = trace_protocol::verify(srs.vk(), &index, &instance.public, &proof)?;
    let mut fixture = trace_protocol::public_fixture(srs.vk(), &index, &instance.public, &proof)?;
    fixture["observations"] = json!({"input_generation_seconds":input_seconds,"srs_loading_seconds":loading_seconds,"indexing_seconds":indexing_seconds,"prover":prover,"verifier":verifier,"resources":resources::snapshot()?});
    fixture["inputs"] = serde_json::to_value(inputs).map_err(|e| e.to_string())?;
    fixture["provenance"] = provenance()?;
    serde_json::to_writer_pretty(&mut out, &fixture).map_err(|e| e.to_string())?;
    out.sync_all().map_err(|e| e.to_string())?;
    println!(
        "{}",
        json!({"operation":"fixture","backend":"trace","output":path,"proof_bytes":proof.len()})
    );
    Ok(())
}
fn execute(config: &ExperimentConfig, args: &[String]) -> Result<()> {
    match args[1].as_str(){"setup" if args.len()==4=>setup(config,&args[3]),"bench" if args.len()==5=>bench(config,&args[3],&args[4]),"fixture" if args.len()==5=>fixture(config,&args[3],&args[4]),_=>Err("usage: hp5 setup CONFIG SRS | hp5 bench CONFIG SRS OUTPUT.jsonl | hp5 fixture CONFIG SRS OUTPUT.json".into())}
}
fn run() -> Result<()> {
    let args = env::args().collect::<Vec<_>>();
    if args.len() < 4 {
        return Err("usage: hp5 setup CONFIG SRS | hp5 bench CONFIG SRS OUTPUT.jsonl | hp5 fixture CONFIG SRS OUTPUT.json".into());
    }
    let config = ExperimentConfig::read(&args[2])?;
    config.validate()?;
    #[cfg(feature = "parallel")]
    {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(config.threads)
            .build()
            .map_err(|e| e.to_string())?;
        pool.install(|| execute(&config, &args))
    }
    #[cfg(not(feature = "parallel"))]
    {
        if config.threads != 1 {
            return Err("non-parallel build requires threads=1".into());
        }
        execute(&config, &args)
    }
}
fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1)
    }
}
