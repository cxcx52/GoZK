//! Shared-SRS, fixed-index throughput measurements. Each concurrent prover has
//! its own Rayon pool and fresh OS randomness. Application seeds are public.
use hyperplonk_repair::{
    experiment::{self, ExperimentConfig},
    index::ValidatedIndex,
    pcs::PublicSrs,
    protocol, resources, workload, Result,
};
use rand::rngs::OsRng;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{
    env,
    fs::{File, OpenOptions},
    io::{BufReader, Write},
    sync::Barrier,
    thread,
    time::Instant,
};

#[cfg(feature = "parallel")]
type WorkerPool = rayon::ThreadPool;
#[cfg(not(feature = "parallel"))]
struct WorkerPool;

fn make_pool(threads: usize, name: String) -> Result<WorkerPool> {
    #[cfg(feature = "parallel")]
    {
        rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .thread_name(move |i| format!("{name}-{i}"))
            .build()
            .map_err(|e| e.to_string())
    }
    #[cfg(not(feature = "parallel"))]
    {
        let _ = name;
        if threads != 1 {
            return Err("parallel feature is required for threads>1".into());
        }
        Ok(WorkerPool)
    }
}

fn install<T: Send, F: FnOnce() -> T + Send>(pool: &WorkerPool, job: F) -> T {
    #[cfg(feature = "parallel")]
    {
        pool.install(job)
    }
    #[cfg(not(feature = "parallel"))]
    {
        let _ = pool;
        job()
    }
}

fn record(output: &mut File, value: &Value) -> Result<()> {
    serde_json::to_writer(&mut *output, value).map_err(|e| e.to_string())?;
    output.write_all(b"\n").map_err(|e| e.to_string())?;
    output.flush().map_err(|e| e.to_string())
}

fn sample(
    config: &ExperimentConfig,
    srs: &PublicSrs,
    index: &ValidatedIndex,
    definition_id: &str,
    worker: usize,
    run: usize,
    private_rng: &mut OsRng,
) -> Result<Value> {
    let seed = config.seed_start + (worker * config.repeats + run) as u64;
    let started = Instant::now();
    let input_start = Instant::now();
    let instance = config.workload.instance(seed)?;
    let input_seconds = input_start.elapsed().as_secs_f64();
    if instance.definition_id != definition_id {
        return Err("public circuit changed between throughput input seeds".into());
    }
    let proof_start = Instant::now();
    let (proof, prover) = protocol::prove_with_options(
        srs,
        index,
        &instance.public,
        &instance.witness,
        private_rng,
        protocol::ProverOptions {
            cache_openings: config.engine == "cached",
        },
    )?;
    let proof_seconds = proof_start.elapsed().as_secs_f64();
    let verify_start = Instant::now();
    let verifier = protocol::verify(
        srs.vk(),
        srs.profile(),
        index,
        &instance.public,
        &proof,
        true,
    )?;
    let verify_seconds = verify_start.elapsed().as_secs_f64();
    let proof_hash = hex::encode(Sha256::digest(&proof));
    let input = workload::metadata(&config.workload, &instance)?;
    Ok(json!({
        "record":"sample", "worker":worker, "run":run, "input_seed":seed,
        "first_execution_for_worker":run==0, "instance_id":instance.instance_id,
        "input":input, "input_generation_seconds":input_seconds,
        "proof_seconds":proof_seconds, "aggregate_verification_seconds":verify_seconds,
        "sample_wall_seconds_before_record":started.elapsed().as_secs_f64(),
        "proof_bytes":proof.len(), "proof_sha256":proof_hash,
        "prover":prover, "aggregate_verifier":verifier, "status":"pass"
    }))
}

struct WorkerResult {
    samples: Vec<Value>,
    failed: bool,
}

fn worker_loop(
    worker: usize,
    pool: WorkerPool,
    config: &ExperimentConfig,
    srs: &PublicSrs,
    index: &ValidatedIndex,
    definition_id: &str,
    ready: &Barrier,
    start: &Barrier,
) -> WorkerResult {
    install(&pool, || {
        // Pool construction and worker readiness are outside the measured batch.
        ready.wait();
        start.wait();
        let mut private_rng = OsRng;
        let mut samples = Vec::with_capacity(config.repeats);
        for run in 0..config.repeats {
            match sample(
                config,
                srs,
                index,
                definition_id,
                worker,
                run,
                &mut private_rng,
            ) {
                Ok(value) => samples.push(value),
                Err(error) => {
                    samples.push(json!({"record":"failure", "worker":worker, "run":run,
                        "input_seed":config.seed_start+(worker*config.repeats+run)as u64,
                        "status":"fail", "error":error}));
                    return WorkerResult {
                        samples,
                        failed: true,
                    };
                }
            }
        }
        WorkerResult {
            samples,
            failed: false,
        }
    })
}

fn execute(
    config: &ExperimentConfig,
    workers: usize,
    srs_path: &str,
    output: &mut File,
) -> Result<()> {
    let p = config.workload.profile()?;
    let provenance = experiment::provenance()?;
    // Restrict initialization as well; do not initialize a process-global pool.
    let init_pool = make_pool(config.threads, "hp8-throughput-init".into())?;
    let (srs, index, definition_id, loading_seconds, input_seconds, indexing_seconds) =
        install(&init_pool, || -> Result<_> {
            let started = Instant::now();
            let mut reader = BufReader::new(File::open(srs_path).map_err(|e| e.to_string())?);
            let srs = PublicSrs::read_from(&mut reader, config.max_primary_points)?;
            let loading_seconds = started.elapsed().as_secs_f64();
            if srs.profile() != &p {
                return Err("config/SRS profile mismatch".into());
            }
            let started = Instant::now();
            let first = config.workload.instance(config.seed_start)?;
            let input_seconds = started.elapsed().as_secs_f64();
            let definition_id = first.definition_id.clone();
            let started = Instant::now();
            let index = ValidatedIndex::certify(&srs, first.spec)?;
            let indexing_seconds = started.elapsed().as_secs_f64();
            drop(first.witness);
            drop(first.public);
            Ok((
                srs,
                index,
                definition_id,
                loading_seconds,
                input_seconds,
                indexing_seconds,
            ))
        })?;
    drop(init_pool);
    // A failed pool construction cannot strand already-running barrier waiters.
    let pools = (0..workers)
        .map(|w| make_pool(config.threads, format!("hp8-worker-{w}")))
        .collect::<Result<Vec<_>>>()?;
    record(
        output,
        &json!({
            "schema":"hyperplonk-throughput-v1", "record":"initialization",
            "config":config, "workers":workers, "threads_per_worker":config.threads,
            "compute_thread_budget":workers*config.threads, "requested_proofs":workers*config.repeats,
            "provenance":provenance, "N":p.n_total(), "n":p.n(), "k":p.k(),
            "profile_id":p.profile_id(), "E":p.e(), "D":p.d(),
            "srs_id":hex::encode(srs.vk().srs_digest()), "index_id":hex::encode(index.digest()),
            "definition_id":definition_id, "srs_bytes":std::fs::metadata(srs_path).map_err(|e|e.to_string())?.len(),
            "primary_points":srs.primary_point_counts(), "cached_points":srs.cached_point_counts(),
            "loading_seconds":loading_seconds, "first_input_generation_seconds":input_seconds,
            "indexing_seconds":indexing_seconds, "resources_after_initialization":resources::snapshot()?,
            "sharing":"one borrowed checked SRS and one certified fixed index; neither deep-cloned",
            "private_rng":"one OsRng handle per worker; fresh OS bytes and rejection sampling for each proof",
            "batch_timing_scope":"synchronized start through worker completion and collection; includes application input generation, proof, aggregate verification, hashing, in-memory sample records; excludes SRS loading, indexing, pool construction, readiness wait, and output file I/O",
            "resource_scope":"whole process only; no per-worker CPU or RSS attribution; VmHWM includes initialization"
        }),
    )?;
    let ready = Barrier::new(workers + 1);
    let start = Barrier::new(workers + 1);
    let (worker_results, batch_seconds, before, after) = thread::scope(|scope| -> Result<_> {
        let mut handles = Vec::with_capacity(workers);
        for (worker, pool) in pools.into_iter().enumerate() {
            let (srs, index, definition_id, ready, start) =
                (&srs, &index, definition_id.as_str(), &ready, &start);
            handles.push((
                worker,
                scope.spawn(move || {
                    worker_loop(
                        worker,
                        pool,
                        config,
                        srs,
                        index,
                        definition_id,
                        ready,
                        start,
                    )
                }),
            ));
        }
        ready.wait();
        // Snapshot failure must not return while workers wait at the start barrier.
        let before = resources::snapshot();
        let started = Instant::now();
        start.wait();
        let results = handles.into_iter().map(|(worker, handle)| match handle.join() {
            Ok(value) => value,
            Err(_) => WorkerResult { failed: true, samples: vec![json!({
                "record":"failure", "worker":worker, "status":"fail", "error":"worker panicked"
            })] },
        }).collect::<Vec<_>>();
        let seconds = started.elapsed().as_secs_f64();
        let after = resources::snapshot()?;
        Ok((results, seconds, before?, after))
    })?;
    let failed = worker_results.iter().any(|r| r.failed);
    let mut completed = 0usize;
    for result in worker_results {
        for sample in result.samples {
            if sample["status"] == "pass" {
                completed += 1;
            }
            record(output, &sample)?;
        }
    }
    let successful = !failed && completed == workers * config.repeats;
    record(
        output,
        &json!({
            "record":"batch", "status":if successful {"pass"} else {"fail"},
            "workers":workers, "threads_per_worker":config.threads,
            "requested_proofs":workers*config.repeats, "completed_verified_proofs":completed,
            "batch_wall_seconds":batch_seconds,
            "verified_proofs_per_second":if successful {Some(completed as f64 / batch_seconds)} else {None},
            "batch_process_cpu_seconds":after.user_seconds+after.system_seconds-before.user_seconds-before.system_seconds,
            "resources_before_batch":before, "resources_after_batch":after,
            "output_order":"worker then run; sample records were buffered in memory during the batch"
        }),
    )?;
    output.sync_all().map_err(|e| e.to_string())?;
    if !successful {
        return Err("throughput batch failed; preserved per-worker results".into());
    }
    eprintln!("{completed} verified proofs, {workers} workers x {} threads, {batch_seconds:.6}s, {:.6} proofs/s",
        config.threads, completed as f64 / batch_seconds);
    Ok(())
}

fn run() -> Result<()> {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 5 {
        return Err("usage: hp8_throughput CONFIG SRS OUTPUT.jsonl WORKERS".into());
    }
    let config = ExperimentConfig::read(&args[1])?;
    if config.engine == "trace" {
        return Err("trace engine is outside this throughput driver".into());
    }
    let workers = args[4]
        .parse::<usize>()
        .map_err(|_| "WORKERS must be a positive integer")?;
    if workers == 0
        || workers
            .checked_mul(config.threads)
            .ok_or("worker budget overflow")?
            > 18
    {
        return Err("workers * threads_per_worker must be in 1..=18".into());
    }
    let samples = workers
        .checked_mul(config.repeats)
        .ok_or("sample count overflow")?;
    config
        .seed_start
        .checked_add((samples - 1) as u64)
        .ok_or("throughput input seed overflow")?;
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[3])
        .map_err(|e| e.to_string())?;
    if let Err(error) = execute(&config, workers, &args[2], &mut output) {
        let _ = record(
            &mut output,
            &json!({"record":"fatal", "status":"fail", "error":error}),
        );
        let _ = output.sync_all();
        return Err(error);
    }
    Ok(())
}
fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}
