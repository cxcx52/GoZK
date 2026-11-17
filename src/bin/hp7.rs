//! Small reproducible driver. Setup and online proving run in separate processes.
//! Benchmark scheduling, statistical repetition and resource measurement belong
//! to the runner; the single-run timings here are diagnostic observations.
use hyperplonk_repair::{
    codec::{g2_bytes, scalar_bytes},
    index::{self, ValidatedIndex},
    pcs::PublicSrs,
    profile::ValidatedProfile,
    protocol, Result,
};
use rand::rngs::OsRng;
use serde_json::json;
use std::{
    env,
    fs::{self, File, OpenOptions},
    io::Write,
    path::Path,
    time::Instant,
};

fn num(s: &str) -> Result<usize> {
    s.parse().map_err(|_| "invalid integer argument".into())
}
fn run() -> Result<()> {
    let a = env::args().collect::<Vec<_>>();
    if a.len() < 3 {
        return Err("usage: hp7 setup SRS NU C PUBLIC_LOG DEGREE TIGHT ANCHOR | hp7 fixture SRS diagonal|fixed13 OUTPUT.json".into());
    }
    if a[1] == "setup" {
        if a.len() != 9 {
            return Err("setup requires SRS NU C PUBLIC_LOG DEGREE TIGHT ANCHOR".into());
        }
        if Path::new(&a[2]).exists() {
            return Err("SRS output exists; reuse it or select a fresh path".into());
        }
        let p = ValidatedProfile::new(
            num(&a[3])?,
            num(&a[4])?,
            num(&a[5])?,
            num(&a[6])?,
            Some(num(&a[8])?),
            match a[7].as_str() {
                "true" => true,
                "false" => false,
                _ => return Err("tight must be true/false".into()),
            },
        )?;
        // Initial pilot cap. Raising it requires an explicit memory/disk estimate.
        if p.v_count() > 1 << 21 {
            return Err("initial setup pilot cap exceeded (2^21 G2 directions)".into());
        }
        let start = Instant::now();
        let srs = PublicSrs::setup(p, &mut OsRng)?;
        let setup_seconds = start.elapsed().as_secs_f64();
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&a[2])
            .map_err(|e| e.to_string())?;
        srs.write_to(&mut file)?;
        file.sync_all().map_err(|e| e.to_string())?;
        println!(
            "{}",
            json!({"operation":"setup","setup_seconds":setup_seconds,"file_bytes":file.metadata().map_err(|e|e.to_string())?.len(),"srs_id":hex::encode(srs.vk().srs_digest()),"primary_points":srs.primary_point_counts(),"cached_points":srs.cached_point_counts(),"private_rng":"OsRng plus rejection; computational byte source"})
        );
        return Ok(());
    }
    if a[1] == "fixture" {
        if a.len() != 5 {
            return Err("fixture requires SRS diagonal|fixed13 OUTPUT.json".into());
        }
        if Path::new(&a[4]).exists() {
            return Err("fixture output exists".into());
        }
        let start = Instant::now();
        let mut file = File::open(&a[2]).map_err(|e| e.to_string())?;
        let srs = PublicSrs::read_from(&mut file, 1 << 22)?;
        let loading_seconds = start.elapsed().as_secs_f64();
        let p = srs.profile();
        let start = Instant::now();
        let (spec, witness) = match a[3].as_str() {
            "diagonal" => index::reference_fixture(p),
            "fixed13" => index::fixed_thirteen_fixture(p, &mut OsRng)?,
            _ => return Err("unknown gate".into()),
        };
        let input_generation_seconds = start.elapsed().as_secs_f64();
        let start = Instant::now();
        let index = ValidatedIndex::certify(&srs, spec)?;
        let indexing_seconds = start.elapsed().as_secs_f64();
        let public = &witness[..1 << p.public_log()];
        let (proof, prover) = protocol::prove(&srs, &index, public, &witness, &mut OsRng)?;
        let individual = protocol::verify(srs.vk(), p, &index, public, &proof, false)?;
        let aggregate = protocol::verify(srs.vk(), p, &index, public, &proof, true)?;
        let result = json!({"schema":"hyperplonk-rust-core7-fixture-v1","profile":{"nu":p.nu(),"c":p.c(),"public_log":p.public_log(),"degree":p.degree(),"anchor":p.anchor(),"tight":p.tight()},"profile_id":p.profile_id(),"E":p.e(),"D":p.d(),"gate":a[3],"context_hex":hex::encode(protocol::context_bytes(p,&index,public)?),"public_input":public.iter().map(|v|hex::encode(scalar_bytes(v))).collect::<Vec<_>>(),"index_commitments":index.commitments().iter().map(|(n,c)|(n.clone(),hex::encode(g2_bytes(c)))).collect::<std::collections::BTreeMap<_,_>>(),"tau_g2":srs.vk().tau_g2().iter().map(|c|hex::encode(g2_bytes(c))).collect::<Vec<_>>(),"zeta_g2":hex::encode(g2_bytes(srs.vk().zeta_g2())),"srs_id":hex::encode(srs.vk().srs_digest()),"index_id":hex::encode(index.digest()),"proof_hex":hex::encode(&proof),"observations":{"loading_seconds":loading_seconds,"input_generation_seconds":input_generation_seconds,"indexing_seconds":indexing_seconds,"prover":prover,"individual_verifier":individual,"aggregate_verifier":aggregate},"timing_scope":"single diagnostic observation, not a repeated performance experiment"});
        let mut out = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&a[4])
            .map_err(|e| e.to_string())?;
        out.write_all(&serde_json::to_vec_pretty(&result).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        out.sync_all().map_err(|e| e.to_string())?;
        println!(
            "{}",
            json!({"operation":"fixture","output":a[4],"proof_bytes":proof.len(),"observations":result["observations"]})
        );
        return Ok(());
    }
    if a[1] == "inspect" {
        let f = fs::read_to_string(&a[2]).map_err(|e| e.to_string())?;
        let value: serde_json::Value = serde_json::from_str(&f).map_err(|e| e.to_string())?;
        println!("{}", value["observations"]);
        return Ok(());
    }
    Err("unknown command".into())
}
fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1)
    }
}
