use petgraph::algo::toposort;
use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rust::{
    check_probabilisitic_equivalence,
    circuit::{BaseGate, Circuit},
    prepare_circuit, run_local_mixing,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    env::{self, args},
    error::Error,
    path::Path,
};

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
enum Strategy {
    Strategy1,
    Strategy2,
}

#[derive(Serialize, Deserialize)]
struct ObfuscationConfig {
    /// Number of wires
    n: usize,
    /// Total steps in strategy 1
    total_steps: usize,
    /// Number of inflationary steps in strategy 2
    inflationary_stage_steps: usize,
    /// Number of kneading steps strategy 2
    kneading_stage_steps: usize,
    /// Maximum number of iterations for each convex searching
    max_convex_iterations: usize,
    /// Maximum number of iterations for each replacement circuit searching
    max_replacement_iterations: usize,
    /// Strategy used
    starategy: Strategy,
    /// Checkpoint steps. Checkpoints obfuscated circuit after `checkpoint` number of iterations
    checkpoint_steps: usize,
}

impl ObfuscationConfig {
    fn new_with_strategy1(
        n: usize,
        total_steps: usize,
        max_convex_iterations: usize,
        max_replacement_iterations: usize,
        checkpoint_steps: usize,
    ) -> Self {
        Self {
            n: n,
            total_steps: total_steps,
            inflationary_stage_steps: 0,
            kneading_stage_steps: 0,
            max_convex_iterations,
            max_replacement_iterations,
            starategy: Strategy::Strategy1,
            checkpoint_steps,
        }
    }

    fn new_with_strategy2(
        n: usize,
        inflationary_stage_steps: usize,
        kneading_stage_steps: usize,
        max_convex_iterations: usize,
        max_replacement_iterations: usize,
        checkpoint_steps: usize,
    ) -> Self {
        Self {
            n,
            inflationary_stage_steps,
            kneading_stage_steps,
            max_convex_iterations,
            max_replacement_iterations,
            starategy: Strategy::Strategy2,
            total_steps: 0,
            checkpoint_steps,
        }
    }

    fn default_strategy1() -> Self {
        ObfuscationConfig::new_with_strategy1(64, 4000, 10000, 1000000, 1000)
    }

    fn default_strategy2() -> Self {
        ObfuscationConfig::new_with_strategy2(64, 2000, 2000, 10000, 1000000, 1000)
    }
}

#[derive(Serialize, Deserialize)]
struct ObfuscationJob {
    config: ObfuscationConfig,
    /// [Strategy 1] Curr no. of total steps
    curr_total_steps: usize,
    /// [Strategy 2] Curr no. of steps in inflationary stage
    curr_inflationary_stage_steps: usize,
    /// [Strategy 2] Curr no. of steps in kneading stage
    curr_kneading_stage_steps: usize,
    curr_circuit: Circuit<BaseGate<2, u8>>,
    original_circuit: Circuit<BaseGate<2, u8>>,
}

impl ObfuscationJob {
    fn load(path: impl AsRef<Path>) -> Self {
        let job: ObfuscationJob = bincode::deserialize(&std::fs::read(path).unwrap()).unwrap();

        #[allow(dead_code)]
        #[derive(Debug)]
        struct Status {
            n: usize,
            total_steps: usize,
            inflationary_stage_steps: usize,
            kneading_stage_steps: usize,
            max_convex_iterations: usize,
            max_replacement_iterations: usize,
            starategy: Strategy,
            checkpoint_steps: usize,
            curr_total_steps: usize,
            curr_inflationary_stage_steps: usize,
            curr_kneading_stage_steps: usize,
            curr_circuit_digest: String,
            original_circuit_digest: String,
        }

        log::info!(
            "loaded job: {:#?}",
            Status {
                n: job.config.n,
                total_steps: job.config.total_steps,
                inflationary_stage_steps: job.config.inflationary_stage_steps,
                kneading_stage_steps: job.config.kneading_stage_steps,
                max_convex_iterations: job.config.max_convex_iterations,
                max_replacement_iterations: job.config.max_replacement_iterations,
                starategy: job.config.starategy,
                checkpoint_steps: job.config.checkpoint_steps,
                curr_total_steps: job.curr_total_steps,
                curr_inflationary_stage_steps: job.curr_inflationary_stage_steps,
                curr_kneading_stage_steps: job.curr_kneading_stage_steps,
                curr_circuit_digest: hex::encode(Sha256::digest(
                    bincode::serialize(&job.curr_circuit).unwrap()
                )),
                original_circuit_digest: hex::encode(Sha256::digest(
                    bincode::serialize(&job.original_circuit).unwrap()
                )),
            }
        );

        job
    }

    fn store(&self, path: impl AsRef<Path>) {
        std::fs::write(&path, bincode::serialize(self).unwrap()).unwrap();

        log::info!(
            "stored job, curr_inflationary_stage_steps: {}, curr_kneading_stage_steps: {}, curr_circuit digest: 0x{}, original_circuit digest: 0x{}",
            self.curr_inflationary_stage_steps,
            self.curr_kneading_stage_steps,
            hex::encode(Sha256::digest(bincode::serialize(&self.curr_circuit).unwrap())),
            hex::encode(Sha256::digest(bincode::serialize(&self.original_circuit).unwrap())),
        );
    }
}

fn run_strategy1(job: &mut ObfuscationJob, job_path: String, debug: bool) {
    let original_circuit = job.original_circuit.clone();
    let mut rng = ChaCha8Rng::from_entropy();

    let (
        mut direct_connections,
        mut direct_incoming_connections,
        mut skeleton_graph,
        mut gate_id_to_node_index_map,
        mut gate_map,
        mut graph_neighbours,
        mut latest_id,
    ) = prepare_circuit(&original_circuit);

    // For total no. of steps do the following:
    //  -> Sample a random no. betwee [2, 4]. Set that as ell_out
    //  -> Run local mixing step with ell_out and ell_in = 4

    while job.curr_total_steps < job.config.total_steps {
        let ell_out = rng.gen_range(2..=4);
        let to_checkpoint = job.curr_total_steps % job.config.checkpoint_steps == 0;

        let success = run_local_mixing(
            &format!(
                "[Strategy 1] [ell^out = {}] Mixing stage step {}",
                ell_out, job.curr_total_steps
            ),
            Some(&original_circuit),
            &mut skeleton_graph,
            &mut direct_connections,
            &mut direct_incoming_connections,
            &mut gate_map,
            &mut gate_id_to_node_index_map,
            &mut graph_neighbours,
            &mut latest_id,
            job.config.n as u8,
            &mut rng,
            ell_out,
            4,
            job.config.max_convex_iterations,
            job.config.max_replacement_iterations,
            to_checkpoint,
            |mixed_circuit| {
                job.curr_circuit = mixed_circuit;
                job.store(&job_path);
            },
            debug,
        );
        if success {
            job.curr_total_steps += 1;
        }
    }

    {
        let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
        job.curr_total_steps = job.config.total_steps;
        job.curr_circuit = Circuit::from_top_sorted_nodes(
            &top_sorted_nodes,
            &skeleton_graph,
            &gate_map,
            job.config.n as _,
        );

        let (is_correct, diff_indices) =
            check_probabilisitic_equivalence(&job.curr_circuit, &original_circuit, &mut rng);
        if !is_correct {
            log::error!(
                "[Error] [Strategy 1] Failed at end of Mixing stage. Different at indices {:?}",
                diff_indices
            );
            assert!(false);
        }

        job.store(&job_path);
    }
}

fn run_strategy2(job: &mut ObfuscationJob, job_path: String, debug: bool) {
    let original_circuit = job.original_circuit.clone();
    let mut rng = ChaCha8Rng::from_entropy();

    let (
        mut direct_connections,
        mut direct_incoming_connections,
        mut skeleton_graph,
        mut gate_id_to_node_index_map,
        mut gate_map,
        mut graph_neighbours,
        mut latest_id,
    ) = prepare_circuit(&original_circuit);

    // Inflationary stage
    {
        while job.curr_inflationary_stage_steps < job.config.inflationary_stage_steps {
            let to_checkpoint =
                job.curr_inflationary_stage_steps % job.config.checkpoint_steps == 0;

            // Inflationary stage
            let success = run_local_mixing(
                &format!(
                    "[Strategy 2] Inflationary stage step {}",
                    job.curr_inflationary_stage_steps
                ),
                Some(&original_circuit),
                &mut skeleton_graph,
                &mut direct_connections,
                &mut direct_incoming_connections,
                &mut gate_map,
                &mut gate_id_to_node_index_map,
                &mut graph_neighbours,
                &mut latest_id,
                job.config.n as u8,
                &mut rng,
                2,
                4,
                job.config.max_convex_iterations,
                job.config.max_replacement_iterations,
                to_checkpoint,
                |mixed_circuit| {
                    job.curr_circuit = mixed_circuit;
                    job.store(&job_path);
                },
                debug,
            );
            if success {
                job.curr_inflationary_stage_steps += 1;
            }
        }

        {
            let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
            job.curr_inflationary_stage_steps = job.config.inflationary_stage_steps;
            job.curr_circuit = Circuit::from_top_sorted_nodes(
                &top_sorted_nodes,
                &skeleton_graph,
                &gate_map,
                job.config.n as _,
            );

            let (is_correct, diff_indices) =
                check_probabilisitic_equivalence(&job.curr_circuit, &original_circuit, &mut rng);
            if !is_correct {
                log::error!(
                    "[Error] [Strategy 2] Failed at end of Inflationary stage. Different at indices {:?}",
                    diff_indices
                );
                assert!(false);
            }

            job.store(&job_path);
        }
    }

    // Kneading stage
    {
        while job.curr_kneading_stage_steps < job.config.kneading_stage_steps {
            let to_checkpoint = job.curr_kneading_stage_steps % job.config.checkpoint_steps == 0;

            let success = run_local_mixing(
                &format!(
                    "[Strategy 2] Kneading stage step {}",
                    job.curr_kneading_stage_steps
                ),
                Some(&original_circuit),
                &mut skeleton_graph,
                &mut direct_connections,
                &mut direct_incoming_connections,
                &mut gate_map,
                &mut gate_id_to_node_index_map,
                &mut graph_neighbours,
                &mut latest_id,
                job.config.n as u8,
                &mut rng,
                4,
                4,
                job.config.max_convex_iterations,
                job.config.max_replacement_iterations,
                to_checkpoint,
                |mixed_circuit| {
                    job.curr_circuit = mixed_circuit;
                    job.store(&job_path);
                },
                debug,
            );

            if success {
                job.curr_kneading_stage_steps += 1
            }
        }

        {
            let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
            job.curr_kneading_stage_steps = job.config.kneading_stage_steps;
            job.curr_circuit = Circuit::from_top_sorted_nodes(
                &top_sorted_nodes,
                &skeleton_graph,
                &gate_map,
                job.config.n as _,
            );

            let (is_correct, diff_indices) =
                check_probabilisitic_equivalence(&job.curr_circuit, &original_circuit, &mut rng);
            if !is_correct {
                log::error!(
                    "[Error] [Strategy 2] Failed at end of kneading stage. Different at indices {:?}",
                    diff_indices
                );
                assert!(false);
            }

            job.store(&job_path);
        }
    }
}

fn create_log4rs_config(log_path: &str) -> Result<log4rs::Config, Box<dyn Error>> {
    // Define the file appender with the specified path and pattern
    let file_appender = log4rs::append::file::FileAppender::builder()
        .encoder(Box::new(log4rs::encode::pattern::PatternEncoder::new(
            "{d} - {l} - {m}{n}",
        )))
        .build(log_path)?;

    // Build the configuration
    let config = log4rs::Config::builder()
        .appender(log4rs::config::Appender::builder().build("file", Box::new(file_appender)))
        .build(
            log4rs::config::Root::builder()
                .appender("file")
                .build(log::LevelFilter::Trace),
        )?;

    Ok(config)
}

fn main() {
    let debug = env::var("DEBUG") // only support `DEBUG=true` or `DEBUG=false`
        .ok()
        .and_then(|var| var.parse().ok())
        .unwrap_or(true);

    // Setup logs
    let log_path = args().nth(1).expect("Log path");
    let log_confg = create_log4rs_config(&log_path).unwrap();
    log4rs::init_config(log_confg).unwrap();

    let job_path = args().nth(2).expect("Job path");
    let orignal_circuit_path = args().nth(3).expect("Original path");

    let mut job = if std::fs::exists(&job_path).unwrap() {
        ObfuscationJob::load(&job_path)
    } else {
        let strategy = args().nth(4).map_or_else(
            || Strategy::Strategy1,
            |sid| match sid.parse::<u8>() {
                Ok(sid) => {
                    if sid == 1 {
                        return Strategy::Strategy1;
                    } else if sid == 2 {
                        return Strategy::Strategy2;
                    } else {
                        assert!(false, "Strategy can either be 1 or 2, not {sid}");
                        return Strategy::Strategy1; // Just to calm the compiler
                    }
                }
                Err(e) => {
                    assert!(false, "Strategy can either be 1 or 2, not {sid}");
                    return Strategy::Strategy1; // Just to calm the compiler
                }
            },
        );

        let config = match strategy {
            Strategy::Strategy1 => ObfuscationConfig::default_strategy1(),
            Strategy::Strategy2 => ObfuscationConfig::default_strategy2(),
        };

        // let (original_circuit, _) =
        // sample_circuit_with_base_gate::<2, u8, _>(300, config.n as u8, 1.0, &mut thread_rng());
        // Circuit::sample_mutli_stage_cipher(config.n, thread_rng());
        let original_circuit = Circuit::sample_mutli_stage_cipher(config.n, thread_rng());

        std::fs::write(
            &orignal_circuit_path,
            bincode::serialize(&original_circuit).unwrap(),
        )
        .unwrap();

        ObfuscationJob {
            config,
            curr_total_steps: 0,
            curr_inflationary_stage_steps: 0,
            curr_kneading_stage_steps: 0,
            curr_circuit: original_circuit.clone(),
            original_circuit,
        }
    };

    match job.config.starategy {
        Strategy::Strategy1 => {
            run_strategy1(&mut job, job_path, debug);
        }
        Strategy::Strategy2 => {
            run_strategy2(&mut job, job_path, debug);
        }
    }
}
