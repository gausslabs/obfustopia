use petgraph::algo::toposort;
use rand::{thread_rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rust::{
    check_probabilisitic_equivalence,
    circuit::{BaseGate, Circuit},
    circuit_to_skeleton_graph, prepare_circuit, run_local_mixing,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{collections::HashMap, env::args, path::Path};

#[derive(Serialize, Deserialize)]
struct ObfuscationConfig {
    /// Number of wires
    n: usize,
    /// Number of inflationary steps
    inflationary_stage_steps: usize,
    /// Number of kneading steps
    kneading_stage_steps: usize,
    /// Maximum number of iterations for each convex searching
    max_convex_iterations: usize,
    /// Maximum number of iterations for each replacement circuit searching
    max_replacement_iterations: usize,
}

#[derive(Serialize, Deserialize)]
struct ObfuscationJob {
    config: ObfuscationConfig,
    curr_inflationary_stage_steps: usize,
    curr_kneading_stage_steps: usize,
    curr_circuit: Circuit<BaseGate<2, u8>>,
    original_circuit: Circuit<BaseGate<2, u8>>,
}

impl ObfuscationJob {
    fn load(path: impl AsRef<Path>) -> Self {
        let job: ObfuscationJob = bincode::deserialize(&std::fs::read(path).unwrap()).unwrap();

        log::info!(
            "loaded job: curr_inflationary_stage_steps: {}, curr_inflationary_stage_steps: {}, curr_circuit digest: 0x{}, original_circuit digest: 0x{}",
            job.curr_inflationary_stage_steps,
            job.curr_kneading_stage_steps,
            hex::encode(Sha256::digest(bincode::serialize(&job.curr_circuit).unwrap())),
            hex::encode(Sha256::digest(bincode::serialize(&job.original_circuit).unwrap())),
        );

        job
    }

    fn store(&self, path: impl AsRef<Path>) {
        std::fs::write(&path, bincode::serialize(self).unwrap()).unwrap();

        log::info!(
            "stored job: curr_inflationary_stage_steps: {}, curr_inflationary_stage_steps: {}, curr_circuit digest: 0x{}, original_circuit digest: 0x{}",
            self.curr_inflationary_stage_steps,
            self.curr_kneading_stage_steps,
            hex::encode(Sha256::digest(bincode::serialize(&self.curr_circuit).unwrap())),
            hex::encode(Sha256::digest(bincode::serialize(&self.original_circuit).unwrap())),
        );
    }
}

fn main() {
    log4rs::init_file("log4rs.yaml", Default::default()).unwrap();
    // env_logger::init();

    let job_path = args().nth(1).expect("Job path");

    let mut job = if std::fs::exists(&job_path).unwrap() {
        ObfuscationJob::load(&job_path)
    } else {
        let config = ObfuscationConfig {
            n: 64,
            inflationary_stage_steps: 50000,
            kneading_stage_steps: 50000,
            max_convex_iterations: 10000,
            max_replacement_iterations: 1000000,
        };
        let original_circuit =
            // sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
            Circuit::sample_mutli_stage_cipher(config.n, thread_rng());
        ObfuscationJob {
            config,
            curr_inflationary_stage_steps: 0,
            curr_kneading_stage_steps: 0,
            curr_circuit: original_circuit.clone(),
            original_circuit,
        }
    };

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
    let skeleton_graph = run_local_mixing::<true, _>(
        "Inflationary stage",
        Some(&original_circuit),
        skeleton_graph,
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
        job.curr_inflationary_stage_steps,
        job.config.inflationary_stage_steps,
        job.config.max_convex_iterations,
        job.config.max_replacement_iterations,
        |step, mixed_circuit| {
            job.curr_inflationary_stage_steps = step;
            job.curr_circuit = mixed_circuit;
            job.store(&job_path);
        },
    );

    log::info!(
        "############################# Inflationary stage finished #############################"
    );

    {
        let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
        job.curr_inflationary_stage_steps = job.config.inflationary_stage_steps;
        job.curr_circuit = Circuit::from_top_sorted_nodes(
            &top_sorted_nodes,
            &skeleton_graph,
            &gate_map,
            job.config.n as _,
        );
        check_probabilisitic_equivalence(&job.curr_circuit, &original_circuit, &mut rng);
        job.store(&job_path);
    }

    log::info!(
        "############################# Kneading stage starting #############################"
    );

    let skeleton_graph = run_local_mixing::<true, _>(
        "Kneading stage",
        Some(&original_circuit),
        skeleton_graph,
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
        job.curr_kneading_stage_steps,
        job.config.kneading_stage_steps,
        job.config.max_convex_iterations,
        job.config.max_replacement_iterations,
        |step, mixed_circuit| {
            job.curr_kneading_stage_steps = step;
            job.curr_circuit = mixed_circuit;
            job.store(&job_path);
        },
    );

    log::info!(
        "############################# Kneading stage finished #############################"
    );

    {
        let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
        job.curr_kneading_stage_steps = job.config.kneading_stage_steps;
        job.curr_circuit = Circuit::from_top_sorted_nodes(
            &top_sorted_nodes,
            &skeleton_graph,
            &gate_map,
            job.config.n as _,
        );
        check_probabilisitic_equivalence(&job.curr_circuit, &original_circuit, &mut rng);
        job.store(&job_path);
    }
}
