use petgraph::algo::toposort;
use rand::{thread_rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rust::{
    check_probabilisitic_equivalence,
    circuit::{BaseGate, Circuit},
    circuit_to_skeleton_graph, run_local_mixing,
};
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, env::args};

#[derive(Serialize, Deserialize)]
struct ObfuscationJob {
    curr_inflationary_stage_steps: usize,
    curr_kneading_stage_steps: usize,
    curr_circuit: Circuit<BaseGate<2, u8>>,
    original_circuit: Circuit<BaseGate<2, u8>>,
}

fn main() {
    log4rs::init_file("log4rs.yaml", Default::default()).unwrap();
    // env_logger::init();

    let mut rng = ChaCha8Rng::from_entropy();
    // let gates = 50000;
    let n = 64;
    let max_convex_iterations = 10000usize;
    let max_replacement_iterations = 1000000usize;

    let job_path = args().nth(1).expect("Job path");

    let mut job = if std::fs::exists(&job_path).unwrap() {
        bincode::deserialize(&std::fs::read(&job_path).unwrap()).unwrap()
    } else {
        let original_circuit =
            // sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
            Circuit::sample_mutli_stage_cipher(n, thread_rng());
        ObfuscationJob {
            curr_inflationary_stage_steps: 0,
            curr_kneading_stage_steps: 0,
            curr_circuit: original_circuit.clone(),
            original_circuit,
        }
    };

    let original_circuit = job.original_circuit.clone();

    let skeleton_graph = circuit_to_skeleton_graph(&job.curr_circuit);
    let mut latest_id = 0;
    let mut gate_map = HashMap::new();
    job.curr_circuit.gates().iter().for_each(|g| {
        latest_id = std::cmp::max(latest_id, g.id());
        gate_map.insert(g.id(), g.clone());
    });

    // Inflationary stage
    let inflationary_stage_steps = 50000;
    let skeleton_graph = run_local_mixing::<true, _>(
        "Inflationary stage",
        Some(&original_circuit),
        skeleton_graph,
        &mut gate_map,
        &mut latest_id,
        n as u8,
        &mut rng,
        2,
        4,
        job.curr_inflationary_stage_steps,
        inflationary_stage_steps,
        max_convex_iterations,
        max_replacement_iterations,
        |step, mixed_circuit| {
            job.curr_inflationary_stage_steps = step;
            job.curr_circuit = mixed_circuit;
            std::fs::write(&job_path, bincode::serialize(&job).unwrap()).unwrap();
        },
    );

    log::info!(
        "############################# Inflationary stage finished #############################"
    );

    {
        let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
        job.curr_inflationary_stage_steps = 50000;
        job.curr_circuit =
            Circuit::from_top_sorted_nodes(&top_sorted_nodes, &skeleton_graph, &gate_map, n as _);
        check_probabilisitic_equivalence(&job.curr_circuit, &original_circuit, &mut rng);
        std::fs::write(&job_path, bincode::serialize(&job).unwrap()).unwrap();
    }

    log::info!(
        "############################# Kneading stage starting #############################"
    );

    let kneading_stage_steps = 50000;
    let skeleton_graph = run_local_mixing::<true, _>(
        "Kneading stage",
        Some(&original_circuit),
        skeleton_graph,
        &mut gate_map,
        &mut latest_id,
        n as u8,
        &mut rng,
        4,
        4,
        job.curr_kneading_stage_steps,
        kneading_stage_steps,
        max_convex_iterations,
        max_replacement_iterations,
        |step, mixed_circuit| {
            job.curr_kneading_stage_steps = step;
            job.curr_circuit = mixed_circuit;
            std::fs::write(&job_path, bincode::serialize(&job).unwrap()).unwrap();
        },
    );

    log::info!(
        "############################# Kneading stage finished #############################"
    );

    {
        let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
        job.curr_kneading_stage_steps = 50000;
        job.curr_circuit =
            Circuit::from_top_sorted_nodes(&top_sorted_nodes, &skeleton_graph, &gate_map, n as _);
        check_probabilisitic_equivalence(&job.curr_circuit, &original_circuit, &mut rng);
        std::fs::write(&job_path, bincode::serialize(&job).unwrap()).unwrap();
    }
}
