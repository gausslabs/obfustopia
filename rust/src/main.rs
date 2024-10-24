use petgraph::algo::toposort;
use rand::{thread_rng, RngCore};
use rust::{
    check_probabilisitic_equivalence,
    circuit::{BaseGate, Circuit, Gate},
    circuit_to_skeleton_graph, local_mixing_step, node_indices_to_gate_ids, run_local_mixing,
    sample_circuit_with_base_gate, timed,
};
use std::collections::HashMap;

fn main() {
    log4rs::init_file("log4rs.yaml", Default::default()).unwrap();
    // env_logger::init();

    let gates = 200;
    let n = 128;
    let max_convex_iterations = 1000usize;
    let max_replacement_iterations = 1000000usize;

    let mut rng = thread_rng();

    let (original_circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
    let skeleton_graph = circuit_to_skeleton_graph(&original_circuit);
    let mut latest_id = 0;
    let mut gate_map = HashMap::new();
    original_circuit.gates().iter().for_each(|g| {
        latest_id = std::cmp::max(latest_id, g.id());
        gate_map.insert(g.id(), g.clone());
    });

    // Inflationary stage
    let inflationary_stage_steps = 10000;
    let skeleton_graph = run_local_mixing::<false, _>(
        &original_circuit,
        skeleton_graph,
        &mut gate_map,
        &mut latest_id,
        n,
        &mut rng,
        2,
        4,
        inflationary_stage_steps,
        max_convex_iterations,
        max_replacement_iterations,
    );

    // check_probabilisitic_equivalence(&original_circuit, &mixed_circuit, &mut rng);
}
