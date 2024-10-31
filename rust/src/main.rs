use petgraph::algo::toposort;
use rand::{thread_rng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rust::{
    check_probabilisitic_equivalence,
    circuit::{BaseGate, Circuit, Gate},
    circuit_to_skeleton_graph, local_mixing_step, node_indices_to_gate_ids, prepare_circuit,
    run_local_mixing, sample_circuit_with_base_gate, timed,
};
use std::collections::HashMap;

fn main() {
    log4rs::init_file("log4rs.yaml", Default::default()).unwrap();
    // env_logger::init();

    let gates = 500;
    let n = 64;
    let max_convex_iterations = 10000usize;
    let max_replacement_iterations = 1000000usize;

    let mut rng = ChaCha8Rng::from_entropy();

    let (original_circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
    let (
        mut direct_connections,
        mut skeleton_graph,
        mut gate_id_to_node_index_map,
        mut gate_map,
        mut latest_id,
    ) = prepare_circuit(&original_circuit);

    // Inflationary stage
    let inflationary_stage_steps = 10000;
    let skeleton_graph = run_local_mixing::<true, _>(
        "Inflationary stage",
        Some(&original_circuit),
        skeleton_graph,
        &mut direct_connections,
        &mut gate_map,
        &mut gate_id_to_node_index_map,
        &mut latest_id,
        n,
        &mut rng,
        2,
        4,
        inflationary_stage_steps,
        max_convex_iterations,
        max_replacement_iterations,
    );

    log::info!(
        "############################# Inflationary stage finished #############################"
    );

    {
        let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
        let mixed_circuit = Circuit::from_top_sorted_nodes(
            &top_sorted_nodes,
            &skeleton_graph,
            &gate_map,
            original_circuit.n(),
        );
        check_probabilisitic_equivalence(&original_circuit, &mixed_circuit, &mut rng);
    }

    log::info!(
        "############################# Kneading stage starting #############################"
    );

    let kneading_stage_steps = 10000;
    let skeleton_graph = run_local_mixing::<true, _>(
        "Kneading stage",
        Some(&original_circuit),
        skeleton_graph,
        &mut direct_connections,
        &mut gate_map,
        &mut gate_id_to_node_index_map,
        &mut latest_id,
        n,
        &mut rng,
        4,
        4,
        kneading_stage_steps,
        max_convex_iterations,
        max_replacement_iterations,
    );

    log::info!(
        "############################# Kneading stage finished #############################"
    );

    {
        let top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
        let mixed_circuit = Circuit::from_top_sorted_nodes(
            &top_sorted_nodes,
            &skeleton_graph,
            &gate_map,
            original_circuit.n(),
        );
        check_probabilisitic_equivalence(&original_circuit, &mixed_circuit, &mut rng);
    }
}
