use std::collections::HashMap;

use itertools::{izip, Itertools};
use petgraph::algo::toposort;
use rand::{distributions::Uniform, thread_rng, Rng, RngCore};
use rust::{
    circuit_to_skeleton_graph, local_mixing_step, sample_circuit_with_base_gate,
    test_circuit_equivalance, BaseGate, Circuit, Gate,
};

fn strategy1<R: RngCore>(
    original_circuit: &Circuit<BaseGate<2, u8>>,
    n: u8,
    rng: &mut R,
) -> Circuit<BaseGate<2, u8>> {
    let mut skeleton_graph = circuit_to_skeleton_graph(&original_circuit);
    let mut latest_id = 0;
    let mut gate_map = HashMap::new();
    original_circuit.gates().iter().for_each(|g| {
        latest_id = std::cmp::max(latest_id, g.id());
        gate_map.insert(g.id(), g.clone());
    });

    let ell_out_inf = 2;
    let ell_in_inf = 4;

    let ell_out_knd = 3;
    let ell_in_knd = 3;

    let max_convex_iterations = 1000usize;
    let max_replacement_iterations = 1000000usize;

    let mut mixing_steps = 0;
    let inflationary_mixing_steps = 100;
    let kneading_mixing_steps = 100;

    let mut top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();

    // Inflationary stage
    while mixing_steps < inflationary_mixing_steps {
        log::info!("#### Inflationary mixing step {mixing_steps} ####");

        let success = local_mixing_step::<2, _, _>(
            &mut skeleton_graph,
            ell_in_inf,
            ell_out_inf,
            n,
            1.0,
            &mut gate_map,
            &top_sorted_nodes,
            &mut latest_id,
            max_replacement_iterations,
            max_convex_iterations,
            rng,
        );

        log::info!("local mixing step {mixing_steps} returned {success}");

        if success {
            let top_sort_res = toposort(&skeleton_graph, None);
            match top_sort_res {
                Result::Ok(v) => {
                    top_sorted_nodes = v;
                }
                Err(_) => {
                    log::error!("Cycle detected!");
                    assert!(false);
                }
            }

            log::info!(
                "Topsorted nodes after step {mixing_steps}: {:?}",
                &top_sorted_nodes
            );

            mixing_steps += 1;
        }
    }

    log::info!("#### Inflationary stage finished ####");

    let mixed_circuit = Circuit::from_top_sorted_nodes(
        &top_sorted_nodes,
        &skeleton_graph,
        &gate_map,
        original_circuit.n(),
    );
    test_circuit_equivalance(&original_circuit, &mixed_circuit, rng);

    // Kneading stage
    mixing_steps = 0; // reset
    while mixing_steps < kneading_mixing_steps {
        log::info!("#### Kneading mixing step {mixing_steps} ####");

        let success = local_mixing_step::<2, _, _>(
            &mut skeleton_graph,
            ell_in_knd,
            ell_out_knd,
            n,
            1.0,
            &mut gate_map,
            &top_sorted_nodes,
            &mut latest_id,
            max_replacement_iterations,
            max_convex_iterations,
            rng,
        );

        log::info!("local mixing step {mixing_steps} returned {success}");

        if success {
            let top_sort_res = toposort(&skeleton_graph, None);
            match top_sort_res {
                Result::Ok(v) => {
                    top_sorted_nodes = v;
                }
                Err(_) => {
                    log::error!("Cycle detected!");
                    assert!(false);
                }
            }

            log::info!(
                "Topsorted nodes after step {mixing_steps}: {:?}",
                &top_sorted_nodes
            );

            mixing_steps += 1;
        }

        let mixed_circuit = Circuit::from_top_sorted_nodes(
            &top_sorted_nodes,
            &skeleton_graph,
            &gate_map,
            original_circuit.n(),
        );
        test_circuit_equivalance(&original_circuit, &mixed_circuit, rng);
    }

    log::info!("#### Kneading stage finished ####");

    let mixed_circuit = Circuit::from_top_sorted_nodes(
        &top_sorted_nodes,
        &skeleton_graph,
        &gate_map,
        original_circuit.n(),
    );
    mixed_circuit
}

fn main() {
    env_logger::init();

    let gates = 100;
    let n = 15;
    let mut rng = thread_rng();
    let (original_circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);

    let mixed_circuit = strategy1(&original_circuit, n, &mut rng);

    test_circuit_equivalance(&original_circuit, &mixed_circuit, &mut rng);
}

// 1. Change log::info to trace that prints weights instead of indices. This is because indices change with node removal where as are constant.
// 2. Check whether graph can be constructed from a dot file. If so, we can use this method to construct graphs for debugging.
// 3.
