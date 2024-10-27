use std::collections::HashMap;

use itertools::{izip, Itertools};
use log4rs::Config;
use petgraph::{
    algo::toposort,
    dot::{Config as PConfig, Dot},
};
use rand::{distributions::Uniform, thread_rng, Rng, RngCore};
use rust::{
    circuit::{circuit_to_skeleton_graph, sample_circuit_with_base_gate, BaseGate, Circuit, Gate},
    local_mixing_step, node_indices_to_gate_ids, test_circuit_equivalance,
    test_circuit_equivalance_for_debug,
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

    let ell_out_knd = 4;
    let ell_in_knd = 4;

    let max_convex_iterations = 100usize;
    let max_replacement_iterations = 1000000usize;

    let mut mixing_steps = 0;
    let inflationary_mixing_steps = 1000;
    let kneading_mixing_steps = 1000;

    let mut top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();

    // Inflationary stage

    while mixing_steps < inflationary_mixing_steps {
        log::info!("############################## Inflationary mixing step {mixing_steps} ##############################");

        let skeleton_graph_before = skeleton_graph.clone();

        let now = std::time::Instant::now();
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
        let elapsed = now.elapsed();

        log::info!(
            "local mixing step {mixing_steps} returned {success} in {:?}",
            elapsed
        );

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

            #[cfg(feature = "trace")]
            log::trace!(
                "Topsorted nodes after step {mixing_steps}: {:?}",
                node_indices_to_gate_ids(top_sorted_nodes.iter(), &skeleton_graph)
            );

            let mixed_circuit = Circuit::from_top_sorted_nodes(
                &top_sorted_nodes,
                &skeleton_graph,
                &gate_map,
                original_circuit.n(),
            );

            match test_circuit_equivalance_for_debug(&original_circuit, &mixed_circuit, rng) {
                Some(diff_indices) => {
                    #[cfg(feature = "trace")]
                    {
                        log::trace!(
                            "(Before) Node id to node index map: {:?}",
                            skeleton_graph_before
                                .node_indices()
                                .into_iter()
                                .map(|index| (
                                    index,
                                    skeleton_graph_before.node_weight(index).unwrap()
                                ))
                                .collect_vec()
                        );

                        log::trace!(
                            "(Before) Node id to node index map: {:?}",
                            skeleton_graph
                                .node_indices()
                                .into_iter()
                                .map(|index| (index, skeleton_graph.node_weight(index).unwrap()))
                                .collect_vec()
                        );

                        let before = Dot::with_config(
                            &skeleton_graph_before,
                            &[PConfig::EdgeNoLabel, PConfig::NodeIndexLabel],
                        );
                        let after = Dot::with_config(
                            &skeleton_graph,
                            &[PConfig::EdgeNoLabel, PConfig::NodeIndexLabel],
                        );

                        log::trace!("Before skeleton: {:?}", before);
                        log::trace!("After skeleton: {:?}", after);
                    }

                    assert!(false, "Different at indices {:?}", diff_indices);
                }
                None => {}
            }

            mixing_steps += 1;
        }
    }

    log::info!(
        "############################## Inflationary stage finished ##############################"
    );

    // Kneading stage
    mixing_steps = 0; // reset
    while mixing_steps < kneading_mixing_steps {
        log::info!("############################## Kneading mixing step {mixing_steps} ##############################");

        let now = std::time::Instant::now();
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
        let elapsed = now.elapsed();

        log::info!(
            "local mixing step {mixing_steps} returned {success} in {:?}",
            elapsed
        );

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

            #[cfg(feature = "trace")]
            log::trace!(
                "Topsorted nodes after step {mixing_steps}: {:?}",
                node_indices_to_gate_ids(top_sorted_nodes.iter(), &skeleton_graph)
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

    log::info!(
        "############################## Kneading stage finished ##############################"
    );

    let mixed_circuit = Circuit::from_top_sorted_nodes(
        &top_sorted_nodes,
        &skeleton_graph,
        &gate_map,
        original_circuit.n(),
    );
    mixed_circuit
}

fn main() {
    log4rs::init_file("log4rs.yaml", Default::default()).unwrap();
    // env_logger::init();

    let gates = 1000;
    let n = 128;
    let mut rng = thread_rng();
    let (original_circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);

    let mixed_circuit = strategy1(&original_circuit, n, &mut rng);

    test_circuit_equivalance(&original_circuit, &mixed_circuit, &mut rng);
}

// 1. Change log::info to trace that prints weights instead of indices. This is because indices change with node removal where as are constant.
// 2. Check whether graph can be constructed from a dot file. If so, we can use this method to construct graphs for debugging.
// 3.
