use circuit::{BaseGate, Circuit, Gate};
use either::Either::{Left, Right};
use itertools::{izip, Itertools};
use num_traits::Zero;
use petgraph::{
    algo::toposort,
    graph::NodeIndex,
    visit::EdgeRef,
    Direction::{self},
    Graph,
};
use rand::{
    distributions::{uniform::SampleUniform, Uniform},
    Rng, RngCore,
};
use sha2::{Digest, Sha256};
use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
};

pub mod algo;
pub mod circuit;

#[macro_export]
macro_rules! timed {
    ($description:expr, $code:expr) => {{
        #[cfg(feature = "time")]
        let start = {
            log::info!("{} {} ", $description, "·".repeat(70 - $description.len()));
            std::io::Write::flush(&mut std::io::stdout()).unwrap();
            std::time::Instant::now()
        };
        let out = $code;
        #[cfg(feature = "time")]
        log::info!("{:?}", start.elapsed());
        out
    }};
}

#[allow(dead_code)]
fn edges_to_string(edges: &HashSet<(NodeIndex, NodeIndex)>, g: &Graph<usize, usize>) -> String {
    let mut string = String::from("[");
    for edge in edges.iter() {
        string = format!(
            "{string} ({}, {}),",
            g.node_weight(edge.0).unwrap(),
            g.node_weight(edge.1).unwrap()
        );
    }
    string = format!("{string}]");
    string
}

pub fn node_indices_to_gate_ids<'a, I>(nodes: I, graph: &Graph<usize, usize>) -> Vec<usize>
where
    I: Iterator<Item = &'a NodeIndex>,
{
    nodes
        .map(|node_index| *graph.node_weight(*node_index).unwrap())
        .collect_vec()
}

fn input_value_to_bitstring_map(n: usize) -> HashMap<usize, Vec<bool>> {
    assert!(n < 20, "{n} >= 20; Too big!");
    let mut map = HashMap::new();
    for i in 0..1usize << n {
        let mut bitstring = vec![false; n];
        for j in 0..n {
            bitstring[j] = ((i >> j) & 1) == 1
        }
        map.insert(i, bitstring);
    }
    return map;
}

/// Find all paths from curr_node to sink
fn sink_dfs_with_collision_sets(
    curr_node: usize,
    collision_set: &[HashSet<usize>],
    path: &mut Vec<usize>,
    chains: &mut Vec<Vec<usize>>,
) {
    // if visited.contains(&curr_node) {
    //     return;
    // }

    if collision_set[curr_node].is_empty() {
        path.push(curr_node);
        chains.push(path.to_vec());
        path.pop();
        return;
    }

    path.push(curr_node);
    for edge in collision_set[curr_node].iter() {
        sink_dfs_with_collision_sets(*edge, collision_set, path, chains);
    }
    path.pop();
}

/// Find all dependency chains of the circuit with collision sets `collision_set`
fn dependency_chains_from_collision_set(collision_set: &[HashSet<usize>]) -> Vec<Vec<usize>> {
    let mut not_sources = HashSet::new();
    for set_i in collision_set.iter() {
        for j in set_i {
            not_sources.insert(*j);
        }
    }

    let mut chains = vec![];
    let mut path = vec![];
    for index in 0..collision_set.len() {
        // Do a DFS iff index is a source
        if !not_sources.contains(&index) {
            sink_dfs_with_collision_sets(index, collision_set, &mut path, &mut chains);
        }
    }
    return chains;
}

fn adjust_collision_with_dependency_chain<const MAX_K: usize, const IS_PRED: bool, D>(
    curr_node: NodeIndex,
    dependency_chain: &[NodeIndex],
    graph: &Graph<usize, usize>,
    gate_map: &HashMap<usize, BaseGate<MAX_K, D>>,
    new_edges: &mut HashSet<(NodeIndex, NodeIndex)>,
) where
    D: Copy + PartialEq + Into<usize>,
{
    if dependency_chain.len() == 0 {
        return;
    }

    let curr_gate = gate_map.get(graph.node_weight(curr_node).unwrap()).unwrap();
    let mut collding_gate_index = None;

    let dependency_index_iterator = if IS_PRED {
        Left(0..dependency_chain.len())
    } else {
        Right((0..dependency_chain.len()).rev())
    };

    for index in dependency_index_iterator {
        let other_gate = gate_map
            .get(graph.node_weight(dependency_chain[index]).unwrap())
            .unwrap();
        if curr_gate.check_collision(other_gate) {
            collding_gate_index = Some(index);
            break;
        }
    }

    if collding_gate_index.is_some() {
        let colliding_gate_index = collding_gate_index.unwrap();

        // add collision edge from curr_node to node in dependency chain or node in dep chain to curr_node
        if IS_PRED {
            new_edges.insert((curr_node, dependency_chain[colliding_gate_index]));
        } else {
            new_edges.insert((dependency_chain[colliding_gate_index], curr_node));
        }

        let new_dep = if IS_PRED {
            &dependency_chain[..colliding_gate_index]
        } else {
            &dependency_chain[colliding_gate_index + 1..]
        };

        if new_dep.len() != 0 {
            let direction = if IS_PRED {
                Direction::Incoming
            } else {
                Direction::Outgoing
            };
            for next_node in graph.neighbors_directed(curr_node, direction) {
                adjust_collision_with_dependency_chain::<MAX_K, IS_PRED, D>(
                    next_node, new_dep, graph, gate_map, new_edges,
                );
            }
        }
    }
}

fn sample_m_unique_values<const M: usize, D, R: RngCore>(
    rng: &mut R,
    distribution: &Uniform<D>,
) -> HashSet<D>
where
    D: SampleUniform + Eq + Hash + Copy + Zero,
{
    // Note(Jay): I removed the hash set way because iterator over hashset is in random order which is not good if we want to debug with a seeded rng.
    let mut values = HashSet::new();
    // let mut i = 0;
    // while i < M {
    //     let sample = rng.sample(distribution);
    //     if !values.contains(&sample) {
    //         values[i] = sample;
    //     }
    //     i += 1;
    // }
    while values.len() < M {
        let sample = rng.sample(distribution);
        values.insert(sample);
    }
    return values;
}

fn permutation_map<G>(
    circuit: &Circuit<G>,
    input_value_to_bitstring_map: &HashMap<usize, Vec<bool>>,
) -> HashMap<usize, Vec<bool>>
where
    G: Gate<Input = [bool]>,
{
    let mut permutation_map = HashMap::new();
    for (value, bitstring) in input_value_to_bitstring_map.iter() {
        let mut inputs = bitstring.clone();
        circuit.run(&mut inputs);
        // assert_ne!(bitstring_map.get(&i).unwrap(), &inputs);
        permutation_map.insert(*value, inputs);
    }
    return permutation_map;
}

pub fn sample_circuit_with_base_gate<const MAX_K: usize, D, R: RngCore>(
    gate_count: usize,
    n: D,
    two_prob: f64,
    rng: &mut R,
) -> (Circuit<BaseGate<MAX_K, D>>, String)
where
    D: Zero + SampleUniform + Copy + Eq + Hash + Debug + Display + Into<usize>,
{
    let three_replacement_cost = 4; // 3-way gates can be decomposed into 4 2-way gates
    let two_replacement_cost = 1;

    let distribution = Uniform::new(D::zero(), n);
    let mut gates = Vec::with_capacity(gate_count);
    let mut curr_gate = 0;
    let mut sample_trace = Sha256::new();
    let mut id = 0;

    while curr_gate < gate_count {
        if MAX_K == 2 {
            assert!(two_prob == 1.0);
            let unique_vals = sample_m_unique_values::<3, _, _>(rng, &distribution);
            let mut iter = unique_vals.into_iter();
            let target = iter.next().unwrap();
            let mut controls = [D::zero(); MAX_K];
            controls[0] = iter.next().unwrap();
            controls[1] = iter.next().unwrap();

            sample_trace.update(format!("TWO{target}{}{}", controls[0], controls[1],));

            curr_gate += two_replacement_cost;

            gates.push(BaseGate::<MAX_K, D>::new(
                id,
                target,
                controls,
                |controls, inputs| inputs[controls[0].into()] & inputs[controls[1].into()],
            ));
        } else {
            assert!(MAX_K == 3);
            let if_true_three = rng.gen_bool(1.0 - two_prob);
            if if_true_three {
                let unique_vals = sample_m_unique_values::<4, _, _>(rng, &distribution);

                let mut iter = unique_vals.into_iter();
                let target = iter.next().unwrap();
                let mut controls = [D::zero(); MAX_K];
                for i in 0..MAX_K {
                    controls[i] = iter.next().unwrap();
                }

                sample_trace.update(format!(
                    "THREE{target}{}{}{}",
                    controls[0], controls[1], controls[2]
                ));

                curr_gate += three_replacement_cost;

                gates.push(BaseGate::<MAX_K, D>::new(
                    id,
                    target,
                    controls,
                    |controls, inputs| {
                        inputs[controls[0].into()]
                            & inputs[controls[1].into()]
                            & inputs[controls[2].into()]
                    },
                ));
            } else {
                // sample 2 way CNOTs
                let unique_vals = sample_m_unique_values::<3, _, _>(rng, &distribution);

                let mut iter = unique_vals.into_iter();
                let target = iter.next().unwrap();
                let mut controls = [D::zero(); MAX_K];
                for i in 0..MAX_K - 1 {
                    controls[i] = iter.next().unwrap();
                }
                // With MAX_K = 3, if any gate has 2 controls then set the last control = n. n indicates useless slot.
                controls[2] = n;

                sample_trace.update(format!("TWO{target}{}{}", controls[0], controls[1],));

                curr_gate += two_replacement_cost;

                gates.push(BaseGate::<MAX_K, D>::new(
                    id,
                    target,
                    controls,
                    |controls, inputs| inputs[controls[0].into()] & inputs[controls[1].into()],
                ));
            };
        }

        id += 1;
    }

    let sample_trace: String = format!("{:X}", sample_trace.finalize());

    (Circuit::new(gates, n.into()), sample_trace)
}

/// Checks whether collisions set of any circuit is weakly connected.
///
/// Any directed graph is weakly connected if the underlying undirected graph is fully connected.
fn is_collisions_set_weakly_connected(collisions_set: &[HashSet<usize>]) -> bool {
    let gate_count = collisions_set.len();
    // row major matrix
    let mut undirected_graph = vec![false; gate_count * gate_count];
    for (i, set_i) in collisions_set.iter().enumerate() {
        for j in set_i {
            assert!(i < gate_count);
            assert!(*j < gate_count, "j={j} n={gate_count}");
            // graph[i][j] = true
            // graph[j][i] = true
            undirected_graph[i * gate_count + j] = true;
            undirected_graph[j * gate_count + i] = true;
        }
    }

    let mut all_nodes: HashSet<usize> = HashSet::from_iter(0..gate_count);
    let mut nodes_visited: HashSet<usize> = HashSet::new();
    let mut stack = vec![0];
    let mut is_weakly_connected = true;
    while nodes_visited.len() < gate_count {
        let curr_node = stack.pop();
        match curr_node {
            Some(curr_node) => {
                for k in all_nodes.iter() {
                    let index = curr_node * gate_count + k;
                    if undirected_graph[index] {
                        nodes_visited.insert(*k);
                        stack.push(*k);
                    }
                }
                nodes_visited.insert(curr_node);
                all_nodes.remove(&curr_node);
            }
            None => {
                is_weakly_connected = false;
                break;
            }
        }
    }

    is_weakly_connected
}

fn find_replacement_circuit<const MAX_K: usize, const WC: bool, D, R: RngCore>(
    circuit: &Circuit<BaseGate<MAX_K, D>>,
    ell_in: usize,
    n: D,
    two_prob: f64,
    max_iterations: usize,
    rng: &mut R,
) -> Option<Circuit<BaseGate<MAX_K, D>>>
where
    D: Zero + SampleUniform + Copy + Eq + Hash + Display + Debug + Into<usize>,
{
    let input_value_to_bitstring_map = input_value_to_bitstring_map(circuit.n());
    let permutation_map = permutation_map(circuit, &input_value_to_bitstring_map);

    let mut curr_iter = 0;
    let mut replacement_circuit = None;
    let mut visited_circuits = HashMap::new();

    while curr_iter < max_iterations {
        let (random_circuit, circuit_trace) =
            sample_circuit_with_base_gate::<MAX_K, D, _>(ell_in, n, two_prob, rng);

        if visited_circuits.contains_key(&circuit_trace) {
            let count = visited_circuits.get_mut(&circuit_trace).unwrap();
            *count += 1;
        } else {
            visited_circuits.insert(circuit_trace, 1usize);

            let mut funtionally_equivalent = true;
            for (value, bitstring) in input_value_to_bitstring_map.iter() {
                let mut inputs = bitstring.to_vec();
                random_circuit.run(&mut inputs);

                if &inputs != permutation_map.get(value).unwrap() {
                    funtionally_equivalent = false;
                    break;
                }
            }

            if funtionally_equivalent && WC {
                let collisions_set = circuit_to_collision_sets(&random_circuit);
                let is_weakly_connected = is_collisions_set_weakly_connected(&collisions_set);
                funtionally_equivalent = is_weakly_connected;
            }

            if funtionally_equivalent {
                replacement_circuit = Some(random_circuit);
                break;
            }
        }

        curr_iter += 1;

        #[cfg(feature = "trace")]
        if curr_iter % 100000 == 0 {
            log::trace!("[find_replacement_circuit] 100K iterations done");
        }

        // if curr_iter == max_iterations {
        //     replacement_circuit = Some(random_circuit);
        // }
    }

    // let mut visited_freq = vec![0; 1000];
    // visited_circuits.iter().for_each(|(_k, v)| {
    //     visited_freq[*v] += 1;
    // });

    #[cfg(feature = "trace")]
    log::trace!("Finding replacement total iterations: {}", curr_iter);
    // println!("Visited frequency: {:?}", visited_freq);

    return replacement_circuit;
}

fn dfs_only(
    curr_node: NodeIndex,
    visited: &mut HashSet<NodeIndex>,
    graph: &Graph<usize, usize>,
    direction: Direction,
) {
    if visited.contains(&curr_node) {
        // println!("Visited again!");
        return;
    }

    // path.push(curr_node.clone());
    for v in graph.neighbors_directed(curr_node.into(), direction) {
        dfs_only(v, visited, graph, direction);
    }
    // path.pop();
    visited.insert(curr_node);
}

fn dfs(
    curr_node: NodeIndex,
    visited_with_path: &mut HashSet<NodeIndex>,
    visited: &mut HashSet<NodeIndex>,
    path: &mut Vec<NodeIndex>,
    graph: &Graph<usize, usize>,
    direction: Direction,
) {
    if visited_with_path.contains(&curr_node) {
        path.iter().for_each(|node| {
            visited_with_path.insert(*node);
        });
        return;
    }

    if visited.contains(&curr_node) {
        return;
    }

    path.push(curr_node.clone());
    for v in graph.neighbors_directed(curr_node.into(), direction) {
        dfs(v, visited_with_path, visited, path, graph, direction);
    }
    path.pop();
    visited.insert(curr_node);
}

fn dfs_for_convexity(
    curr_node: NodeIndex,
    visited_with_path: &mut HashSet<NodeIndex>,
    visited: &mut HashSet<NodeIndex>,
    path: &mut Vec<NodeIndex>,
    graph: &Graph<usize, usize>,
    direction: Direction,
    break_when: usize,
) -> bool {
    if visited_with_path.len() > break_when {
        return false;
    }

    if visited_with_path.contains(&curr_node) {
        path.iter().for_each(|node| {
            visited_with_path.insert(*node);
        });
        if visited_with_path.len() > break_when {
            return false;
        }
        return true;
    }

    if visited.contains(&curr_node) {
        return true;
    }

    let mut return_bool = true;
    path.push(curr_node.clone());
    for v in graph.neighbors_directed(curr_node.into(), direction) {
        return_bool = return_bool
            && dfs_for_convexity(
                v,
                visited_with_path,
                visited,
                path,
                graph,
                direction,
                break_when,
            );

        if !return_bool {
            return false;
        }
    }

    path.pop();
    visited.insert(curr_node);
    return return_bool;
}

fn dfs_for_convexity2(
    curr_node: NodeIndex,
    target_node: NodeIndex,
    existing_convex_set: &HashSet<NodeIndex>,
    visited: &mut HashSet<NodeIndex>,
    path: &mut Vec<NodeIndex>,
    graph: &Graph<usize, usize>,
    direction: Direction,
) -> bool {
    if curr_node == target_node {
        for node in path.iter() {
            if !existing_convex_set.contains(node) {
                return false;
            }
        }
    }

    if visited.contains(&curr_node) {
        return true;
    }

    let mut return_bool = true;
    path.push(curr_node.clone());
    for v in graph.neighbors_directed(curr_node.into(), direction) {
        return_bool = return_bool
            && dfs_for_convexity2(
                v,
                target_node,
                existing_convex_set,
                visited,
                path,
                graph,
                direction,
            );

        if !return_bool {
            return false;
        }
    }

    path.pop();
    visited.insert(curr_node);
    return return_bool;
}

fn dfs_random(
    curr_node: NodeIndex,
    target_node: NodeIndex,
    set: &HashSet<NodeIndex>,
    visited: &mut HashSet<NodeIndex>,
    path: &mut Vec<NodeIndex>,
    graph: &Graph<usize, usize>,
    direction: Direction,
) -> bool {
    if curr_node == target_node {
        for node in path.iter() {
            if !set.contains(node) {
                return false;
            }
        }
        return true;
    }

    if visited.contains(&curr_node) {
        return true;
    }

    let mut return_bool = true;
    path.push(curr_node.clone());
    for v in graph.neighbors_directed(curr_node.into(), direction) {
        return_bool =
            return_bool && dfs_random(v, target_node, set, visited, path, graph, direction);

        if !return_bool {
            return false;
        }
    }

    path.pop();
    visited.insert(curr_node);
    return return_bool;
}

fn random_subgraph<R: RngCore>(
    desire_set_size: usize,
    graph: &Graph<usize, usize>,
    rng: &mut R,
) -> (Option<NodeIndex>, Option<HashSet<NodeIndex>>, bool) {
    let start_node = NodeIndex::from(rng.gen_range(0..graph.node_count()) as u32);

    let mut candidates = Vec::new();
    for edge in graph.edges_directed(start_node, Direction::Outgoing) {
        candidates.push(edge.target());
    }

    let mut set = HashSet::new();
    set.insert(start_node);
    while set.len() < desire_set_size {
        if candidates.len() == 0 {
            return (None, None, false);
        }

        let index = rng.gen_range(0..candidates.len());
        let el = candidates[index];
        candidates[index] = *candidates.last().unwrap();
        candidates.pop();
        if !set.contains(&el) {
            set.insert(el);
            for edge in graph.edges_directed(el, Direction::Outgoing) {
                candidates.push(edge.target());
            }
        }
    }

    return (Some(start_node), Some(set), true);
}

fn expand_convex_set_with_random_dfs(
    desire_set_size: usize,
    convex_set: &mut HashSet<NodeIndex>,
    graph: &Graph<usize, usize>,
) -> bool {
    if convex_set.len() == desire_set_size {
        return true;
    }
    // pick one edge randomly
    // check whether the graph still remains convex. If it does check whether max length has been reached. If yes, then return true with else pop the element out and return false.
    let candidate_node = {
        let mut iter_convex_set = convex_set.iter();
        let mut candidate_node = None;
        loop {
            match iter_convex_set.next() {
                Some(source_node) => {
                    // Pick just one outgoing edge.
                    // We really want to iterate over all edges in big graph! So just find the first one that's not in the convex set
                    let mut edge_iter = graph.neighbors_directed(*source_node, Direction::Outgoing);
                    loop {
                        match edge_iter.next() {
                            Some(potential_candidate) => {
                                if !convex_set.contains(&potential_candidate) {
                                    candidate_node = Some(potential_candidate);
                                    break;
                                }
                                // candidate_node = Some(potential_candidate);
                                // break;
                            }
                            None => {
                                break;
                            }
                        }
                    }

                    if candidate_node.is_some() {
                        break;
                    }
                }
                None => {
                    break;
                }
            };
        }
        if candidate_node.is_none() {
            return false;
        }

        candidate_node.unwrap()
    };

    // if convex_set.contains(&candidate_node) {
    //     assert!(false);
    //     return false;
    // }

    let mut union_visited_with_path = HashSet::new();
    union_visited_with_path.insert(candidate_node);
    let mut union_visited = HashSet::new();
    let mut path = vec![];
    for source in convex_set.iter() {
        let dfs_did_not_break = dfs_for_convexity(
            *source,
            &mut union_visited_with_path,
            &mut union_visited,
            &mut path,
            &graph,
            Direction::Outgoing,
            desire_set_size,
        );

        if !dfs_did_not_break {
            return false;
        }
    }

    union_visited_with_path.retain(|n| !convex_set.contains(n));

    if union_visited_with_path.len() + convex_set.len() <= desire_set_size {
        for node in union_visited_with_path {
            convex_set.insert(node);
        }
        if convex_set.len() < desire_set_size {
            return expand_convex_set_with_random_dfs(desire_set_size, convex_set, graph);
        } else {
            return true;
        }
    } else {
        return false;
    }
}

fn expand_convex_set_with_random_dfs2(
    desire_set_size: usize,
    convex_set: &mut HashSet<NodeIndex>,
    graph: &Graph<usize, usize>,
) -> bool {
    if convex_set.len() == desire_set_size {
        return true;
    }
    // pick one edge randomly
    // check whether the graph still remains convex. If it does check whether max length has been reached. If yes, then return true with else pop the element out and return false.
    let candidate_node = {
        let mut iter_convex_set = convex_set.iter();
        let mut candidate_node = None;
        loop {
            match iter_convex_set.next() {
                Some(source_node) => {
                    // Pick just one outgoing edge.
                    // We really want to iterate over all edges in big graph! So just find the first one that's not in the convex set
                    let mut edge_iter = graph.neighbors_directed(*source_node, Direction::Outgoing);
                    loop {
                        match edge_iter.next() {
                            Some(potential_candidate) => {
                                if !convex_set.contains(&potential_candidate) {
                                    candidate_node = Some(potential_candidate);
                                    break;
                                }
                                // candidate_node = Some(potential_candidate);
                                // break;
                            }
                            None => {
                                break;
                            }
                        }
                    }

                    if candidate_node.is_some() {
                        break;
                    }
                }
                None => {
                    break;
                }
            };
        }
        if candidate_node.is_none() {
            return false;
        }

        candidate_node.unwrap()
    };

    // if convex_set.contains(&candidate_node) {
    //     assert!(false);
    //     return false;
    // }

    let mut union_visited = HashSet::new();
    let mut path = vec![];
    for source in convex_set.iter() {
        let dfs_did_not_break = dfs_for_convexity2(
            *source,
            candidate_node,
            &convex_set,
            &mut union_visited,
            &mut path,
            &graph,
            Direction::Outgoing,
        );

        if !dfs_did_not_break {
            return false;
        }
    }

    convex_set.insert(candidate_node);

    return expand_convex_set_with_random_dfs(desire_set_size, convex_set, graph);
}

fn find_convex_subgraph<R: RngCore>(
    graph: &Graph<usize, usize>,
    ell_out: usize,
    max_iterations: usize,
    rng: &mut R,
) -> Option<HashSet<NodeIndex>> {
    let mut curr_iter = 0;

    let mut final_convex_set = None;
    let mut exhausted = HashSet::new();
    while curr_iter < max_iterations {
        let start_node = NodeIndex::from(rng.gen_range(0..graph.node_count()) as u32);

        if exhausted.contains(&start_node) {
            continue;
        } else {
            exhausted.insert(start_node);
        }

        let mut convex_set = HashSet::new();
        convex_set.insert(start_node);

        let moment_of_truth = expand_convex_set_with_random_dfs(ell_out, &mut convex_set, graph);

        if moment_of_truth {
            assert!(convex_set.len() == ell_out);
            final_convex_set = Some(convex_set);
            break;
        } else {
            curr_iter += 1;
        }
    }

    #[cfg(feature = "trace")]
    log::trace!("Find convex subcircuit iterations: {curr_iter}");

    return final_convex_set;
}

fn find_convex_subgraph2<R: RngCore>(
    graph: &Graph<usize, usize>,
    ell_out: usize,
    max_iterations: usize,
    rng: &mut R,
) -> Option<HashSet<NodeIndex>> {
    let mut curr_iter = 0;

    let mut final_convex_set = None;
    let mut exhausted = HashSet::new();
    while curr_iter < max_iterations {
        let start_node = NodeIndex::from(rng.gen_range(0..graph.node_count()) as u32);

        if exhausted.contains(&start_node) {
            continue;
        } else {
            exhausted.insert(start_node);
        }

        let mut convex_set = HashSet::new();
        convex_set.insert(start_node);

        let moment_of_truth = expand_convex_set_with_random_dfs2(ell_out, &mut convex_set, graph);

        if moment_of_truth {
            assert!(convex_set.len() == ell_out);
            final_convex_set = Some(convex_set);
            break;
        } else {
            curr_iter += 1;
        }
    }

    #[cfg(feature = "trace")]
    log::trace!("Find convex subcircuit iterations: {curr_iter}");

    return final_convex_set;
}

fn circuit_to_collision_sets<G: Gate>(circuit: &Circuit<G>) -> Vec<HashSet<usize>> {
    let mut all_collision_sets = Vec::with_capacity(circuit.gates().len());
    for (i, gi) in circuit.gates().iter().enumerate() {
        let mut collision_set_i = HashSet::new();
        for (j, gj) in (circuit.gates().iter().enumerate()).skip(i + 1) {
            if gi.check_collision(gj) {
                collision_set_i.insert(j);
            }
        }
        all_collision_sets.push(collision_set_i);
    }

    // Remove intsecting collisions. That is i can collide with j iff there is no k such that i < k < j with which both i & j collide
    for (i, _) in circuit.gates().iter().enumerate() {
        // Don't update collision set i in place. Otherwise situations like the following are missed: Let i collide with j < k < l. '
        // If i^th collision set is updated in place then k is removed from the set after checking against j^th collision set. And i^th
        // collision set will never be checked against k. Hence, an incorrect (or say unecessary) dependency will be drawn from i to l.
        // let mut collisions_set_i = all_collision_sets[i].clone();
        let mut to_remove = HashSet::new();
        for (j, _) in circuit.gates().iter().enumerate().skip(i + 1) {
            if all_collision_sets[i].contains(&j) {
                // remove id k from set of i iff k is in set of j (ie j, where j < k, collides with k)
                for node in all_collision_sets[i].intersection(&all_collision_sets[j]) {
                    to_remove.insert(*node);
                }
                // collisions_set_i.retain(|k| !all_collision_sets[j].contains(k));
            }
        }
        all_collision_sets[i].retain(|v| !to_remove.contains(v));
    }

    return all_collision_sets;
}

pub fn circuit_to_skeleton_graph<G: Gate>(circuit: &Circuit<G>) -> Graph<usize, usize> {
    let all_collision_sets = circuit_to_collision_sets(circuit);

    let mut skeleton = Graph::<usize, usize>::new();
    // add nodes with weights as ids
    let nodes = circuit
        .gates()
        .iter()
        .map(|g| skeleton.add_node(g.id()))
        .collect_vec();
    let edges = all_collision_sets.iter().enumerate().flat_map(|(i, set)| {
        // FIXME(Jay): Had to collect_vec due to lifetime issues
        let v = set.iter().map(|j| (nodes[i], nodes[*j])).collect_vec();
        v.into_iter()
    });

    skeleton.extend_with_edges(edges);

    return skeleton;
}

/// Local mixing step
///
/// Returns false if mixing step is not successuful which may happen if one of the following is true
/// - Elements in convex subset < \ell^out
/// - \omega^out <= 3
/// - Not able to find repalcement circuit after exhausting max_replacement_iterations iterations
pub fn local_mixing_step<const MAX_K: usize, D, R: RngCore>(
    skeleton_graph: &mut Graph<usize, usize>,
    ell_in: usize,
    ell_out: usize,
    n: D,
    two_prob: f64,
    gate_map: &mut HashMap<usize, BaseGate<MAX_K, D>>,
    top_sorted_nodes: &[NodeIndex],
    latest_id: &mut usize,
    max_replacement_iterations: usize,
    max_convex_iterations: usize,
    rng: &mut R,
) -> bool
where
    D: Into<usize>
        + TryFrom<usize>
        + PartialEq
        + Copy
        + Eq
        + Hash
        + Zero
        + Display
        + SampleUniform
        + Debug,
    <D as TryFrom<usize>>::Error: Debug,
{
    assert!(ell_out <= ell_in);

    let convex_subset = timed!(
        "Find convex subcircuit",
        match find_convex_subgraph(&skeleton_graph, ell_out, max_convex_iterations, rng) {
            Some(convex_subset) => convex_subset,
            None => return false,
        }
    );

    // Convex subset sorted in topological order
    let convex_subgraph_top_sorted_gate_ids = top_sorted_nodes
        .iter()
        .filter(|v| convex_subset.contains(v))
        .map(|node_index| skeleton_graph.node_weight(*node_index).unwrap());

    #[cfg(feature = "trace")]
    log::trace!(
        "Convex subset gate ids: {:?}",
        &convex_subgraph_top_sorted_gate_ids.clone().collect_vec()
    );

    let convex_subgraph_gates =
        convex_subgraph_top_sorted_gate_ids.map(|node| gate_map.get(node).unwrap());

    // Set of active wires in convex subgraph
    let mut omega_out = HashSet::new();
    convex_subgraph_gates.clone().for_each(|g| {
        omega_out.insert(g.target());
        for wire in g.controls().iter() {
            omega_out.insert(*wire);
        }
    });

    // return false if omega^out <= 3 because finding a replacement is apparently not possilbe.
    if omega_out.len() <= 3 {
        return false;
    }

    // Map from old wires to new wires in C^out
    let mut old_to_new_map = HashMap::new();
    let mut new_to_old_map = HashMap::new();
    for (new_index, old_index) in omega_out.iter().enumerate() {
        old_to_new_map.insert(*old_index, D::try_from(new_index).unwrap());
        new_to_old_map.insert(D::try_from(new_index).unwrap(), *old_index);
    }
    let c_out_gates = convex_subgraph_gates
        .clone()
        .enumerate()
        .map(|(index, gate)| {
            let old_controls = gate.controls();
            let mut new_controls = [D::zero(); MAX_K];
            new_controls[0] = *old_to_new_map.get(&old_controls[0]).unwrap();
            new_controls[1] = *old_to_new_map.get(&old_controls[1]).unwrap();
            BaseGate::new(
                index,
                *old_to_new_map.get(&gate.target()).unwrap(),
                new_controls,
                gate.control_func().clone(),
            )
        })
        .collect_vec();

    let c_out = Circuit::new(c_out_gates, omega_out.len());

    let c_in_dash = match find_replacement_circuit::<MAX_K, true, D, _>(
        &c_out,
        ell_in,
        D::try_from(c_out.n()).unwrap(),
        two_prob,
        max_replacement_iterations,
        rng,
    ) {
        Some(c_in_dash) => c_in_dash,
        None => return false,
    };

    let collision_sets_c_in = circuit_to_collision_sets(&c_in_dash);

    let c_in = Circuit::new(
        c_in_dash
            .gates()
            .iter()
            .map(|g| {
                *latest_id += 1;

                let new_controls = g.controls();
                // assert!(new_controls[2] == D::try_from(c_in_dash.n).unwrap());
                let mut old_controls = [D::zero(); MAX_K];
                old_controls[0] = *new_to_old_map.get(&new_controls[0]).unwrap();
                old_controls[1] = *new_to_old_map.get(&new_controls[1]).unwrap();
                BaseGate::<MAX_K, _>::new(
                    *latest_id,
                    *new_to_old_map.get(&g.target()).unwrap(),
                    old_controls,
                    g.control_func().clone(),
                )
            })
            .collect(),
        n.into(),
    );

    #[cfg(feature = "trace")]
    {
        log::trace!("Old to new wires map: {:?}", &old_to_new_map);
        log::trace!("New to old wires map: {:?}", &new_to_old_map);
        log::trace!("@@@@ C^out @@@@ {}", &c_out);
        log::trace!("@@@@ C^in @@@@ {}", &c_in_dash);
        log::trace!("C^in collision sets: {:?}", &collision_sets_c_in);
    }

    // #### Replace C^out with C^in #### //

    // Find all predecessors and successors of subgrpah C^out
    let mut c_out_imm_predecessors = HashSet::new();
    let mut c_out_imm_successors = HashSet::new();
    // First find all immediate predecessors and successors
    for node in convex_subset.iter() {
        for pred_edge in skeleton_graph.edges_directed(node.clone(), Direction::Incoming) {
            if !convex_subset.contains(&pred_edge.source()) {
                c_out_imm_predecessors.insert(pred_edge.source());
            }
        }
        for succ_edge in skeleton_graph.edges_directed(node.clone(), Direction::Outgoing) {
            if !convex_subset.contains(&succ_edge.target()) {
                c_out_imm_successors.insert(succ_edge.target());
            }
        }
    }

    let mut predecessors = HashSet::new();
    let mut path = vec![];
    for node in c_out_imm_predecessors.iter() {
        dfs(
            *node,
            &mut HashSet::new(),
            &mut predecessors,
            &mut path,
            &skeleton_graph,
            Direction::Incoming,
        );
    }
    assert!(path.len() == 0);
    let mut successors = HashSet::new();
    let mut path = vec![];
    for node in c_out_imm_successors.iter() {
        dfs(
            *node,
            &mut HashSet::new(),
            &mut successors,
            &mut path,
            &skeleton_graph,
            Direction::Outgoing,
        );
    }
    assert!(path.len() == 0);

    let mut outsiders = HashSet::new();
    for node in skeleton_graph.node_indices() {
        if !(successors.union(&predecessors)).contains(&node) && !convex_subset.contains(&node) {
            outsiders.insert(node);
        }
    }

    let c_in_nodes = c_in
        .gates()
        .iter()
        .map(|g| {
            let node = skeleton_graph.add_node(g.id());
            gate_map.insert(g.id(), g.clone());
            node
        })
        .collect_vec();

    let mut new_edges = HashSet::new();
    for (i, set_i) in collision_sets_c_in.iter().enumerate() {
        for j in set_i {
            new_edges.insert((c_in_nodes[i], c_in_nodes[*j]));
        }
    }

    #[cfg(feature = "trace")]
    log::trace!(
        "C^in gates: {:?}",
        node_indices_to_gate_ids(c_in_nodes.iter(), &skeleton_graph)
    );

    for node in predecessors.iter() {
        let node_gate = gate_map
            .get(skeleton_graph.node_weight(*node).unwrap())
            .unwrap();
        let colliding_indices = c_in.gates().iter().enumerate().filter_map(|(index, gate)| {
            if node_gate.check_collision(gate) {
                Some(c_in_nodes[index])
            } else {
                None
            }
        });
        colliding_indices.for_each(|target_node| {
            new_edges.insert((*node, target_node));
        });
    }
    for node in successors.iter() {
        let node_gate = gate_map
            .get(skeleton_graph.node_weight(*node).unwrap())
            .unwrap();
        let colliding_indices = c_in.gates().iter().enumerate().filter_map(|(index, gate)| {
            if node_gate.check_collision(gate) {
                Some(c_in_nodes[index])
            } else {
                None
            }
        });
        colliding_indices.for_each(|source_node| {
            new_edges.insert((source_node, *node));
        });
    }
    for node in outsiders.iter() {
        let node_gate = gate_map
            .get(skeleton_graph.node_weight(*node).unwrap())
            .unwrap();
        let colliding_indices = c_in.gates().iter().enumerate().filter_map(|(index, gate)| {
            if node_gate.check_collision(gate) {
                Some(c_in_nodes[index])
            } else {
                None
            }
        });
        colliding_indices.for_each(|target_node| {
            new_edges.insert((*node, target_node));
        });
    }

    for edge in new_edges {
        skeleton_graph.add_edge(edge.0, edge.1, Default::default());
    }

    // Index of removed node is take over by the node that has the last index. Here we remove \ell^out nodes.
    // As long as \ell^out <= \ell^in (notice that C^in gates are added before removing gates of C^out) none of
    // pre-existing nodes we replace the removed node and hence we wouldn't incorrectly delete some node.
    for node in convex_subset {
        gate_map
            .remove(&skeleton_graph.remove_node(node).unwrap())
            .unwrap();
    }

    return true;
}

pub fn run_local_mixing<const DEBUG: bool, R: RngCore>(
    original_circuit: &Circuit<BaseGate<2, u8>>,
    mut skeleton_graph: Graph<usize, usize>,
    gate_map: &mut HashMap<usize, BaseGate<2, u8>>,
    latest_id: &mut usize,
    n: u8,
    rng: &mut R,
    ell_out: usize,
    ell_in: usize,
    total_mixing_steps: usize,
    max_convex_iterations: usize,
    max_replacement_iterations: usize,
) -> Graph<usize, usize> {
    let mut mixing_steps = 0;

    let mut top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();

    while mixing_steps < total_mixing_steps {
        log::info!("############################## Local mixing step {mixing_steps} ##############################");

        let now = std::time::Instant::now();
        let success = local_mixing_step::<2, _, _>(
            &mut skeleton_graph,
            ell_in,
            ell_out,
            n,
            1.0,
            gate_map,
            &top_sorted_nodes,
            latest_id,
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
            let top_sort_res = timed!(
                "Topological sort after local mixing",
                toposort(&skeleton_graph, None)
            );
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

            if DEBUG {
                let mixed_circuit = Circuit::from_top_sorted_nodes(
                    &top_sorted_nodes,
                    &skeleton_graph,
                    &gate_map,
                    original_circuit.n(),
                );
                check_probabilisitic_equivalence(&original_circuit, &mixed_circuit, rng);
            }

            mixing_steps += 1;
        }
    }

    skeleton_graph
}

pub fn check_probabilisitic_equivalence<G, R: RngCore>(
    circuit0: &Circuit<G>,
    circuit1: &Circuit<G>,
    rng: &mut R,
) where
    G: Gate<Input = [bool]>,
{
    assert_eq!(circuit0.n(), circuit1.n());
    let n = circuit0.n();

    for value in rng.sample_iter(Uniform::new(0, 1u128 << n - 1)).take(10000) {
        // for value in 0..1u128 << 8 {
        let mut inputs = vec![];
        for i in 0..n {
            inputs.push((value >> i) & 1u128 == 1);
        }

        let mut inputs0 = inputs.clone();
        circuit0.run(&mut inputs0);

        let mut inputs1 = inputs.clone();
        circuit1.run(&mut inputs1);

        let mut diff_indices = vec![];
        if inputs0 != inputs1 {
            izip!(inputs0.iter(), inputs1.iter())
                .enumerate()
                .for_each(|(index, (v0, v1))| {
                    if v0 != v1 {
                        diff_indices.push(index);
                    }
                });
        }

        assert_eq!(inputs0, inputs1, "Different at indices {:?}", diff_indices);
    }
}

#[cfg(test)]
mod tests {

    use petgraph::algo::{
        all_simple_paths, connected_components, has_path_connecting, toposort, DfsSpace,
    };
    use rand::{thread_rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[test]
    fn test_local_mixing() {
        env_logger::init();

        let gates = 100;
        let n = 8;
        let mut rng = ChaCha8Rng::from_entropy();
        let (original_circuit, _) =
            sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);

        let mut skeleton_graph = circuit_to_skeleton_graph(&original_circuit);
        let mut top_sorted_nodes = toposort(&skeleton_graph, None).unwrap();
        let mut latest_id = 0;
        let mut gate_map = HashMap::new();
        original_circuit.gates().iter().for_each(|g| {
            latest_id = std::cmp::max(latest_id, g.id());
            gate_map.insert(g.id(), g.clone());
        });

        let ell_out = 2;
        let ell_in = 4;
        let max_convex_iterations = 1000usize;
        let max_replacement_iterations = 1000000usize;

        let mut mixing_steps = 0;
        let total_mixing_steps = 100;

        while mixing_steps < total_mixing_steps {
            log::info!("#### Mixing step {mixing_steps} ####");
            log::info!(
                "Topological order before local mixing iteration: {:?}",
                &node_indices_to_gate_ids(top_sorted_nodes.iter(), &skeleton_graph)
            );

            let success = local_mixing_step::<2, _, _>(
                &mut skeleton_graph,
                ell_in,
                ell_out,
                n,
                1.0,
                &mut gate_map,
                &top_sorted_nodes,
                &mut latest_id,
                max_replacement_iterations,
                max_convex_iterations,
                &mut rng,
            );

            log::info!("local mixing step {mixing_steps} returned {success}");

            if success {
                // let original_graph = circuit_to_skeleton_graph(&original_circuit);
                // let original_circuit_graphviz = Dot::with_config(
                //     &original_graph,
                //     &[Config::EdgeNoLabel, Config::NodeIndexLabel],
                // );
                // let mixed_circuit_graphviz = Dot::with_config(
                //     &skeleton_graph,
                //     &[Config::EdgeNoLabel, Config::NodeIndexLabel],
                // );

                // println!("Original circuit: {:?}", original_circuit_graphviz);
                // println!("Mixed circuit: {:?}", mixed_circuit_graphviz);

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
                    "Topological order after local mixing iteration: {:?}",
                    &node_indices_to_gate_ids(top_sorted_nodes.iter(), &skeleton_graph)
                );

                let mixed_circuit = Circuit::from_top_sorted_nodes(
                    &top_sorted_nodes,
                    &skeleton_graph,
                    &gate_map,
                    original_circuit.n(),
                );
                check_probabilisitic_equivalence(&original_circuit, &mixed_circuit, &mut rng);

                mixing_steps += 1;
            }
        }
    }

    #[test]
    fn test_dfs() {
        let gates = 50;
        let n = 10;
        let mut rng = thread_rng();
        for _ in 0..10 {
            let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
            let skeleton_graph = circuit_to_skeleton_graph(&circuit);

            let mut visited_with_path = HashSet::new();
            let mut visited = HashSet::new();
            let mut path = vec![];
            let node_a = thread_rng().gen_range(0..n) as u32;
            let node_b = thread_rng().gen_range(0..n) as u32;
            let source = NodeIndex::from(std::cmp::min(node_a, node_b));
            let target = NodeIndex::from(std::cmp::max(node_a, node_b));
            visited_with_path.insert(target);
            dfs(
                source,
                &mut visited_with_path,
                &mut visited,
                &mut path,
                &skeleton_graph,
                Direction::Outgoing,
            );

            // visited path will always contain `target` even if no path exists from source to target. Here we remove it.
            if visited_with_path.len() == 1 {
                assert!(visited_with_path.remove(&target));
            }

            // println!(
            //     "Source: {:?}, Target: {:?}, Visited nodes: {:?}",
            //     source, target, &visited_with_path
            // );

            // visited nodes must equal all nodes on all paths from source to target
            let mut expected_visited_nodes = HashSet::new();
            all_simple_paths::<Vec<_>, _>(&skeleton_graph, source, target, 0, None)
                .into_iter()
                .for_each(|path| {
                    path.into_iter().for_each(|node| {
                        expected_visited_nodes.insert(node);
                    });
                });

            assert_eq!(visited_with_path, expected_visited_nodes);
        }
    }

    #[test]
    fn test_find_convex_subcircuit() {
        let gates = 2000;
        let n = 64;
        let ell_out = 4;
        let max_iterations = 10000;
        let mut rng = thread_rng();

        let mut iter = 0;
        while iter < 1000 {
            let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
            let skeleton_graph = circuit_to_skeleton_graph(&circuit);

            let convex_subgraph =
                find_convex_subgraph(&skeleton_graph, ell_out, max_iterations, &mut rng);

            match convex_subgraph {
                Some(convex_subgraph) => {
                    // check that the subgraph is convex

                    let values = convex_subgraph.iter().map(|v| *v).collect_vec();
                    // If path exists from i to j then find all nodes in any path from i to j and check that the nodes are in the convex subgraph set
                    for i in 0..values.len() {
                        for j in 0..values.len() {
                            if i != j {
                                if has_path_connecting(&skeleton_graph, values[i], values[j], None)
                                {
                                    all_simple_paths::<Vec<_>, _>(
                                        &skeleton_graph,
                                        values[i],
                                        values[j],
                                        0,
                                        None,
                                    )
                                    .into_iter()
                                    .for_each(|path| {
                                        path.iter().for_each(|node| {
                                            assert!(convex_subgraph.contains(node));
                                        });
                                    });
                                }
                            }
                        }
                    }

                    iter += 1;
                }
                None => {}
            }
        }
    }

    #[test]
    fn test_is_weakly_connected() {
        let n = 5;
        let gates = 5;
        let mut rng = thread_rng();
        for _ in 0..10000 {
            let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
            let graph = circuit_to_skeleton_graph(&circuit);

            let collisions_sets = circuit_to_collision_sets(&circuit);
            let is_wc = is_collisions_set_weakly_connected(&collisions_sets);
            let expected_wc = connected_components(&graph) == 1;
            assert_eq!(
                is_wc, expected_wc,
                "Expected {expected_wc} but got {is_wc} for collisions sets {:?}",
                collisions_sets
            );
        }
    }

    pub(crate) struct Stats<T> {
        samples: Vec<T>,
    }

    impl<T> Stats<T>
    where
        T: for<'a> std::iter::Sum<&'a T> + TryInto<f64>,
        <T as TryInto<f64>>::Error: Debug,
    {
        pub(crate) fn new() -> Stats<T> {
            Self {
                samples: Default::default(),
            }
        }

        pub(crate) fn add_sample(&mut self, sample: T) {
            self.samples.push(sample);
        }

        pub(crate) fn average(&self) -> f64 {
            let s: T = self.samples.iter().sum();
            let s: f64 = s.try_into().unwrap();
            s / self.samples.len() as f64
        }
    }

    fn trialtrial<R: RngCore>(
        graph: &Graph<usize, usize>,
        max_iterations: usize,
        rng: &mut R,
    ) -> Option<HashSet<NodeIndex>> {
        let mut curr_iter = 0;
        while curr_iter < max_iterations {
            let mut source_node = None;
            let mut convex_set = None;
            loop {
                let (_source_node, _convex_set, is_valid) = random_subgraph(4, &graph, rng);
                if is_valid {
                    source_node = _source_node;
                    convex_set = _convex_set;
                    break;
                }
            }

            let source_node = source_node.unwrap();
            let convex_set = convex_set.unwrap();
            let mut convex_set_vec = vec![source_node];
            for i in convex_set.iter() {
                if *i != source_node {
                    convex_set_vec.push(*i);
                }
            }

            let mut is_convex = true;
            for i in 0..convex_set_vec.len() {
                for j in i + 1..convex_set_vec.len() {
                    let mut union_visited = HashSet::new();
                    let mut path = vec![];
                    is_convex = is_convex
                        && dfs_random(
                            convex_set_vec[i],
                            convex_set_vec[j],
                            &convex_set,
                            &mut union_visited,
                            &mut path,
                            &graph,
                            Direction::Outgoing,
                        );
                }
            }

            if is_convex {
                return Some(convex_set);
            }

            curr_iter += 1;
        }

        return None;
    }

    #[test]
    fn time_convex_subcircuit() {
        env_logger::init();
        let gates = 50000;
        let n = 64;
        let ell_out = 2;
        let max_iterations = 10000;
        let mut rng = thread_rng();
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let skeleton_graph = circuit_to_skeleton_graph(&circuit);

        let mut stats0 = Stats::new();
        let mut stats1 = Stats::new();

        for _ in 0..10 {
            let now = std::time::Instant::now();
            let _ =
                find_convex_subgraph2(&skeleton_graph, ell_out, max_iterations, &mut rng).unwrap();
            stats1.add_sample(now.elapsed().as_secs_f64());
            let now = std::time::Instant::now();
            let _ =
                find_convex_subgraph(&skeleton_graph, ell_out, max_iterations, &mut rng).unwrap();
            stats0.add_sample(now.elapsed().as_secs_f64());
        }

        println!("Average fast: {}", stats0.average());
        println!("Average fast2: {}", stats1.average());
    }

    #[test]
    fn time_blah() {
        env_logger::init();
        let gates = 50000;
        let n = 64;
        let ell_out = 4;
        let mut rng = thread_rng();
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let skeleton_graph = circuit_to_skeleton_graph(&circuit);

        let mut stats0 = Stats::new();
        let mut stats1 = Stats::new();

        for _ in 0..100 {
            let start_node = NodeIndex::from(rng.gen_range(0..skeleton_graph.node_count()) as u32);
            let mut convex_set = HashSet::new();
            convex_set.insert(start_node);

            let now = std::time::Instant::now();
            // let _ = trialll(&skeleton_graph, ell_out, max_iterations, &mut rng).unwrap();
            let _ = expand_convex_set_with_random_dfs(ell_out, &mut convex_set, &skeleton_graph);
            stats0.add_sample(now.elapsed().as_secs_f64());

            let now = std::time::Instant::now();
            // let _ = trialll(&skeleton_graph, ell_out, max_iterations, &mut rng).unwrap();
            let _ = expand_convex_set_with_random_dfs2(ell_out, &mut convex_set, &skeleton_graph);
            stats1.add_sample(now.elapsed().as_secs_f64());
        }

        println!("Average 0 runtime: {}", stats0.average());
        println!("Average 1 runtime: {}", stats1.average());
    }

    #[test]
    fn time_find_preds_succs() {
        env_logger::init();
        let gates = 50000;
        let n = 64;
        let ell_out = 4;
        let mut rng = thread_rng();
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let skeleton_graph = circuit_to_skeleton_graph(&circuit);

        let mut stats = Stats::new();
        // let mut stats1 = Stats::new();

        for _ in 0..10 {
            let start_node = NodeIndex::from(rng.gen_range(15000..17000) as u32);
            println!("Node: {:?}", start_node);
            let now = std::time::Instant::now();
            // let mut path = vec![];
            // dfs(
            //     start_node,
            //     &mut HashSet::new(),
            //     &mut HashSet::new(),
            //     &mut path,
            //     &skeleton_graph,
            //     Direction::Incoming,
            // );
            // dfs(
            //     start_node,
            //     &mut HashSet::new(),
            //     &mut HashSet::new(),
            //     &mut path,
            //     &skeleton_graph,
            //     Direction::Outgoing,
            // );

            dfs_only(
                start_node,
                &mut HashSet::new(),
                &skeleton_graph,
                Direction::Incoming,
            );

            // dfs_only(
            //     start_node,
            //     &mut HashSet::new(),
            //     &skeleton_graph,
            //     Direction::Incoming,
            // );
            stats.add_sample(now.elapsed().as_secs_f64());

            // let now = std::time::Instant::now();
            // dfs_only(
            //     start_node,
            //     &mut HashSet::new(),
            //     &skeleton_graph,
            //     Direction::Outgoing,
            // );
            // stats1.add_sample(now.elapsed().as_secs_f64());
        }

        println!(
            "Average traverse preds and succs with normal graph runtime: {}",
            stats.average()
        );
    }

    #[test]
    fn iteration_time() {
        let gates = 50000;
        let n = 64;
        let ell_out = 4;
        let mut rng = thread_rng();
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let skeleton_graph = circuit_to_skeleton_graph(&circuit);
        let mut stats = Stats::new();
        // let mut stats1 = Stats::new();

        for _ in 0..10 {
            let now = std::time::Instant::now();
            for node in skeleton_graph.node_indices() {
                if node.index() == (gates + 1) {
                    assert!(false);
                }
            }
            stats.add_sample(now.elapsed().as_secs_f64());
        }

        println!("Iteration runtime: {}", stats.average());
    }

    #[test]
    fn comp() {
        env_logger::init();
        let gates = 40000;
        let n = 64;
        let ell_out = 4;
        let mut rng = thread_rng();
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let skeleton_graph = circuit_to_skeleton_graph(&circuit);

        let mut stats_mydfs = Stats::new();
        // let mut stats_otherdfs = Stats::new();

        // for _ in 0..100 {
        //     let start_node = NodeIndex::from(0u32);

        //     let now = std::time::Instant::now();
        //     depth_first_search(
        //         &skeleton_graph,
        //         Some(start_node),
        //         (|event| Control::<usize>::Continue),
        //     );
        //     stats_otherdfs.add_sample(now.elapsed().as_secs_f64());

        //     let now = std::time::Instant::now();
        //     // let mut path = vec![];
        //     dfs_only(
        //         start_node,
        //         &mut HashSet::new(),
        //         &skeleton_graph,
        //         Direction::Outgoing,
        //     );
        //     stats_mydfs.add_sample(now.elapsed().as_secs_f64());
        // }
        let mut dfs_space = DfsSpace::new(&skeleton_graph);
        for _ in 0..10 {
            let now = std::time::Instant::now();
            toposort(&skeleton_graph, Some(&mut dfs_space)).unwrap();
            stats_mydfs.add_sample(now.elapsed().as_secs_f64());
        }

        println!("My DFS: {}", stats_mydfs.average());
        // println!("Other DFS: {}", stats_otherdfs.average());
    }
}
