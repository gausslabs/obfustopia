use crate::circuit::{BaseGate, Circuit, Gate};
use circuit::{circuit_to_collision_sets, find_replacement_circuit};
use either::Either::{Left, Right};
use itertools::{izip, Itertools};
use num_traits::Zero;
use petgraph::{
    dot::{Config, Dot},
    graph::{self, NodeIndex},
    visit::EdgeRef,
    Direction::{self, Outgoing},
    Graph,
};
use rand::{
    distributions::{uniform::SampleUniform, Uniform},
    Rng, RngCore,
};
use rayon::{
    current_num_threads,
    iter::{
        IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelBridge,
        ParallelIterator,
    },
    slice::ParallelSlice,
};
use rustc_hash::FxHasher;

use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    thread::current,
};

pub mod circuit;

#[macro_export]
macro_rules! timed {
    ($description:expr, $code:expr) => {{
        #[cfg(feature = "time")]
        let start = {
            log::info!(
                "[Time] {} {} ",
                $description,
                "·".repeat(70 - $description.len())
            );
            std::io::Write::flush(&mut std::io::stdout()).unwrap();
            std::time::Instant::now()
        };
        let out = $code;
        #[cfg(feature = "time")]
        log::info!("{:?}", start.elapsed());
        out
    }};
}

pub fn node_indices_to_gate_ids<'a, I>(nodes: I, graph: &Graph<usize, usize>) -> Vec<usize>
where
    I: Iterator<Item = &'a NodeIndex>,
{
    nodes
        .map(|node_index| *graph.node_weight(*node_index).unwrap())
        .collect_vec()
}

pub fn edges_indices_to_gate_ids<'a, I>(
    nodes: I,
    graph: &Graph<usize, usize>,
) -> Vec<(usize, usize)>
where
    I: Iterator<Item = &'a (NodeIndex, NodeIndex)>,
{
    nodes
        .map(|node_tuple| {
            (
                *graph.node_weight(node_tuple.0).unwrap(),
                *graph.node_weight(node_tuple.1).unwrap(),
            )
        })
        .collect_vec()
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

fn find_convex_subcircuit<R: RngCore>(
    graph: &Graph<usize, usize>,
    ell_out: usize,
    max_iterations: usize,
    rng: &mut R,
) -> Option<HashSet<NodeIndex>> {
    let mut curr_iter = 0;

    let mut final_convex_set = None;
    while curr_iter < max_iterations {
        let convex_set = {
            let start_node = NodeIndex::from(rng.gen_range(0..graph.node_count()) as u32);

            let mut explored_candidates = HashSet::new();
            let mut unexplored_candidates = vec![];
            // TODO: Why does this always has to outgoing?
            for outgoing in graph.neighbors_directed(start_node, Outgoing) {
                unexplored_candidates.push(outgoing);
            }

            let mut convex_set = HashSet::new();
            convex_set.insert(start_node);

            while convex_set.len() < ell_out {
                let candidate = unexplored_candidates.pop();

                if candidate.is_none() {
                    break;
                }

                let mut union_vertices_visited_with_path = HashSet::new();
                let mut union_vertices_visited = HashSet::new();
                let mut path = vec![];
                union_vertices_visited_with_path.insert(candidate.unwrap());
                for source in convex_set.iter() {
                    dfs(
                        source.clone(),
                        &mut union_vertices_visited_with_path,
                        &mut union_vertices_visited,
                        &mut path,
                        graph,
                        Direction::Outgoing,
                    );
                }

                // Remove nodes in the exisiting convex set. The resulting set contains nodes that when added to convex set the set still remains convex.
                union_vertices_visited_with_path.retain(|node| !convex_set.contains(node));

                if union_vertices_visited_with_path.len() + convex_set.len() <= ell_out {
                    union_vertices_visited_with_path.iter().for_each(|node| {
                        convex_set.insert(node.clone());
                    });

                    if convex_set.len() < ell_out {
                        // more exploration to do
                        union_vertices_visited_with_path
                            .into_iter()
                            .for_each(|node| {
                                // add more candidates to explore
                                for outgoing in graph.neighbors_directed(node, Outgoing) {
                                    if !explored_candidates.contains(&outgoing) {
                                        unexplored_candidates.push(outgoing);
                                    }
                                }
                            });
                        explored_candidates.insert(candidate.unwrap());
                    }
                } else {
                    explored_candidates.insert(candidate.unwrap());
                }
            }
            convex_set
        };

        if convex_set.len() == ell_out {
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

fn find_all_predecessors(node: NodeIndex, graph: &Graph<usize, usize>) -> HashSet<NodeIndex> {
    let mut preds = HashSet::new();
    // First find all immediate predecessors and successors
    let mut path = vec![];
    for pred_edge in graph.edges_directed(node.clone(), Direction::Incoming) {
        let node = pred_edge.source();
        dfs(
            node,
            &mut HashSet::new(),
            &mut preds,
            &mut path,
            &graph,
            Direction::Incoming,
        );
    }
    return preds;
}

fn find_outsiders(
    graph: &Graph<usize, usize>,
    imm_predecessors: &HashSet<NodeIndex>,
    imm_successors: &HashSet<NodeIndex>,
    c_out: &HashSet<NodeIndex>,
) -> HashSet<NodeIndex> {
    let mut all_preds = HashSet::new();
    let mut path = vec![];
    for node in imm_predecessors.iter() {
        dfs(
            *node,
            &mut HashSet::new(),
            &mut all_preds,
            &mut path,
            &graph,
            Direction::Incoming,
        );
    }
    assert!(path.len() == 0);
    let mut all_succs = HashSet::new();
    for node in imm_successors.iter() {
        dfs(
            *node,
            &mut HashSet::new(),
            &mut all_succs,
            &mut path,
            &graph,
            Direction::Outgoing,
        );
    }

    let mut all_outsiders = HashSet::new();
    for node in graph.node_indices() {
        if !all_preds.contains(&node) && !all_succs.contains(&node) && !c_out.contains(&node) {
            all_outsiders.insert(node);
        }
    }
    return all_outsiders;
}

fn adjust_collision_with_dependency_chain<const MAX_K: usize, const IS_PRED: bool, D>(
    curr_node: NodeIndex,
    dependency_chain: &[NodeIndex],
    graph: &Graph<usize, usize>,
    gate_map: &HashMap<usize, BaseGate<MAX_K, D>>,
    new_edges: &mut HashSet<(NodeIndex, NodeIndex)>,
    depth: usize,
    visited: &mut HashSet<(NodeIndex, usize)>,
) where
    D: Copy + PartialEq + Into<usize>,
{
    #[cfg(feature = "trace")]
    {
        log::info!("        Call depth: {depth}");
        log::info!("        Curr node: {:?}", curr_node);
        log::info!("        Dependency chain: {:?}", dependency_chain);
    }

    if visited.contains(&(curr_node, dependency_chain.len())) {
        return;
    }

    if dependency_chain.len() == 0 {
        return;
    }

    visited.insert((curr_node, dependency_chain.len()));

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
        assert!(collding_gate_index.is_none());
    }

    let mut new_dep = &dependency_chain[..];

    if collding_gate_index.is_some() {
        let colliding_gate_index = collding_gate_index.unwrap();

        #[cfg(feature = "trace")]
        log::trace!(
            "       Found collision with node {:?} at index {}",
            graph
                .node_weight(dependency_chain[colliding_gate_index])
                .unwrap(),
            colliding_gate_index
        );

        // add collision edge from curr_node to node in dependency chain or node in dep chain to curr_node
        if IS_PRED {
            #[cfg(feature = "trace")]
            log::trace!(
                "       Adding new edge (pred to gate): {:?}",
                (
                    graph.node_weight(curr_node).unwrap(),
                    graph
                        .node_weight(dependency_chain[colliding_gate_index])
                        .unwrap()
                )
            );

            new_edges.insert((curr_node, dependency_chain[colliding_gate_index]));
        } else {
            #[cfg(feature = "trace")]
            log::trace!(
                "       Adding new edge (gate to succ): {:?}",
                (
                    graph
                        .node_weight(dependency_chain[colliding_gate_index])
                        .unwrap(),
                    graph.node_weight(curr_node).unwrap(),
                )
            );

            new_edges.insert((dependency_chain[colliding_gate_index], curr_node));
        }

        new_dep = if IS_PRED {
            &dependency_chain[..colliding_gate_index]
        } else {
            &dependency_chain[colliding_gate_index + 1..]
        };
    }

    // log::info!(
    //     "        Depth={depth} DDD {}",
    //     new_dep.len() == dependency_chain.len()
    // );

    if new_dep.len() != 0 {
        let direction = if IS_PRED {
            Direction::Incoming
        } else {
            Direction::Outgoing
        };
        for next_node in graph.neighbors_directed(curr_node, direction) {
            adjust_collision_with_dependency_chain::<MAX_K, IS_PRED, D>(
                next_node,
                new_dep,
                graph,
                gate_map,
                new_edges,
                depth + 1,
                visited,
            );
        }
    }
}

fn adjust_collision_with_dependency_chain_with_prune<const MAX_K: usize, D>(
    curr_node: NodeIndex,
    dependency_chain: PathWithIdentityRef,
    graph: &Graph<usize, usize>,
    gate_map: &HashMap<usize, BaseGate<MAX_K, D>>,
    new_edges: &mut HashSet<(NodeIndex, NodeIndex)>,
    depth: usize,
    visited: &mut HashSet<(NodeIndex, u64)>,
) where
    D: Copy + PartialEq + Into<usize>,
{
    #[cfg(feature = "trace")]
    {
        log::info!("        Call depth: {depth}");
        log::info!("        Curr node: {:?}", curr_node);
        log::info!("        Dependency chain: {:?}", dependency_chain);
    }

    if dependency_chain.is_empty() {
        // log::trace!("           Empty!");
        return;
    }

    if visited.contains(&(curr_node, dependency_chain.identity().unwrap())) {
        // log::trace!("           Collision!");
        return;
    }

    visited.insert((curr_node, dependency_chain.identity().unwrap()));

    let curr_gate = gate_map.get(graph.node_weight(curr_node).unwrap()).unwrap();
    let mut collding_gate_index = None;

    for index in 0..dependency_chain.path().len() {
        let other_gate = gate_map
            .get(graph.node_weight(dependency_chain.path()[index]).unwrap())
            .unwrap();
        if curr_gate.check_collision(other_gate) {
            collding_gate_index = Some(index);
            break;
        }
        assert!(collding_gate_index.is_none());
    }

    let new_dep = match collding_gate_index {
        Some(colliding_gate_index) => {
            #[cfg(feature = "trace")]
            log::trace!(
                "       Found collision with node {:?} at index {}",
                graph
                    .node_weight(dependency_chain[colliding_gate_index])
                    .unwrap(),
                colliding_gate_index
            );

            // add collision edge from curr_node to node in dependency chain or node in dep chain to curr_node
            #[cfg(feature = "trace")]
            log::trace!(
                "       Adding new edge (pred to gate): {:?}",
                (
                    graph.node_weight(curr_node).unwrap(),
                    graph
                        .node_weight(dependency_chain[colliding_gate_index])
                        .unwrap()
                )
            );

            new_edges.insert((curr_node, dependency_chain.path()[colliding_gate_index]));

            dependency_chain.drop_at(colliding_gate_index)
        }
        None => dependency_chain.clone(),
    };

    // log::info!(
    //     "        Depth={depth} DDD {}",
    //     new_dep.len() == dependency_chain.len()
    // );

    if !new_dep.is_empty() {
        for next_node in graph.neighbors_directed(curr_node, Direction::Incoming) {
            adjust_collision_with_dependency_chain_with_prune::<MAX_K, D>(
                next_node,
                new_dep,
                graph,
                gate_map,
                new_edges,
                depth + 1,
                visited,
            );
        }
    }
}

fn dfs_within_convex_set(
    curr_node: NodeIndex,
    convex_set: &HashSet<NodeIndex>,
    graph: &Graph<usize, usize>,
    targets_reached: &mut HashSet<NodeIndex>,
    visited: &mut HashSet<NodeIndex>,
) {
    assert!(convex_set.contains(&curr_node));

    if visited.contains(&curr_node) {
        return;
    }

    // targets outside c^out reached
    for t in graph
        .neighbors_directed(curr_node, Direction::Outgoing)
        .filter(|node| !convex_set.contains(node))
    {
        targets_reached.insert(t);
    }

    // Only pursue paths within C^out
    for target_node in graph.neighbors_directed(curr_node, Direction::Outgoing) {
        if convex_set.contains(&target_node) {
            dfs_within_convex_set(target_node, convex_set, graph, targets_reached, visited);
        }
    }
    visited.insert(curr_node);
}

#[derive(Debug)]
struct PathWithIdentity {
    path: Vec<NodeIndex>,
    path_hashes: Vec<u64>,
}

impl PathWithIdentity {
    fn new(path: Vec<NodeIndex>) -> Self {
        let mut hasher = FxHasher::default();

        let mut path_hashes = Vec::with_capacity(path.len());
        for node in path.iter() {
            hasher.write_usize(node.index());
            path_hashes.push(hasher.finish());
        }

        Self { path, path_hashes }
    }

    fn as_ref(&self) -> PathWithIdentityRef {
        PathWithIdentityRef {
            path: &self.path,
            path_hashes: &self.path_hashes,
        }
    }
}

#[derive(Clone, Copy)]
struct PathWithIdentityRef<'a> {
    path: &'a [NodeIndex],
    path_hashes: &'a [u64],
}

impl<'a> PathWithIdentityRef<'a> {
    fn drop_at(&self, index: usize) -> Self {
        Self {
            path: &self.path[..index],
            path_hashes: &self.path_hashes[..index],
        }
    }

    fn identity(&self) -> Option<u64> {
        self.path_hashes.last().copied()
    }

    fn is_empty(&self) -> bool {
        self.path.len() == 0
    }

    fn path(&self) -> &[NodeIndex] {
        &self.path
    }
}

fn dfs_till_collision<const MAX_K: usize, D>(
    target_gate: &BaseGate<MAX_K, D>,
    curr_node: NodeIndex,
    graph: &Graph<usize, usize>,
    gate_map: &HashMap<usize, BaseGate<MAX_K, D>>,
    path: &mut Vec<NodeIndex>,
    colliding_nodes: &mut HashSet<NodeIndex>,
    dependency_chains: &mut Vec<Vec<NodeIndex>>,
    visited: &mut HashSet<NodeIndex>,
) where
    D: Copy + PartialEq + Into<usize>,
{
    if visited.contains(&curr_node) {
        return;
    }

    let curr_gate = gate_map.get(graph.node_weight(curr_node).unwrap()).unwrap();

    if curr_gate.check_collision(target_gate) {
        // if path.len() != 0 {
        // assert!(*path.last().unwrap() != curr_node);
        // }
        dependency_chains.push(path.clone());
        colliding_nodes.insert(curr_node);
        return;
    }

    // if graph
    //     .neighbors_directed(curr_node, Direction::Outgoing)
    //     .count()
    //     == 0
    // {
    //     log::trace!("       Zero outgoin: {:?}", &path);
    //     dependency_chains.push(path.clone());
    //     return;
    // }

    path.push(curr_node);
    for next_node in graph.neighbors_directed(curr_node, Direction::Outgoing) {
        if !visited.contains(&next_node) {
            dfs_till_collision(
                target_gate,
                next_node,
                graph,
                gate_map,
                path,
                colliding_nodes,
                dependency_chains,
                visited,
            );
        }
    }
    path.pop();
    visited.insert(curr_node);
}

fn adjust_dependencies_for_prev_connected_nodes<const MAX_K: usize, D>(
    pred: NodeIndex,
    succ: NodeIndex,
    graph: &Graph<usize, usize>,
    gate_map: &HashMap<usize, BaseGate<MAX_K, D>>,
) -> HashSet<(NodeIndex, NodeIndex)>
where
    D: Copy + PartialEq + Into<usize> + Sync,
{
    #[cfg(feature = "trace")]
    log::trace!(
        "@@@@ Connecting prev connect pred {} succ {} @@@@@",
        graph.node_weight(pred).unwrap(),
        graph.node_weight(succ).unwrap()
    );

    let pred_gate = gate_map.get(graph.node_weight(pred).unwrap()).unwrap();

    let mut path = vec![];
    // Depedency chains to be adjusted with pred's predecessors
    let mut nodes_colliding_with_pred = HashSet::new();
    let mut dependency_chains = vec![];
    // timed!(
    // "        [Making connectinos] Part 1",
    dfs_till_collision(
        &pred_gate,
        succ,
        graph,
        gate_map,
        &mut path,
        &mut nodes_colliding_with_pred,
        &mut dependency_chains,
        &mut HashSet::new(),
    );
    // );

    let mut dependency_chains_with_identity = Vec::with_capacity(dependency_chains.len());
    dependency_chains
        .into_par_iter()
        .map(|dep| PathWithIdentity::new(dep))
        .collect_into_vec(&mut dependency_chains_with_identity);

    let mut new_edges = HashSet::new();
    for node in nodes_colliding_with_pred {
        new_edges.insert((pred, node));
    }

    #[cfg(feature = "trace")]
    {
        log::trace!("   Dependency chains");
        for dep in dependency_chains.iter() {
            log::trace!("{:?}", dep);
        }
    }

    #[cfg(feature = "trace")]
    log::trace!(
        "   New edges for predecessor {}: {:?}",
        graph.node_weight(pred).unwrap(),
        edges_indices_to_gate_ids(new_edges.iter(), graph)
    );

    // timed!(
    // "        [Making connections] part 2",
    let mut chunk_size = dependency_chains_with_identity.len() / current_num_threads();
    if chunk_size == 0 {
        chunk_size += 1;
    }

    let all_new_edges: Vec<HashSet<(NodeIndex, NodeIndex)>> = dependency_chains_with_identity
        .par_chunks(chunk_size)
        .map(|dep_chains| {
            let mut visited_dep_chains = HashSet::new();

            let mut new_edges = HashSet::new();

            for dep in dep_chains {
                for incoming_pred in graph.neighbors_directed(pred, Direction::Incoming) {
                    adjust_collision_with_dependency_chain_with_prune::<MAX_K, _>(
                        incoming_pred,
                        dep.as_ref(),
                        graph,
                        gate_map,
                        &mut new_edges,
                        0,
                        &mut visited_dep_chains,
                    );
                }
            }

            new_edges
        })
        .collect();

    for e in all_new_edges {
        new_edges.extend(e);
    }

    // for dep in dependency_chains_with_identity {
    //     #[cfg(feature = "trace")]
    //     log::trace!("   Processing Dependency chain: {:?}", &dep);

    //     for incoming_pred in graph.neighbors_directed(pred, Direction::Incoming) {
    //         #[cfg(feature = "trace")]
    //         log::trace!(
    //             "       Predecessor's predecessor: {:?}",
    //             graph.node_weight(incoming_pred).unwrap()
    //         );

    //         let mut tmp = HashSet::new();
    //         adjust_collision_with_dependency_chain_with_prune::<MAX_K, _>(
    //             incoming_pred,
    //             dep.as_ref(),
    //             graph,
    //             gate_map,
    //             &mut tmp,
    //             0,
    //             &mut visited_dep_chains,
    //         );

    //         #[cfg(feature = "trace")]
    //         log::trace!(
    //             "       New edges for predecessor's predecessor {}: {:?}",
    //             graph.node_weight(incoming_pred).unwrap(),
    //             edges_indices_to_gate_ids(tmp.iter(), graph)
    //         );

    //         new_edges.extend(tmp);
    //     }
    // }
    // );

    #[cfg(feature = "trace")]
    log::trace!("@@@@ @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ @@@@@",);

    new_edges
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
        + Debug
        + Sync,
    <D as TryFrom<usize>>::Error: Debug,
{
    assert!(ell_out <= ell_in);

    let convex_subset = timed!(
        "Find convex subset C^out",
        match find_convex_subcircuit(&skeleton_graph, ell_out, max_convex_iterations, rng) {
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

    let c_in_dash = timed!(
        "Find replacement circuit C^in",
        match find_replacement_circuit::<MAX_K, true, D, _>(
            &c_out,
            ell_in,
            D::try_from(c_out.n()).unwrap(),
            two_prob,
            max_replacement_iterations,
            rng,
        ) {
            Some(c_in_dash) => c_in_dash,
            None => return false,
        }
    );

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
        for pred in skeleton_graph.neighbors_directed(node.clone(), Direction::Incoming) {
            c_out_imm_predecessors.insert(pred);
        }
        for succ in skeleton_graph.neighbors_directed(node.clone(), Direction::Outgoing) {
            c_out_imm_successors.insert(succ);
        }
    }

    for node in convex_subset.iter() {
        c_out_imm_predecessors.remove(node);
        c_out_imm_successors.remove(node);
    }

    // find outsiders and add outgoing edges to gates it collides within C^in
    let outsiders = timed!(
        "Find outsiders",
        find_outsiders(
            &skeleton_graph,
            &c_out_imm_predecessors,
            &c_out_imm_successors,
            &convex_subset,
        )
    );

    #[cfg(feature = "trace")]
    {
        log::trace!("@@@@@ Immediate predecessors @@@@@");
        log::trace!(
            "{:?}",
            node_indices_to_gate_ids(c_out_imm_predecessors.iter(), &skeleton_graph)
        );
        log::trace!("@@@@@ @@@@@@@@@@@@@@@@@@@@@@ @@@@@");

        log::trace!("@@@@@ Immediate successors @@@@@");
        log::trace!(
            "{:?}",
            node_indices_to_gate_ids(c_out_imm_successors.iter(), &skeleton_graph)
        );
        log::trace!("@@@@@ @@@@@@@@@@@@@@@@@@@@ @@@@@");

        log::trace!("@@@@@ Outsiders @@@@@");
        log::trace!(
            "{:?}",
            node_indices_to_gate_ids(find_outsiders.iter(), &skeleton_graph)
        );
        log::trace!("@@@@@ @@@@@@@@@ @@@@@");
    }

    // find immediate predecessor and successor connection set
    let mut imm_pred_to_imm_succs_connection_via_cout = HashMap::new();
    timed!(
        "Immediate predecessors to immediate successors connections via C^out",
        for imm_pred in c_out_imm_predecessors.iter() {
            // find all immediate successors imm_pred is connected with via c^out
            let cout_nodes = skeleton_graph
                .neighbors_directed(*imm_pred, Direction::Outgoing)
                .filter(|target_node| convex_subset.contains(target_node));

            let mut targets_reached = HashSet::new();
            let mut visited = HashSet::new();
            for node in cout_nodes {
                dfs_within_convex_set(
                    node,
                    &convex_subset,
                    &skeleton_graph,
                    &mut targets_reached,
                    &mut visited,
                );
            }

            imm_pred_to_imm_succs_connection_via_cout.insert(*imm_pred, targets_reached);
        }
    );

    #[cfg(feature = "trace")]
    {
        log::trace!(
            "Immediate predecessors to Immediate succesors connections via C^out: {:?}",
            imm_pred_to_imm_succs_connection
        );
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

    #[cfg(feature = "trace")]
    log::trace!(
        "C^in gates: {:?}",
        node_indices_to_gate_ids(c_in_nodes.iter(), &skeleton_graph)
    );

    let dependency_chains = dependency_chains_from_collision_set(&collision_sets_c_in)
        .iter()
        .map(|dep_chain| {
            dep_chain
                .iter()
                .map(|index| c_in_nodes[*index])
                .collect_vec()
        })
        .collect_vec();

    #[cfg(feature = "trace")]
    {
        log::trace!("@@@@@ Dependency chains @@@@@");
        for dep_chain in dependency_chains.iter() {
            log::trace!(
                "{:?}",
                node_indices_to_gate_ids(dep_chain.iter(), &skeleton_graph)
            );
        }
        log::trace!("@@@@@ @@@@@@@@@@@@@@@@@ @@@@@");
    }

    // For each immediate predecessor find the first gate it collides with for all dependecy chains.
    // Let A be imm predecessor of C^out and A collides with gate K of dependency chain J -> K -> L.
    // Then preodecessors of A must be checked for collisions against J because J, part of C^in, must
    // come later in computation than predecessors of A. This means if any imm pedecessor A collides with
    // i^th gate of k^th dependency chain, then predecessors of A must be checked for collisions for j \in [0, i).
    let mut new_edges = HashSet::new();
    timed!(
        "Adjust C^in's dependency chains for predecessors",
        for imm_pred in c_out_imm_predecessors.iter() {
            #[cfg(feature = "trace")]
            log::trace!("@@@@@ Checking immediate pred {:?} @@@@@", imm_pred);

            for dep_chain in dependency_chains.iter() {
                #[cfg(feature = "trace")]
                log::trace!("  Dependency chain {:?}", dep_chain);

                let mut this_set = HashSet::new();
                adjust_collision_with_dependency_chain::<MAX_K, true, _>(
                    *imm_pred,
                    dep_chain,
                    &skeleton_graph,
                    gate_map,
                    &mut this_set,
                    0,
                    &mut HashSet::new(),
                );

                #[cfg(feature = "trace")]
                log::trace!("  Edges added: {:?}", this_set);

                new_edges.extend(this_set.iter());
            }
            #[cfg(feature = "trace")]
            log::trace!("@@@@@ @@@@@@@@@@@@@@@@@@@@@@@@@@@ @@@@@");
        }
    );

    timed!(
        "Adjust C^in's dependency chains for successors",
        for imm_succ in c_out_imm_successors.iter() {
            #[cfg(feature = "trace")]
            log::trace!("@@@@@ Checking immediate succ {:?} @@@@@", imm_succ);

            for dep_chain in dependency_chains.iter() {
                #[cfg(feature = "trace")]
                log::trace!("  Dependency chain {:?}", dep_chain);

                let mut this_set = HashSet::new();
                adjust_collision_with_dependency_chain::<MAX_K, false, _>(
                    *imm_succ,
                    dep_chain,
                    &skeleton_graph,
                    gate_map,
                    &mut this_set,
                    0,
                    &mut HashSet::new(),
                );

                #[cfg(feature = "trace")]
                log::trace!("  Edges added: {:?}", this_set);

                new_edges.extend(this_set.iter());
            }
            #[cfg(feature = "trace")]
            log::trace!("@@@@@ @@@@@@@@@@@@@@@@@@@@@@@@@@@ @@@@@");
        }
    );

    for out_node in outsiders.iter() {
        let out_gate = gate_map
            .get(skeleton_graph.node_weight(*out_node).unwrap())
            .unwrap();
        for (index, g) in c_in.gates().iter().enumerate() {
            if out_gate.check_collision(g) {
                new_edges.insert((*out_node, c_in_nodes[index]));
            }
        }
    }

    // Add edges within C^in
    for (i, set_i) in collision_sets_c_in.iter().enumerate() {
        for j in set_i {
            new_edges.insert((c_in_nodes[i], c_in_nodes[*j]));
        }
    }

    log::trace!("       New edges count: {}", new_edges.len());

    // Update the graph with new edges
    for edge in new_edges {
        skeleton_graph.add_edge(edge.0, edge.1, Default::default());
    }

    // -----

    // Find immPred to immSucc connectino with C^in
    let mut cin_convex_subset = HashSet::new();
    c_in_nodes.iter().for_each(|n| {
        cin_convex_subset.insert(*n);
    });
    let mut imm_pred_to_imm_succs_connection_via_cin = HashMap::new();
    for imm_pred in c_out_imm_predecessors.iter() {
        // find all immediate successors imm_pred is connected with via c^in
        let cin_nodes = skeleton_graph
            .neighbors_directed(*imm_pred, Direction::Outgoing)
            .filter(|target_node| cin_convex_subset.contains(target_node));

        let mut targets_reached = HashSet::new();
        let mut visited = HashSet::new();
        for node in cin_nodes {
            dfs_within_convex_set(
                node,
                &cin_convex_subset,
                &skeleton_graph,
                &mut targets_reached,
                &mut visited,
            );
        }

        imm_pred_to_imm_succs_connection_via_cin.insert(*imm_pred, targets_reached);
    }

    #[cfg(feature = "trace")]
    {
        log::trace!(
            "Immediate predecessors to Immediate succesors connections via C^in: {:?}",
            imm_pred_to_imm_succs_connection_after_cin
        );
    }

    // Find immPred and immSucc pairs that existed via C^out but do not exist via C^in
    let mut imm_pred_imm_succs_disconnected = imm_pred_to_imm_succs_connection_via_cout;
    for (imm_pred, imm_succ_set_cout) in imm_pred_imm_succs_disconnected.iter_mut() {
        let imm_succ_set_cin = imm_pred_to_imm_succs_connection_via_cin
            .get(imm_pred)
            .unwrap();

        let had_len = imm_succ_set_cout.len();

        // only retain immediate successors that are no more connected with imm pred via C^in
        imm_succ_set_cout.retain(|n| !imm_succ_set_cin.contains(n));

        {
            if !imm_succ_set_cout.is_empty() {
                log::trace!(
                    "Immediate Predecessor {} was conn with {} many via C^out, is conn with {} many via C^in. {} missing connections",
                    skeleton_graph.node_weight(*imm_pred).unwrap(),
                    had_len,
                    imm_succ_set_cin.len(),
                    imm_succ_set_cout.len()
                );
            }
        }

        // assert!(imm_succ_set_cout.is_empty());
    }

    // Create missing conections
    #[cfg(feature = "trace")]
    {
        log::trace!(
            "Missing connections {:?}",
            imm_pred_imm_succs_to_create_conn
        );
    }

    // for (imm_pred, succs) in imm_pred_imm_succs_to_create_conn.iter() {
    //     let pred_gate = gate_map
    //         .get(skeleton_graph.node_weight(*imm_pred).unwrap())
    //         .unwrap();

    //     for s in succs.iter() {
    //         let mut path = vec![];
    //         // Depedency chains to be adjusted with pred's predecessors
    //         let mut nodes_colliding_with_pred = HashSet::new();
    //         let mut dependency_chains = vec![];

    //         dfs_till_collision(
    //             pred_gate,
    //             s,
    //             &skeleton_graph,
    //             &gate_map,
    //             path,
    //             colliding_nodes,
    //             dependency_chains,
    //             visited,
    //         );
    //     }
    // }

    // let mut disconnected_successors_dependencies = HashMap::new();
    // let all_disconneted_successors = HashSet::from_iter(
    //     imm_pred_imm_succs_to_create_conn
    //         .values()
    //         .flat_map(|v| v.iter()),
    // );
    // for n in all_disconneted_successors {
    //     // dfs_till_collision(target_gate, curr_node, graph, gate_map, path, colliding_nodes, dependency_chains, visited);
    // }

    let edges_to_add: Vec<HashSet<(NodeIndex, NodeIndex)>> = timed!(
        "Fix missing connections via C^in",
        imm_pred_imm_succs_disconnected
            .par_iter()
            .map(|(imm_pred, imm_succ_prev_connnected)| {
                let mut tmp = HashSet::new();
                for imm_succ in imm_succ_prev_connnected {
                    let edges = adjust_dependencies_for_prev_connected_nodes(
                        *imm_pred,
                        *imm_succ,
                        &skeleton_graph,
                        &gate_map,
                    );
                    tmp.extend(edges);
                }
                tmp
            })
            .collect()
    );

    let mut new_edges = HashSet::new();

    for e in edges_to_add {
        new_edges.extend(e);
    }
    log::trace!(
        "       New edges count for missing links: {}",
        new_edges.len()
    );

    // timed!(
    //     "Fix missing connections via C^in",
    //     for (imm_pred, imm_succ_prev_connnected) in imm_pred_imm_succs_disconnected {
    //         for imm_succ in imm_succ_prev_connnected {
    //             let edges = adjust_dependencies_for_prev_connected_nodes(
    //                 imm_pred,
    //                 imm_succ,
    //                 &skeleton_graph,
    //                 &gate_map,
    //             );
    //             new_edges.extend(edges);
    //         }
    //     }
    // );

    // Update the graph with new edges
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

pub fn test_circuit_equivalance<G, R: RngCore>(
    circuit0: &Circuit<G>,
    circuit1: &Circuit<G>,
    rng: &mut R,
) where
    G: Gate<Input = [bool]>,
{
    assert_eq!(circuit0.n(), circuit1.n());
    let n = circuit0.n();

    for value in rng.sample_iter(Uniform::new(0, 1u128 << n - 1)).take(10000) {
        // for value in 0..1u128 << 15 {
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

pub fn test_circuit_equivalance_for_debug<G, R: RngCore>(
    circuit0: &Circuit<G>,
    mixed_circuit: &Circuit<G>,
    rng: &mut R,
) -> Option<Vec<usize>>
where
    G: Gate<Input = [bool]>,
{
    assert_eq!(circuit0.n(), mixed_circuit.n());
    let n = circuit0.n();

    for value in rng.sample_iter(Uniform::new(0, 1u128 << n - 1)).take(10000) {
        // for value in 0..1u128 << 15 {
        let mut inputs = vec![];
        for i in 0..n {
            inputs.push((value >> i) & 1u128 == 1);
        }

        let mut inputs0 = inputs.clone();
        circuit0.run(&mut inputs0);

        let mut inputs1 = inputs.clone();
        mixed_circuit.run(&mut inputs1);

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

        if inputs0 != inputs1 {
            return Some(diff_indices);
        }

        // assert_eq!(inputs0, inputs1, "Different at indices {:?}", diff_indices);
    }

    None
}

#[cfg(test)]
mod tests {
    use circuit::{circuit_to_skeleton_graph, sample_circuit_with_base_gate};
    use petgraph::{
        algo::{all_simple_paths, has_path_connecting, toposort},
        dot::{Config, Dot},
    };
    use rand::{thread_rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[test]
    fn test_local_mixing() {
        env_logger::init();

        let gates = 100;
        let n = 15;
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

            log::info!(
                "Topological order after local mixing iteration: {:?}",
                &node_indices_to_gate_ids(top_sorted_nodes.iter(), &skeleton_graph)
            );

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

                let mixed_circuit = Circuit::from_top_sorted_nodes(
                    &top_sorted_nodes,
                    &skeleton_graph,
                    &gate_map,
                    original_circuit.n(),
                );
                test_circuit_equivalance(&original_circuit, &mixed_circuit, &mut rng);

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
        let gates = 50;
        let n = 10;
        let ell_out = 5;
        let max_iterations = 10000;
        let mut rng = thread_rng();

        let mut iter = 0;
        while iter < 1000 {
            let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
            let skeleton_graph = circuit_to_skeleton_graph(&circuit);

            let convex_subgraph =
                find_convex_subcircuit(&skeleton_graph, ell_out, max_iterations, &mut rng);

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
    fn test_dependency_chains_from_collision_set() {
        let mut rng = thread_rng();
        let gates = 5;
        let n = 3;
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let collisions = circuit_to_collision_sets(&circuit);
        let chains = dependency_chains_from_collision_set(&collisions);

        let skeleton_graph = circuit_to_skeleton_graph(&circuit);

        println!(
            "Graph: {:?}",
            Dot::with_config(
                &skeleton_graph,
                &[Config::EdgeNoLabel, Config::NodeIndexLabel],
            )
        );

        // find chain in the graph
        fn dfs(
            curr_node: NodeIndex,
            visited: &mut HashSet<NodeIndex>,
            path: &mut Vec<NodeIndex>,
            chains: &mut Vec<Vec<NodeIndex>>,
        ) {
        }

        dbg!(chains);
    }
}
