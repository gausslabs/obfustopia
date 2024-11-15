use bitvec::{array::BitArray, bitarr, order::Lsb0, vec::BitVec};
use circuit::{BaseGate, Circuit, Gate};
use either::Either::{Left, Right};
use itertools::{chain, izip, Itertools};
use num_traits::Zero;
use petgraph::{
    algo::toposort,
    graph::{EdgeIndex, Node, NodeIndex},
    visit::{EdgeRef, IntoNodeIdentifiers},
    Direction::{self, Outgoing},
    Graph,
};
use rand::{
    distributions::{uniform::SampleUniform, Uniform},
    seq::SliceRandom,
    Rng, RngCore, SeedableRng,
};
use rayon::{
    current_num_threads,
    iter::{
        IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator,
        IntoParallelRefMutIterator, ParallelBridge, ParallelIterator,
    },
    slice::{ParallelSlice, ParallelSliceMut},
};
use std::{
    array::from_fn,
    collections:: VecDeque,
    fmt::{Debug, Display},
    hash::Hash,
    iter::{self, repeat_with},
    ops::Deref,
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed},
        Arc, Mutex,
    },
    time::Duration,
};
use hashbrown::{HashMap, HashSet};

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

#[allow(dead_code)]
fn edges_to_string(edges: &HashSet<(usize, usize)>) -> String {
    let mut string = String::from("[");
    for edge in edges.iter() {
        string = format!("{string} ({}, {}),", edge.0, edge.1);
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
    // let mut sample_trace = Sha256::new();
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
            let control_func = rng.next_u64() as u8 % BaseGate::<MAX_K, D>::N_CONTROL_FUNC;
            // let control_func = 1;

            // sample_trace.update(format!("TWO{target}{}{}", controls[0], controls[1],));

            curr_gate += two_replacement_cost;

            gates.push(BaseGate::<MAX_K, D>::new(
                id,
                target,
                controls,
                control_func,
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
                let control_func = loop {
                    let v = rng.next_u64() as u8;
                    if v < BaseGate::<MAX_K, D>::N_CONTROL_FUNC {
                        break v;
                    }
                };
                // sample_trace.update(format!(
                //     "THREE{target}{}{}{}",
                //     controls[0], controls[1], controls[2]
                // ));

                curr_gate += three_replacement_cost;

                gates.push(BaseGate::<MAX_K, D>::new(
                    id,
                    target,
                    controls,
                    control_func,
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

                let control_func = loop {
                    let v = rng.next_u64() as u8;
                    if v < BaseGate::<MAX_K, D>::N_CONTROL_FUNC {
                        break v;
                    }
                };

                // sample_trace.update(format!("TWO{target}{}{}", controls[0], controls[1],));

                curr_gate += two_replacement_cost;

                gates.push(BaseGate::<MAX_K, D>::new(
                    id,
                    target,
                    controls,
                    control_func,
                ));
            };
        }

        id += 1;
    }

    // let sample_trace: String = format!("{:X}", sample_trace.finalize());

    (Circuit::new(gates, n.into()), String::new())
}

pub fn sample_circuit_with_base_gate_fast<R: Rng>(
    circuit: &mut Circuit<BaseGate<2, u8>>,
    n: u8,
    rng: &mut R,
) {
    let set: [bool; 16] = from_fn(|i| (i as u8) >= n);
    let mut rng = repeat_with(|| rng.next_u32()).flat_map(|v| v.to_le_bytes());

    izip!(0.., circuit.gates_mut()).for_each(|(id, gate)| {
        let mut set = set;
        let [t, c0, c1] = from_fn(|_| loop {
            let v = rng.next().unwrap();
            if !set[(v & 15) as usize] {
                set[(v & 15) as usize] = true;
                break (v & 15);
            }
            if !set[(v >> 4) as usize] {
                set[(v >> 4) as usize] = true;
                break (v >> 4);
            }
        });
        let control_func = rng.next().unwrap() % BaseGate::<2, u8>::N_CONTROL_FUNC;
        // let control_func = 1;
        *gate = BaseGate::<2, u8>::new(id, t, [c0, c1], control_func);
    });
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

fn find_replacement_circuit<
    const MAX_K: usize,
    const WC: bool,
    D,
    R: Send + Sync + RngCore + SeedableRng,
>(
    circuit: &Circuit<BaseGate<MAX_K, D>>,
    ell_in: usize,
    n: D,
    two_prob: f64,
    max_iterations: usize,
    rng: &mut R,
) -> Option<Circuit<BaseGate<MAX_K, D>>>
where
    D: Send
        + Sync
        + Zero
        + SampleUniform
        + Copy
        + Eq
        + Hash
        + Display
        + Debug
        + Into<usize>
        + PartialEq
        + Eq,
{
    let input_value_to_bitstring_map = input_value_to_bitstring_map(circuit.n());
    let permutation_map = permutation_map(circuit, &input_value_to_bitstring_map);

    // let mut visited_circuits = HashMap::new();
    let max_iterations = max_iterations / current_num_threads();

    (0..current_num_threads())
        .map(|_| R::from_rng(&mut *rng).unwrap())
        .collect_vec()
        .into_par_iter()
        .find_map_any(|mut rng| {
            let mut curr_iter = 0;
            let mut replacement_circuit = None;

            while curr_iter < max_iterations {
                let (random_circuit, _) =
                    sample_circuit_with_base_gate::<MAX_K, D, _>(ell_in, n, two_prob, &mut rng);

                let mut funtionally_equivalent = true;
                for (value, bitstring) in input_value_to_bitstring_map.iter() {
                    let mut inputs = bitstring.to_vec();
                    random_circuit.run(&mut inputs);

                    if &inputs != permutation_map.get(value).unwrap() {
                        funtionally_equivalent = false;
                        break;
                    }
                }

                if funtionally_equivalent {
                    funtionally_equivalent = &random_circuit != circuit
                }

                if funtionally_equivalent && WC {
                    let collisions_set = circuit_to_collision_sets(&random_circuit);
                    let is_weakly_connected = is_collisions_set_weakly_connected(&collisions_set);
                    #[cfg(feature = "trace")]
                    {
                        if funtionally_equivalent && !is_weakly_connected {
                            log::trace!("[find_replacement_circuit] wft");
                        }
                    }
                    funtionally_equivalent = is_weakly_connected;
                }

                if funtionally_equivalent {
                    replacement_circuit = Some(random_circuit);
                    break;
                }

                curr_iter += 1;

                #[cfg(feature = "trace")]
                if curr_iter % 10000000 == 0 {
                    log::trace!("[find_replacement_circuit] 100K iterations done",);
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
            log::trace!(
                "Finding replacement total iterations: {}",
                curr_iter,
                // visited_circuits
                //     .values()
                //     .counts()
                //     .into_iter()
                //     .sorted()
                //     .collect_vec()
            );
            // println!("Visited frequency: {:?}", visited_freq);

            replacement_circuit
        })
}

fn find_replacement_circuit_fast<R: Send + Sync + RngCore + SeedableRng>(
    circuit: &Circuit<BaseGate<2, u8>>,
    ell_in: usize,
    n: usize,
    max_iterations: usize,
    rng: &mut R,
) -> Option<Circuit<BaseGate<2, u8>>> {
    return match n {
        3 => inner::<_, 3, { 1 << 3 }>(circuit, ell_in, max_iterations, rng),
        4 => inner::<_, 4, { 1 << 4 }>(circuit, ell_in, max_iterations, rng),
        5 => inner::<_, 5, { 1 << 5 }>(circuit, ell_in, max_iterations, rng),
        6 => inner::<_, 6, { 1 << 6 }>(circuit, ell_in, max_iterations, rng),
        7 => inner::<_, 7, { 1 << 7 }>(circuit, ell_in, max_iterations, rng),
        8 => inner::<_, 8, { 1 << 8 }>(circuit, ell_in, max_iterations, rng),
        9 => inner::<_, 9, { 1 << 9 }>(circuit, ell_in, max_iterations, rng),
        10 => inner::<_, 10, { 1 << 10 }>(circuit, ell_in, max_iterations, rng),
        11 => inner::<_, 11, { 1 << 11 }>(circuit, ell_in, max_iterations, rng),
        _ => unimplemented!(),
    };

    fn inner<R: Send + Sync + RngCore + SeedableRng, const N: usize, const N2: usize>(
        circuit: &Circuit<BaseGate<2, u8>>,
        ell_in: usize,
        max_iterations: usize,
        rng: &mut R,
    ) -> Option<Circuit<BaseGate<2, u8>>> {
        let mut permutations: [_; N2] = from_fn(|i| {
            let inputs = from_fn::<_, N, _>(|j| (i >> j) & 1 == 1);
            let mut outputs = inputs;
            circuit.run(&mut outputs);
            (inputs, outputs)
        });

        permutations.shuffle(rng);

        // let mut visited_circuits = HashMap::new();
        let max_iterations = max_iterations / current_num_threads();
        let found = AtomicBool::new(false);

        (0..current_num_threads())
            .map(|_| R::from_rng(&mut *rng).unwrap())
            .par_bridge()
            .find_map_any(|mut rng| {
                let epoch_size = rng.gen_range(10..20);
                let mut curr_iter = 0;
                let mut replacement_circuit = None;

                let mut random_circuit =
                    Circuit::new(vec![BaseGate::new(0, 0, [0, 0], 0); ell_in], N);

                while curr_iter < max_iterations {
                    if curr_iter % epoch_size == 0 && found.load(Relaxed) {
                        return None;
                    }

                    sample_circuit_with_base_gate_fast(&mut random_circuit, N as u8, &mut rng);

                    let mut funtionally_equivalent = true;
                    for (inputs, map) in &permutations {
                        let mut inputs = *inputs;
                        random_circuit.run(&mut inputs);

                        if &inputs != map {
                            funtionally_equivalent = false;
                            break;
                        }
                    }

                    if funtionally_equivalent {
                        funtionally_equivalent = &random_circuit != circuit
                    }

                    if funtionally_equivalent {
                        let collisions_set = circuit_to_collision_sets(&random_circuit);
                        let is_weakly_connected =
                            is_collisions_set_weakly_connected(&collisions_set);
                        funtionally_equivalent = is_weakly_connected;
                    }

                    if funtionally_equivalent {
                        replacement_circuit = Some(random_circuit);
                        found.store(true, Relaxed);
                        break;
                    }

                    curr_iter += 1;

                    #[cfg(feature = "trace")]
                    if curr_iter % 10000000 == 0 {
                        log::trace!("[find_replacement_circuit] 100K iterations done",);
                    }
                }

                // println!("sampling: {t0:?}, check: {t1:?}");

                #[cfg(feature = "trace")]
                log::trace!("Finding replacement total iterations: {}", curr_iter,);

                replacement_circuit
            })
    }
}

fn dfs_fast(
    graph: &Graph<usize, usize>,
    sources: Vec<NodeIndex>,
    direction: Direction,
    removed_nodes: &HashSet<NodeIndex>,
) -> HashSet<NodeIndex> {
    let visited = repeat_with(|| AtomicBool::new(false))
        .take(graph.node_count())
        .collect_vec();
    sources.par_iter().for_each(|s| {
        visited[s.index()].swap(true, Relaxed);
    });
    let stack = Arc::new(Mutex::new(sources));

    (0..current_num_threads()).into_par_iter().for_each(|_| {
        let mut next = None;
        while let Some(curr) = next.take().or_else(|| stack.lock().unwrap().pop()) {
            let mut succs = graph
                .neighbors_directed(curr, direction)
                .filter(|node| !removed_nodes.contains(node))
                .flat_map(|succ| (!visited[succ.index()].swap(true, Relaxed)).then_some(succ))
                .collect_vec();
            next = succs.pop();
            if !succs.is_empty() {
                stack.lock().unwrap().extend(succs);
            }
        }
    });

    visited
        .into_par_iter()
        .enumerate()
        .flat_map(|(i, visited)| {
            visited.into_inner().then(|| {
                assert!(!removed_nodes.contains(&NodeIndex::from(i as u32)));
                NodeIndex::from(i as u32)
            })
        })
        .collect()
}

fn dfs(
    curr_node: NodeIndex,
    visited_with_path: &mut HashSet<NodeIndex>,
    visited: &mut HashSet<NodeIndex>,
    path: &mut Vec<NodeIndex>,
    graph: &Graph<usize, usize>,
    direction: Direction,
    removed_nodes: &HashSet<NodeIndex>,
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
    for v in graph
        .neighbors_directed(curr_node.into(), direction)
        .filter(|node| !removed_nodes.contains(node))
    {
        dfs(
            v,
            visited_with_path,
            visited,
            path,
            graph,
            direction,
            removed_nodes,
        );
    }
    path.pop();
    visited.insert(curr_node);
}

fn dfs2(
    curr_node: NodeIndex,
    visited_with_path: &mut HashSet<NodeIndex>,
    visited: &mut HashSet<NodeIndex>,
    path: &mut Vec<NodeIndex>,
    graph: &Graph<usize, usize>,
    direction: Direction,
    break_when: usize,
    max_level: usize,
    level: &[usize],
    removed_nodes: &HashSet<NodeIndex>,
) -> bool {
    assert!(!removed_nodes.contains(&curr_node));

    if visited_with_path.len() > break_when {
        return false;
    }

    if visited_with_path.contains(&curr_node) {
        path.iter().for_each(|node| {
            visited_with_path.insert(*node);
        });
        return true;
    }

    if visited.contains(&curr_node) || level[curr_node.index()] >= max_level {
        return true;
    }

    let mut return_bool = true;
    path.push(curr_node.clone());
    for v in graph
        .neighbors_directed(curr_node.into(), direction)
        .filter(|node| !removed_nodes.contains(node))
    {
        return_bool = return_bool
            && dfs2(
                v,
                visited_with_path,
                visited,
                path,
                graph,
                direction,
                break_when,
                max_level,
                level,
                removed_nodes,
            );

        if !return_bool {
            return false;
        }
    }

    path.pop();
    visited.insert(curr_node);
    return return_bool;
}

fn blah(
    desire_set_size: usize,
    convex_set: &mut HashSet<NodeIndex>,
    graph: &Graph<usize, usize>,
    level: &[usize],
    removed_nodes: &HashSet<NodeIndex>,
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
                    let mut edge_iter = graph
                        .neighbors_directed(*source_node, Direction::Outgoing)
                        .filter(|node| !removed_nodes.contains(node));
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
        let dfs_did_not_break = dfs2(
            *source,
            &mut union_visited_with_path,
            &mut union_visited,
            &mut path,
            &graph,
            Direction::Outgoing,
            desire_set_size,
            level[candidate_node.index()],
            level,
            removed_nodes,
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
            return blah(desire_set_size, convex_set, graph, level, removed_nodes);
        } else {
            return true;
        }
    } else {
        return false;
    }
}

// Copied from https://stackoverflow.com/a/65182786/7705999
struct UnsafeSlice<'a, T> {
    slice: &'a [core::cell::UnsafeCell<T>],
}
unsafe impl<'a, T: Send + Sync> Send for UnsafeSlice<'a, T> {}
unsafe impl<'a, T: Send + Sync> Sync for UnsafeSlice<'a, T> {}

impl<'a, T> UnsafeSlice<'a, T> {
    pub fn new(slice: &'a mut [T]) -> Self {
        let ptr = slice as *mut [T] as *const [core::cell::UnsafeCell<T>];
        Self {
            slice: unsafe { &*ptr },
        }
    }

    /// SAFETY: It is UB if two threads write to the same index without
    /// synchronization.
    pub unsafe fn write(&self, i: usize, value: T) {
        let ptr = self.slice[i].get();
        *ptr = value;
    }

    /// SAFETY: It is UB if two threads update the same index without
    /// synchronization.
    pub unsafe fn update(&self, i: usize, f: impl Fn(&mut T)) {
        let ptr = self.slice[i].get();
        f(&mut *ptr);
    }
}

fn find_all_predecessors(
    convex_set: &HashSet<NodeIndex>,
    graph: &Graph<usize, usize>,
    removed_nodes: &HashSet<NodeIndex>,
) -> HashSet<NodeIndex> {
    // Find all predecessors and successors of subgrpah C^out
    let mut imm_predecessors = HashSet::new();

    // First find all immediate predecessors and successors
    for node in convex_set.iter() {
        for pred in graph
            .neighbors_directed(node.clone(), Direction::Incoming)
            .filter(|node| !removed_nodes.contains(node))
        {
            if !convex_set.contains(&pred) {
                imm_predecessors.insert(pred);
            }
        }
    }

    let predecessors = dfs_fast(
        graph,
        Vec::from_iter(imm_predecessors.clone()),
        Direction::Incoming,
        removed_nodes,
    );

    return predecessors;
}

fn find_all_successors(
    convex_set: &HashSet<NodeIndex>,
    graph: &Graph<usize, usize>,
    removed_nodes: &HashSet<NodeIndex>,
) -> HashSet<NodeIndex> {
    let mut imm_successors = HashSet::new();
    // First find all immediate predecessors and successors
    for node in convex_set.iter() {
        for succ in graph
            .neighbors_directed(node.clone(), Direction::Outgoing)
            .filter(|node| !removed_nodes.contains(node))
        {
            if !convex_set.contains(&succ) {
                imm_successors.insert(succ);
            }
        }
    }

    let successors = dfs_fast(
        graph,
        Vec::from_iter(imm_successors.clone()),
        Direction::Outgoing,
        removed_nodes,
    );

    return successors;
}

pub fn toposort_with_cached_graph_neighbours(
    skeleton_graph: &Graph<usize, usize>,
    graph_neighbors: &[[HashSet<NodeIndex>; 2]],
    removed_nodes: &HashSet<NodeIndex>,
) -> Vec<NodeIndex> {
    let levels = graph_level_single_threaded(&skeleton_graph, &graph_neighbors, removed_nodes);
    let mut node_indices = skeleton_graph
        .node_indices()
        .into_iter()
        .filter(|node| !removed_nodes.contains(node))
        .collect_vec();
    node_indices.par_sort_by(|a, b| levels[a.index()].cmp(&levels[b.index()]));
    node_indices
}

fn graph_neighbors(
    graph: &Graph<usize, usize>,
    removed_nodes: &HashSet<NodeIndex>,
) -> Vec<[HashSet<NodeIndex>; 2]> {
    (0..graph.node_count() as _)
        .into_par_iter()
        .map(|n| {
            if removed_nodes.contains(&NodeIndex::from(n)) {
                [HashSet::new(), HashSet::new()]
            } else {
                [Direction::Incoming, Direction::Outgoing].map(|dir| {
                    graph
                        .neighbors_directed(NodeIndex::from(n), dir)
                        .filter(|node| !removed_nodes.contains(node))
                        .collect()
                })
            }
        })
        .collect()
}

fn update_graph_neighbors(
    graph: &Graph<usize, usize>,
    in_degree: &mut Vec<[HashSet<NodeIndex>; 2]>,
    to_remove_nodes: &HashSet<NodeIndex>,
    incoming: HashSet<NodeIndex>,
    removed_nodes: &HashSet<NodeIndex>,
) {
    to_remove_nodes.iter().for_each(|n| {
        let incoming = &mut in_degree[n.index()][0];
        *incoming = HashSet::new();
        let outgoing = &mut in_degree[n.index()][1];
        *outgoing = HashSet::new();
    });


    in_degree.resize_with(graph.node_count(), Default::default);
    let in_degree_slice = UnsafeSlice::new(in_degree);
    incoming.into_par_iter().for_each(|n| unsafe {
        assert!(!removed_nodes.contains(&n));
        in_degree_slice.update(n.index(), |[incoming, outgoing]| {
            *incoming = graph
                .neighbors_directed(n, Direction::Incoming)
                .filter(|node| !removed_nodes.contains(node))
                .collect();
            *outgoing = graph
                .neighbors_directed(n, Direction::Outgoing)
                .filter(|node| !removed_nodes.contains(node))
                .collect()
        })
    });
}

/// Implements Kahn's algorithm. Instead of the original graph it uses cached incoming and outgoing edges per edge
fn graph_level_single_threaded(
    graph: &Graph<usize, usize>,
    graph_neighbors: &[[HashSet<NodeIndex>; 2]],
    removed_nodes: &HashSet<NodeIndex>,
) -> Vec<usize> {
    let mut stack = Vec::new();
    let mut degree = graph_neighbors
        .iter()
        .enumerate()
        .map(|(n, [incomings, _])| {
            let node = NodeIndex::from(n as u32);
            if incomings.is_empty() && !removed_nodes.contains(&node) {
                stack.push(node);
            }
            (incomings.len(), 0)
        })
        .collect::<Vec<_>>();
    let mut level = vec![0; graph.node_count()];
    let mut next = None;
    while let Some(curr) = next.take().or_else(|| stack.pop()) {
        let curr_level = level[curr.index()];
        graph_neighbors[curr.index()][1].iter().for_each(|succ| {
            assert!(!removed_nodes.contains(succ));
            let (succ_in_degree, succ_level) = &mut degree[succ.index()];
            *succ_in_degree -= 1;
            *succ_level = std::cmp::max(curr_level + 1, *succ_level);
            level[succ.index()] = *succ_level;
            if *succ_in_degree == 0 {
                stack.push(*succ);
            }
        });
    }
    level
}

pub fn graph_level(
    graph: &Graph<usize, usize>,
    graph_neighbors: &[[HashSet<NodeIndex>; 2]],
    removed_nodes: &HashSet<NodeIndex>,
) -> Vec<usize> {
    let stack = Arc::new(Mutex::new(Vec::new()));
    let degree = graph_neighbors
        .par_iter()
        .enumerate()
        .filter_map(|(n, [incomings, _])| {
            if incomings.is_empty() && !removed_nodes.contains(&NodeIndex::from(n as u32)) {
                stack.lock().unwrap().push(NodeIndex::from(n as u32));
            }

            // for i in incomings.iter() {
            //     assert!(
            //         !removed_nodes.contains(i),
            //         "[graph_level] Removed node {} found in incoming neighbours of node {}",
            //         i.index(),
            //         n
            //     );
            // }

            return Some((AtomicUsize::new(incomings.len()), AtomicUsize::new(0)));
        })
        .collect::<Vec<_>>();
    let mut level = vec![0; graph.node_count()];
    let level_slice = UnsafeSlice::new(&mut level);
    (0..current_num_threads()).into_par_iter().for_each(|_| {
        let mut next = None;
        while let Some(curr) = next.take().or_else(|| stack.lock().unwrap().pop()) {
            let curr_level = degree[curr.index()].1.load(Relaxed);
            unsafe { level_slice.write(curr.index(), curr_level) };
            let mut succs = graph_neighbors[curr.index()][1]
                .iter()
                // .filter(|node| !removed_nodes.contains(*node))
                .flat_map(|succ| {
                    assert!(!removed_nodes.contains(succ));
                    let (succ_degree, succ_level) = &degree[succ.index()];
                    let succ_degree = succ_degree.fetch_sub(1, Relaxed);
                    succ_level
                        .fetch_update(Relaxed, Relaxed, |succ_level| {
                            Some(succ_level.max(curr_level + 1))
                        })
                        .unwrap();
                    (succ_degree == 1).then_some(*succ)
                })
                .collect_vec();
            // next = succs.pop();
            if !succs.is_empty() {
                stack.lock().unwrap().extend(succs);
            }
        }
    });
    level
}

fn find_convex_fast<R: Send + Sync + RngCore + SeedableRng>(
    graph: &Graph<usize, usize>,
    level: &[usize],
    ell_out: usize,
    max_iterations: usize,
    rng: &mut R,
    removed_nodes: &HashSet<NodeIndex>,
) -> Option<(NodeIndex, HashSet<NodeIndex>)> {
    let max_iterations = max_iterations / current_num_threads();

    let found = AtomicBool::new(false);

    (0..current_num_threads())
        .map(|_| R::from_rng(&mut *rng).unwrap())
        .par_bridge()
        .find_map_any(|mut rng| {
            let epoch_size = rng.gen_range(5..10);
            let mut t = Duration::default();
            let mut curr_iter = 0;
            let mut return_set = None;
            for start_node in (0..graph.node_count())
                .filter(|index| !removed_nodes.contains(&NodeIndex::from(*index as u32)))
                .collect_vec()
                .choose_multiple(&mut rng, max_iterations)
                .into_iter()
                .map(|v| NodeIndex::from(*v as u32))
            {
                assert!(
                    !removed_nodes.contains(&start_node),
                    "[find_convex_fast] Start node is in removed_nodes set"
                );

                if curr_iter % epoch_size == 0 && found.load(Relaxed) {
                    return None;
                }

                let mut convex_set = HashSet::new();
                convex_set.insert(start_node);

                let sttt = std::time::Instant::now();
                let moment_of_truth = blah(ell_out, &mut convex_set, graph, &level, removed_nodes);
                t += sttt.elapsed();

                if moment_of_truth {
                    assert!(convex_set.len() == ell_out);
                    return_set = Some((start_node, convex_set));
                    found.store(true, Relaxed);
                    break;
                } else {
                    curr_iter += 1;
                }
            }

            #[cfg(feature = "trace")]
            log::trace!("Find convex subcircuit iterations: {curr_iter}");

            // println!("find_convex_fast_iter: {curr_iter}, blah: {t:?}");

            return_set
        })
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
        let mut collisions_set_i = all_collision_sets[i].clone();
        for (j, _) in circuit.gates().iter().enumerate().skip(i + 1) {
            if all_collision_sets[i].contains(&j) {
                // remove id k from set of i iff k is in set of j (ie j, where j < k, collides with k)
                collisions_set_i.retain(|k| !all_collision_sets[j].contains(k));
            }
        }
        all_collision_sets[i] = collisions_set_i;
    }

    return all_collision_sets;
}

pub fn prepare_circuit<G: Gate>(
    circuit: &Circuit<G>,
) -> (
    HashMap<usize, HashSet<usize>>,
    HashMap<usize, HashSet<usize>>,
    Graph<usize, usize>,
    HashMap<usize, NodeIndex>,
    HashMap<usize, G>,
    Vec<[HashSet<NodeIndex>; 2]>,
    HashSet<(usize, usize)>,
    usize,
)
where
    G: Clone,
{
    let mut direct_connections_outgoing = Vec::with_capacity(circuit.gates().len());

    for (i, gi) in circuit.gates().iter().enumerate() {
        let mut direct_collisions_i = HashSet::new();
        for (j, gj) in (circuit.gates().iter().enumerate()).skip(i + 1) {
            if gi.check_collision(gj) {
                direct_collisions_i.insert(j);
            }
        }
        direct_connections_outgoing.push(direct_collisions_i);
    }

    let mut direct_incoming_connections_map = HashMap::new();
    for (i, gi) in circuit.gates().iter().enumerate().rev() {
        let mut direct_incoming_conn_i = HashSet::new();
        for (j, gj) in (circuit.gates().iter().enumerate().rev()).skip(circuit.gates().len() - i) {
            if gi.check_collision(gj) {
                direct_incoming_conn_i.insert(gj.id());
            }
        }
        direct_incoming_connections_map.insert(gi.id(), direct_incoming_conn_i);
    }

    let mut transitive_connections = Vec::with_capacity(circuit.gates().len());
    // Remove intsecting collisions. That is i can collide with j iff there is no k such that i < k < j with which both i & j collide
    for (i, _) in circuit.gates().iter().enumerate() {
        // Don't update collision set i in place. Otherwise situations like the following are missed: Let i collide with j < k < l. '
        // If i^th collision set is updated in place then k is removed from the set after checking against j^th collision set. And i^th
        // collision set will never be checked against k. Hence, an incorrect (or say unecessary) dependency will be drawn from i to l.
        let mut transitive_connections_i = direct_connections_outgoing[i].clone();
        // for (j, _) in circuit.gates().iter().enumerate().skip(i + 1) {
        //     if direct_connections[i].contains(&j) {
        //         // remove id k from set of i iff k is in set of j (ie j, where j < k, collides with k)
        //         transitive_connections_i.retain(|k| !direct_connections[j].contains(k));
        //     }
        // }

        for j in direct_connections_outgoing[i].iter() {
            transitive_connections_i.retain(|k| !direct_connections_outgoing[*j].contains(k));
        }

        transitive_connections.push(transitive_connections_i);
    }

    // direct connections map
    let mut direct_connections_map = HashMap::new();
    for (index, connections) in direct_connections_outgoing.into_iter().enumerate() {
        let conn = HashSet::from_iter(connections.iter().map(|i| circuit.gates()[*i].id()));
        direct_connections_map.insert(circuit.gates()[index].id(), conn);
    }

    // edge collection
    let mut active_edges_with_gateids = HashSet::new();

    // create skeleton graph with transitive connections
    let mut skeleton = Graph::<usize, usize>::new();
    // add nodes with weights as ids
    let nodes = circuit
        .gates()
        .iter()
        .map(|g| skeleton.add_node(g.id()))
        .collect_vec();
    transitive_connections
        .iter()
        .enumerate()
        .for_each(|(i, set)| {
            // FIXME(Jay): Had to collect_vec due to lifetime issues
            set.iter().for_each(|j| {
                active_edges_with_gateids
                    .insert((circuit.gates()[i].id(), circuit.gates()[*j].id()));
                skeleton.update_edge(nodes[i], nodes[*j], Default::default());
            });
        });

    // create gate id to gate map
    let mut gate_map = HashMap::new();
    let mut latest_id = 0;
    for gate in circuit.gates() {
        latest_id = std::cmp::max(latest_id, gate.id());
        gate_map.insert(gate.id(), gate.clone());
    }

    // create gate id to node index map
    let mut gate_id_to_node_index_map = HashMap::new();
    for node in skeleton.node_indices() {
        gate_id_to_node_index_map.insert(*skeleton.node_weight(node).unwrap(), node);
    }

    let graph_neighbours = graph_neighbors(&skeleton, &HashSet::new());

    (
        direct_connections_map,
        direct_incoming_connections_map,
        skeleton,
        gate_id_to_node_index_map,
        gate_map,
        graph_neighbours,
        active_edges_with_gateids,
        latest_id,
    )
}

pub fn dfs_within_convex_set(
    curr_node: NodeIndex,
    convex_set: &HashSet<NodeIndex>,
    graph: &Graph<usize, usize>,
    visited: &mut HashSet<NodeIndex>,
    top_sorted: &mut VecDeque<NodeIndex>,
) {
    if visited.contains(&curr_node) {
        return;
    }

    for succ in graph
        .neighbors_directed(curr_node, Direction::Outgoing)
        .filter(|n| convex_set.contains(n))
    {
        dfs_within_convex_set(succ, convex_set, graph, visited, top_sorted);
    }

    visited.insert(curr_node);
    top_sorted.push_front(curr_node);
}

/// Local mixing step
///
/// Returns false if mixing step is not successuful which may happen if one of the following is true
/// - Elements in convex subset < \ell^out
/// - \omega^out <= 3
/// - Not able to find repalcement circuit after exhausting max_replacement_iterations iterations
pub fn local_mixing_step<R: Send + Sync + SeedableRng + RngCore>(
    skeleton_graph: &mut Graph<usize, usize>,
    ell_in: usize,
    ell_out: usize,
    n: u8,
    direct_connections: &mut HashMap<usize, HashSet<usize>>,
    direct_incoming_connections: &mut HashMap<usize, HashSet<usize>>,
    gate_map: &mut HashMap<usize, BaseGate<2, u8>>,
    gate_id_to_node_index_map: &mut HashMap<usize, NodeIndex>,
    graph_neighbours: &mut Vec<[HashSet<NodeIndex>; 2]>,
    removed_nodes: &mut HashSet<NodeIndex>,
    active_edges_with_gateids: &mut HashSet<(usize, usize)>,
    latest_id: &mut usize,
    max_replacement_iterations: usize,
    max_convex_iterations: usize,
    rng: &mut R,
) -> bool {
    assert!(ell_out <= ell_in);

    let level = graph_level(skeleton_graph, graph_neighbours, &removed_nodes);

    let (cout_convex_start_node, cout_convex_subset) = timed!(
        "Find convex subcircuit",
        match find_convex_fast(
            &skeleton_graph,
            &level,
            ell_out,
            max_convex_iterations,
            rng,
            removed_nodes
        ) {
            Some((convex_start_node, convex_subset)) => (convex_start_node, convex_subset),
            None => {
                log::trace!("[returned false] Find convex subscircuit");
                return false;
            }
        }
    );

    let mut convex_subset_top_sorted = VecDeque::new();
    dfs_within_convex_set(
        cout_convex_start_node,
        &cout_convex_subset,
        &skeleton_graph,
        &mut HashSet::new(),
        &mut convex_subset_top_sorted,
    );

    // Convex subset sorted in topological order
    let convex_subgraph_top_sorted_gate_ids = convex_subset_top_sorted
        .iter()
        .map(|node_index| skeleton_graph.node_weight(*node_index).unwrap());

    for node in convex_subset_top_sorted.iter() {
        assert!(!removed_nodes.contains(node));
    }

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
    // if omega_out.len() <= 3 {
    //     log::trace!("[returned false] <= active wires");
    //     return false;
    // }

    // Map from old wires to new wires in C^out
    let mut old_to_new_map = HashMap::new();
    let mut new_to_old_map = HashMap::new();
    for (new_index, old_index) in omega_out.iter().enumerate() {
        old_to_new_map.insert(*old_index, new_index as u8);
        new_to_old_map.insert(new_index as u8, *old_index);
    }
    let c_out_gates = convex_subgraph_gates
        .clone()
        .enumerate()
        .map(|(index, gate)| {
            let old_controls = gate.controls();
            let mut new_controls = [0u8; 2];
            new_controls[0] = *old_to_new_map.get(&old_controls[0]).unwrap();
            new_controls[1] = *old_to_new_map.get(&old_controls[1]).unwrap();
            BaseGate::new(
                index,
                *old_to_new_map.get(&gate.target()).unwrap(),
                new_controls,
                gate.control_func(),
            )
        })
        .collect_vec();

    let c_out = Circuit::new(c_out_gates, omega_out.len());

    let c_in_dash = timed!(
        "Find replacement circuit",
        match find_replacement_circuit_fast(
            &c_out,
            ell_in,
            c_out.n(),
            max_replacement_iterations,
            rng,
        ) {
            Some(c_in_dash) => c_in_dash,
            None => {
                log::trace!("[returned false] Find replacement circuit");
                return false;
            }
        }
    );

    let c_in = Circuit::new(
        c_in_dash
            .gates()
            .iter()
            .map(|g| {
                *latest_id += 1;

                let new_controls = g.controls();
                // assert!(new_controls[2] == D::try_from(c_in_dash.n).unwrap());
                let mut old_controls = [0u8; 2];
                old_controls[0] = *new_to_old_map.get(&new_controls[0]).unwrap();
                old_controls[1] = *new_to_old_map.get(&new_controls[1]).unwrap();
                BaseGate::<2, _>::new(
                    *latest_id,
                    *new_to_old_map.get(&g.target()).unwrap(),
                    old_controls,
                    g.control_func(),
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
        log::trace!("@@@@ C^in' @@@@ {}", &c_in_dash);
        // log::trace!("@@@@ C^in @@@@ {}", &c_in);
        let collision_sets_c_in = circuit_to_collision_sets(&c_in_dash);
        log::trace!("C^in collision sets: {:?}", &collision_sets_c_in);
    }

    // #### Replace C^out with C^in #### //

    // Find all predecessors and successors of subgrpah C^out
    let mut c_out_imm_predecessors = HashSet::new();
    let mut c_out_imm_successors = HashSet::new();
    // First find all immediate predecessors and successors
    for node in cout_convex_subset.iter() {
        for pred in skeleton_graph
            .neighbors_directed(node.clone(), Direction::Incoming)
            .filter(|node| !removed_nodes.contains(node))
        {
            if !cout_convex_subset.contains(&pred) {
                c_out_imm_predecessors.insert(pred);
            }
        }
        for succ in skeleton_graph
            .neighbors_directed(node.clone(), Direction::Outgoing)
            .filter(|node| !removed_nodes.contains(node))
        {
            if !cout_convex_subset.contains(&succ) {
                c_out_imm_successors.insert(succ);
            }
        }
    }

    // add C^in gates to the graph
    let cin_gates = c_in.gates();
    let cin_nodes = cin_gates
        .iter()
        .map(|gate| {
            let node_index = skeleton_graph.add_node(gate.id());
            assert!(gate_map.insert(gate.id(), gate.clone()).is_none());
            assert!(gate_id_to_node_index_map
                .insert(gate.id(), node_index)
                .is_none());
            node_index
        })
        .collect_vec();

    let cout_predecessors = timed!(
        "Find all predecessors",
        find_all_predecessors(&cout_convex_subset, &skeleton_graph, removed_nodes)
    );
    let cout_successors = timed!(
        "Find all successors",
        find_all_successors(&cout_convex_subset, &skeleton_graph, removed_nodes)
    );

    assert!(cout_predecessors.is_disjoint(&cout_successors));
    assert!(cout_predecessors.is_disjoint(&removed_nodes));
    assert!(cout_successors.is_disjoint(&removed_nodes));

    let top_sorted_predecessors = {
        let mut top_sorted_predecessors = Vec::from_iter(cout_predecessors.iter().copied());
        top_sorted_predecessors.par_sort_by(|a, b| level[a.index()].cmp(&level[b.index()]));
        top_sorted_predecessors
    };
    let top_sorted_successors = {
        let mut top_sorted_successorss = Vec::from_iter(cout_successors.iter().copied());
        top_sorted_successorss.par_sort_by(|a, b| level[a.index()].cmp(&level[b.index()]));
        top_sorted_successorss
    };
    let top_sorted_outsiders = {
        let insider = HashSet::<_>::from_iter(
            chain![
                &cin_nodes,
                &cout_convex_subset,
                &cout_successors,
                &cout_predecessors,
                removed_nodes.deref()
            ]
            .copied(),
        );
        let mut top_sorted_outsiders = skeleton_graph
            .node_indices()
            .par_bridge()
            .filter(|n| !insider.contains(n))
            .collect::<Vec<_>>();
        top_sorted_outsiders.par_sort_by(|a, b| level[a.index()].cmp(&level[b.index()]));
        top_sorted_outsiders
    };

    log::trace!(
        "@@@ No. of predecessors: {}@@@",
        top_sorted_predecessors.len()
    );
    log::trace!("@@@ No. of successors: {}@@@", top_sorted_successors.len());

    #[cfg(feature = "trace")]
    {
        log::trace!(
            "C^in gate ids: {:?}",
            cin_gates.iter().map(|g| g.id()).collect_vec()
        );

        log::trace!(
            "Top sorted predecessors: {:?}",
            node_indices_to_gate_ids(top_sorted_predecessors.iter(), skeleton_graph)
        );
        log::trace!(
            "Top sorted successors: {:?}",
            node_indices_to_gate_ids(top_sorted_successors.iter(), skeleton_graph)
        );
        log::trace!(
            "Top sorted outsiders: {:?}",
            node_indices_to_gate_ids(top_sorted_outsiders.iter(), skeleton_graph)
        );
    }

    let mut new_edges = HashSet::new();
    let mut remove_edges = HashSet::new();

    // Successors
    timed!("Process successors", {
        // create blank entries in direct incoming connections for C^in nodes
        cin_gates.iter().for_each(|g| {
            direct_incoming_connections.insert(g.id(), HashSet::new());
        });

        for i in 0..cin_gates.len() {
            let mut direct_collisions = HashSet::new();

            let gate_i = &cin_gates[i];
            for j in i + 1..cin_gates.len() {
                let gate_j = &cin_gates[j];
                if gate_i.check_collision(gate_j) {
                    direct_collisions.insert(gate_j.id());
                }
            }

            for succ in top_sorted_successors.iter() {
                let succ_gate = gate_map
                    .get(skeleton_graph.node_weight(*succ).unwrap())
                    .unwrap();

                if gate_i.check_collision(succ_gate) {
                    direct_collisions.insert(succ_gate.id());
                }
            }

            // Make all outsiders succerss
            for out_succ in top_sorted_outsiders.iter() {
                let out_succ = gate_map
                    .get(skeleton_graph.node_weight(*out_succ).unwrap())
                    .unwrap();

                if gate_i.check_collision(out_succ) {
                    direct_collisions.insert(out_succ.id());
                }
            }

            // update direct incoming connections for each node in direct_collisions
            for n in direct_collisions.iter() {
                direct_incoming_connections
                    .get_mut(n)
                    .unwrap()
                    .insert(gate_i.id());
            }

            direct_connections.insert(gate_i.id(), direct_collisions);
        }

        for i in 0..cin_gates.len() {
            let direct_collisions = direct_connections.get(&cin_gates[i].id()).unwrap();
            let mut transitive_collisions = direct_collisions.clone();

            for g_id in direct_collisions.iter() {
                let dc_other_gate = direct_connections.get(g_id).unwrap();
                transitive_collisions.retain(|n| !dc_other_gate.contains(n));
            }

            for gate_id in transitive_collisions {
                new_edges.insert((cin_gates[i].id(), gate_id));
            }
        }
    });

    // Predecessors
    // timed!("Process predecessors", {
    // Handle direction connections from predecessors to gates in C^in

    // let mut transitive_connections_to_remove = HashSet::new();
    // let mut transitive_connections_to_add = vec![HashSet::new(); cin_gates.len()];
    let mut chunk_size = top_sorted_predecessors.len()
        / (current_num_threads() as f64 / ell_in as f64).ceil() as usize;
    if chunk_size == 0 {
        chunk_size += 1;
    }

    // println!("Chunk size={chunk_size}; threads={}; total_preds={}", current_num_threads(), top_sorted_predecessors.len());
    // println!("Starting pred processing");

    {
        let (mut tc_to_add, tc_to_remove, direct_outgoing_to_add, direct_incoming_to_add) = timed!(
            "[Process predecessors] Process C^in gates in parallel",
            cin_gates
                .par_iter()
                .enumerate()
                .map(|(i, gate_i)| {
                    // It is possible to chunk topologically sorted predecessors into multiple chunks (ideally `top_sorted_predecessors.len() / (current_num_threads() / 4)`)
                    // and process each chunk separately. After which remove transtive edge from predecessor A to the gate if there exist an edge from a direct connection of A
                    // in any of the succeding chunks.
                    // We're deprioritising this for the moment.

                    let (tc_remove, tc_add_chunk_map, direct_outgoing_to_insert,direct_incoming_to_insert)=   top_sorted_predecessors
                        .par_chunks(chunk_size)
                        .enumerate()
                        .map(|(chunk_index, top_preds_chunk)| {
                            // direct outgoing connections to gate_i
                            let mut direct_outgoing_to_insert_chunk = HashSet::new();
                            // direct incoming connections to gate_i
                            let mut direct_incoming_to_insert_chunk = HashSet::new();

                            let mut tc_add_chunk = HashSet::new();
                            let mut tc_remove_chunk = HashSet::new();

                            let mut gate_i_pred_collisions_chunk = HashSet::new();

                            for pred in top_preds_chunk.iter().rev() {
                                let pred_gate = gate_map
                                    .get(skeleton_graph.node_weight(*pred).unwrap())
                                    .unwrap();

                                if pred_gate.check_collision(gate_i) {
                                    let gate_i_dc = direct_connections.get(&gate_i.id()).unwrap();
                                    let pred_direct_collisions =
                                        direct_connections.get(&pred_gate.id()).unwrap();

                                    // Remove all transitive edges to nodes that gate_i has direct connections with.
                                    for gate_id in pred_direct_collisions.intersection(gate_i_dc) {
                                        if active_edges_with_gateids
                                            .contains(&(pred_gate.id(), *gate_id))
                                        {
                                            tc_remove_chunk.insert((pred_gate.id(), *gate_id));
                                        }
                                    }

                                    // only add transitive edge from pred to gate i if there's no gate beetwen pred and gate i which collides with both.
                                    if pred_direct_collisions
                                        .is_disjoint(&gate_i_pred_collisions_chunk)
                                    {
                                        tc_add_chunk.insert(pred_gate.id());
                                    }

                                    direct_outgoing_to_insert_chunk
                                        .insert(pred_gate.id());
                                    direct_incoming_to_insert_chunk
                                        .insert(pred_gate.id());

                                    gate_i_pred_collisions_chunk.insert(pred_gate.id());
                                }
                            }

                            let mut tc_add_chunk_map = HashMap::new();
                            tc_add_chunk_map.insert(chunk_index, tc_add_chunk);

                            return (
                                tc_remove_chunk,
                                tc_add_chunk_map,
                                direct_outgoing_to_insert_chunk,
                                direct_incoming_to_insert_chunk,
                            );
                        })
                        .reduce(
                            || {
                                (
                                    HashSet::new(),
                                    HashMap::new(),
                                    HashSet::new(),
                                    HashSet::new(),
                                )
                            },
                            |(mut tc_remove0,mut  tc_add0,mut  direct_outgoing0,mut  direct_incoming0), (tc_remove1, tc_add1, direct_outgoing1, direct_incoming1)| {
                                tc_remove0.extend(tc_remove1);
                                tc_add0.extend(tc_add1);
                                direct_outgoing0.extend(direct_outgoing1);
                                direct_incoming0.extend(direct_incoming1);

                                (tc_remove0, tc_add0, direct_outgoing0, direct_incoming0)
                            },
                        );


                    let mut tc_add = HashSet::new();
                    match tc_add_chunk_map.keys().max() { 
                        Some(chunk_max_index ) => {
                            for i in 0..=*chunk_max_index {
                        let chunk_i_adds = tc_add_chunk_map.get(&i).unwrap();

                        for pred in chunk_i_adds.iter() {
                            let mut should_remove_pred = false;
                            let pred_dc = direct_connections.get(pred).unwrap();
                            for j in i+1..=*chunk_max_index {
                                let chunk_j_adds = tc_add_chunk_map.get(&j).unwrap();
                                if !pred_dc.is_disjoint(chunk_j_adds) {
                                    should_remove_pred = true;
                                }
                            }

                            if !should_remove_pred {
                                tc_add.insert(*pred);
                            }
                        }
                    }
                        },
                        None => {}
                    }
                    
                    let mut tc_add_out = HashMap::new();
                    tc_add_out.insert(i, tc_add);

                    let mut direct_outgoing_to_insert_out = HashMap::new();
                    for node in direct_outgoing_to_insert {
                        let mut set = HashSet::new();
                        set.insert(gate_i.id());
                        direct_outgoing_to_insert_out.insert(node, set);
                    }
                    let mut direct_incoming_to_insert_out = HashMap::new();
                    direct_incoming_to_insert_out.insert(gate_i.id(),direct_incoming_to_insert);


                    (
                        tc_add_out,
                        tc_remove,
                        direct_outgoing_to_insert_out,
                        direct_incoming_to_insert_out,
                    )
                })
                .reduce(
                    || {
                        (
                            HashMap::new(),
                            HashSet::new(),
                            HashMap::new(),
                            HashMap::new(),
                        )
                    },
                    |(
                        mut tc_add_out0,
                        mut tc_remove0,
                        mut direct_outgoing_to_insert0,
                        mut direct_incoming_to_insert0,
                    ),
                     (
                        tc_add_out1,
                        tc_remove1,
                        direct_outgoing_to_insert1,
                        direct_incoming_to_insert1,
                    )| {
                        // tc_add_out0.extend(tc_add_out1);
                        tc_remove0.extend(tc_remove1);
                        // direct_outgoing_to_insert0.extend(direct_outgoing_to_insert1);
                        // direct_incoming_to_insert0.extend(direct_incoming_to_insert1);

                        for (k, v) in tc_add_out1 {
                            assert!(tc_add_out0.insert(k, v).is_none());
                        }

                        for (k, v) in direct_outgoing_to_insert1 {
                            direct_outgoing_to_insert0
                                .entry(k)
                                .or_insert(HashSet::new())
                                .extend(v);
                        }

                        for (k, v) in direct_incoming_to_insert1 {
                            direct_incoming_to_insert0
                                .entry(k)
                                .or_insert(HashSet::new())
                                .extend(v);
                        }

                        (
                            tc_add_out0,
                            tc_remove0,
                            direct_outgoing_to_insert0,
                            direct_incoming_to_insert0,
                        )
                    },
                )
        );

        for i in (0..cin_gates.len()).rev() {
            let i_id = cin_gates[i].id();

            for j in 0..i {
                let j_id = cin_gates[j].id();
                let dc_j = direct_connections.get(&j_id).unwrap();

                if dc_j.contains(&i_id) {
                    let tc_to_add_i = tc_to_add.get(&i).unwrap();
                    let tc_to_add_j = tc_to_add.get(&j).unwrap();

                    let mut to_remove = HashSet::new();
                    for node in tc_to_add_i.intersection(tc_to_add_j) {
                        to_remove.insert(*node);
                    }

                    tc_to_add
                        .get_mut(&i)
                        .unwrap()
                        .retain(|id| !to_remove.contains(id));
                }
            }
        }

        remove_edges = tc_to_remove;

        for (i, incoming_conn_cin_gate_i) in tc_to_add.iter() {
            for id in incoming_conn_cin_gate_i {
                new_edges.insert((*id, cin_gates[*i].id()));
            }
        }

        timed!(
            "[Process predecessors] Extend outgoing and incoming direct conns",
            {
                // Extend direct outgoing connections and direct incoming connections
                for (k, v) in direct_outgoing_to_add {
                    direct_connections.get_mut(&k).unwrap().extend(v);
                }
                for (k, v) in direct_incoming_to_add {
                    direct_incoming_connections.get_mut(&k).unwrap().extend(v);
                }
            }
        );
    }

    // println!("Done pred processing");

    // });

    let cout_ids = cout_convex_subset
        .iter()
        .map(|node| *skeleton_graph.node_weight(*node).unwrap())
        .collect_vec();

    let mut union_dir_conns = HashSet::new();
    let mut union_dir_inc_conns = HashSet::new();
    cout_ids.iter().for_each(|id| {
        let mut conns = direct_connections.get(id).unwrap().clone();
        conns.retain(|v| !cout_ids.contains(v));
        union_dir_conns.extend(conns);

        let mut inc_conns = direct_incoming_connections.get(id).unwrap().clone();
        inc_conns.retain(|v| !cout_ids.contains(v));
        union_dir_inc_conns.extend(inc_conns);
    });

    // ### Update the graph ###

    #[cfg(feature = "trace")]
    {
        for g in cin_gates.iter() {
            let id = g.id();
            log::trace!(
                "Direction connections of C^in gate {id}: {:?}",
                direct_connections.get(&id).unwrap()
            );
        }
        log::trace!("New edges 0: {}", edges_to_string(&new_edges,));
        log::trace!("Remove edges: {}", edges_to_string(&remove_edges,));
    }

    timed!(
        "Delete C^out's auxilary data", // delete C^out
        for (gate_id) in cout_ids.iter() {
            direct_connections.remove(gate_id).unwrap();
            direct_incoming_connections.remove(gate_id).unwrap();
            gate_map.remove(gate_id).unwrap();
            gate_id_to_node_index_map.remove(gate_id).unwrap();

            direct_connections.par_iter_mut().for_each(|(_, set)| {
                set.remove(gate_id);
            });
            direct_incoming_connections
                .par_iter_mut()
                .for_each(|(_, set)| {
                    set.remove(gate_id);
                });
        }
    );

    {
        timed!(
            "Repairing missing conns from direct preds to direct succs",
            {
                let missing_new_edges = union_dir_inc_conns
                    .par_iter()
                    .map(|pred| {
                        let mut edges = HashSet::new();
                        let pred_dcs = direct_connections.get(pred).unwrap();
                        for succ in union_dir_conns.iter() {
                            if pred_dcs.contains(succ) {
                                // check that intersection of DCs of pred and DICs of succ > 0. If not create an edge from pred to succ
                                let succ_dics = direct_incoming_connections.get(succ).unwrap();
                                if pred_dcs.is_disjoint(succ_dics) {
                                    edges.insert((*pred, *succ));
                                }
                            }
                        }
                        edges
                    })
                    .reduce(HashSet::new, |mut acc, item| {
                        acc.extend(item);
                        acc
                    });

                #[cfg(feature = "trace")]
                {
                    let missing_new_edges_old = {
                        let mut new_edges_old = HashSet::new();
                        for pred in &union_dir_inc_conns {
                            let pred_dcs = direct_connections.get_mut(pred).unwrap();
                            for succ in union_dir_conns.iter() {
                                if pred_dcs.contains(succ) {
                                    // check that intersection of DCs of pred and DICs of succ > 0. If not create an edge from pred to succ
                                    let succ_dics = direct_incoming_connections.get(succ).unwrap();
                                    if (pred_dcs.intersection(succ_dics)).count() == 0 {
                                        new_edges_old.insert((*pred, *succ));
                                    }
                                }
                            }
                        }
                        new_edges_old
                    };

                    assert_eq!(&missing_new_edges_old, &missing_new_edges);
                }

                new_edges.extend(missing_new_edges);

                // #[cfg(feature = "trace")]
                // log::trace!(
                //     "New edges 1: {}",
                //     edges_to_string(&new_edges, &skeleton_graph)
                // );
                // for edge in &new_edges {
                //     skeleton_graph.add_edge(edge.0, edge.1, Default::default());
                // }
            }
        )
    }

    // make sure remove edge set and new edge set are disjoint
    //
    // This is because removal and addition in the graph is more expensive.
    remove_edges.retain(|node|!new_edges.contains(node));


    // Remove "removed edges" from active edges set
    timed!(
        "Remove removed edges from active edge set",
        remove_edges.iter().for_each(|edge| {
            assert!(active_edges_with_gateids.remove(edge));
        })
    );


    // Remove from `new_edges` the edges that are in `active_edges` set
    new_edges.retain(|node|!active_edges_with_gateids.contains(node));

    // Add new edges to active edges set
    timed!(
        "Add new edges to active edge set",
        for edge in new_edges.iter() {
            active_edges_with_gateids.insert(*edge);
        }
    );

    // Remove edges
    timed!(
        "Find indices and remove 'to be removed' edges in the graph",
        {
            remove_edges
            .iter()
            .for_each(|edge|{
                let source_index = *gate_id_to_node_index_map.get(&edge.0).unwrap();
                let target_index = *gate_id_to_node_index_map.get(&edge.1).unwrap();
                 match skeleton_graph.find_edge(source_index, target_index) {
                Some(e) => {
                    // let source_id = *skeleton_graph.node_weight(edge.0).unwrap();
                    // let target_id = *skeleton_graph.node_weight(edge.1).unwrap();
                    // log::trace!("Removing ({source_id}, {target_id})");
                    // assert!(active_edges_with_gateids.contains(&(source_id, target_id)));
                    skeleton_graph.remove_edge(e).unwrap();

                },
                None => {
                    let source_id = edge.0;
                    let target_id = edge.1;
                    assert!(active_edges_with_gateids.contains(&(source_id, target_id)));
                    assert!(false, "active_edges_with_gateids contains the edge {:?} but it does not exists in the skeleton graph" , (source_id, target_id));
                }
            }
            })
        }
    );

    // Add new edges
    timed!(
        "Add new edges to graph",
        for edge in &new_edges {
            let source_index = *gate_id_to_node_index_map.get(&edge.0).unwrap();
            let target_index = *gate_id_to_node_index_map.get(&edge.1).unwrap();

            // assert!(skeleton_graph.find_edge(source_index,target_index).is_none());

            skeleton_graph.add_edge(source_index, target_index, Default::default());
        }
    );

    timed!(
        "Delete C^out",
        // Delete C^out
        // Index of removed node is take over by the node that has the last index. Here we remove \ell^out nodes.
        // As long as \ell^out <= \ell^in (notice that C^in gates are added before removing gates of C^out) none of
        // pre-existing nodes we replace the removed node and hence we wouldn't incorrectly delete some node.

        // for node in cout_convex_subset.iter() {
        //     skeleton_graph.remove_node(*node).unwrap();
        // }
        for node in cout_convex_subset.iter() {
            assert!(removed_nodes.insert(*node));
        }
    );

    // log::info!("All removed nodes: {:?}", removed_nodes);
    // log::info!("@@@ C^out nodes: {:?} @@@", &cout_convex_subset);
    // log::info!("@@@ C^in nodes: {:?} @@@", &cin_nodes);
    // log::info!("@@@ C^out imm preds: {:?} @@@", &c_out_imm_predecessors);
    // log::info!("@@@ C^out imm succs: {:?} @@@", &c_out_imm_successors);
    // log::info!(
    //     "@@@ New edges nodes: {:?} @@@",
    //     &new_edges.iter().flat_map(|e| [e.0, e.1]).collect_vec()
    // );
    // log::info!(
    //     "@@@ Removed edges nodes: {:?} @@@",
    //     &real_removed_edge_targets
    // );

    timed!(
        "Update graph neighbours",
        update_graph_neighbors(
            skeleton_graph,
            graph_neighbours,
            &cout_convex_subset,
            chain![
                // cout_convex_subset.iter().copied(),
                cin_nodes.iter().copied(),
                c_out_imm_predecessors.iter().copied(),
                c_out_imm_successors.iter().copied(),
                new_edges.iter().flat_map(|e| {
                    [
                        *gate_id_to_node_index_map.get(&e.0).unwrap(),
                        *gate_id_to_node_index_map.get(&e.1).unwrap(),
                    ]
                }),
                remove_edges.iter().flat_map(|e| {
                    [
                        *gate_id_to_node_index_map.get(&e.0).unwrap(),
                        *gate_id_to_node_index_map.get(&e.1).unwrap(),
                    ]
                })
            ]
            .collect(),
            removed_nodes
        )
    );

    // Checks whether graph neighbour updates are correct
    //
    // let iii = izip!(
    //     0..,
    //     graph_neighbours,
    //     &crate::graph_neighbors(skeleton_graph, removed_nodes)
    // )
    // .filter_map(|(idx, a, b)| (a != b).then_some(idx))
    // .collect_vec();
    // if !iii.is_empty() {
    //     println!("diff: {iii:?}");
    //     println!(
    //         "cout_convex_subset: {:?}",
    //         cout_convex_subset.iter().copied().collect_vec()
    //     );
    //     println!(
    //         "cin_nodes: {:?}",
    //         cin_nodes
    //             .iter()
    //             .take(ell_in - ell_out)
    //             .copied()
    //             .collect_vec()
    //     );
    //     println!("c_out_imm_successors: {:?}", c_out_imm_successors);
    //     println!(
    //         "new_edges targets: {:?}",
    //         new_edges
    //             .iter()
    //             .map(|e| e.1)
    //             .filter(|target| target.index() < skeleton_graph.node_count())
    //             .collect_vec()
    //     );
    //     println!(
    //         "real_removed_edge_targets: {:?}",
    //         real_removed_edge_targets.iter().copied(),
    //     );
    //     panic!("");
    // }

    // Checks whether active edge list updates are correct
    // {
    //     let mut expected_active_edges = HashSet::new();
    //     for edge in skeleton_graph.edge_references() {
    //         let source_id = *skeleton_graph.node_weight(edge.source()).unwrap();
    //         let target_id = *skeleton_graph.node_weight(edge.target()).unwrap();
    //         expected_active_edges.insert((source_id, target_id));
    //     }

    //     let diff = expected_active_edges
    //         .difference(active_edges_with_gateids)
    //         .collect_vec();

    //     if diff.len() != 0 {
    //         log::trace!("@@ Active edge set did not update correctly @@");
    //         for d in diff {
    //             if expected_active_edges.contains(d) {
    //                 log::trace!("   Active edge set does not contains expected edge {:?}", d);
    //             } else {
    //                 log::trace!("   Active edge set contains not-expected edge {:?}", d);
    //             }
    //         }
    //         panic!();
    //     }
    // }

    // update gate_id to node_index map
    // timed!(
    //     "Update gate_id_to_node_index_map",
    //     for node in skeleton_graph.node_indices() {
    //         if !removed_nodes.contains(&node) {
    //             assert!(
    //                 *gate_id_to_node_index_map
    //                     .get(skeleton_graph.node_weight(node).unwrap())
    //                     .unwrap()
    //                     == node
    //             );
    //         }
    //     }
    // );

    return true;
}

pub fn run_local_mixing<R: Send + Sync + SeedableRng + RngCore>(
    tag: &str,
    original_circuit: Option<&Circuit<BaseGate<2, u8>>>,
    skeleton_graph: &mut Graph<usize, usize>,
    direct_connections: &mut HashMap<usize, HashSet<usize>>,
    direct_incoming_connections: &mut HashMap<usize, HashSet<usize>>,
    gate_map: &mut HashMap<usize, BaseGate<2, u8>>,
    gate_id_to_node_index_map: &mut HashMap<usize, NodeIndex>,
    graph_neighbors: &mut Vec<[HashSet<NodeIndex>; 2]>,
    removed_nodes: &mut HashSet<NodeIndex>,
    active_edges_with_gateids: &mut HashSet<(usize, usize)>,
    latest_id: &mut usize,
    n: u8,
    rng: &mut R,
    ell_out: usize,
    ell_in: usize,
    max_convex_iterations: usize,
    max_replacement_iterations: usize,
    to_checkpoint: bool,
    probabilitic_eq_check_iterations: usize,
    mut cb: impl FnMut(Circuit<BaseGate<2, u8>>),
    debug: bool,
) -> bool {
    if debug {
        assert!(original_circuit.is_some());
    }

    log::info!("############################## [run_local_mixing START] {tag} ##############################");

    let now = std::time::Instant::now();
    let success = local_mixing_step::<_>(
        skeleton_graph,
        ell_in,
        ell_out,
        n,
        direct_connections,
        direct_incoming_connections,
        gate_map,
        gate_id_to_node_index_map,
        graph_neighbors,
        removed_nodes,
        active_edges_with_gateids,
        latest_id,
        max_replacement_iterations,
        max_convex_iterations,
        rng,
    );
    let elapsed = now.elapsed();

    log::info!("local mixing step returned {success} in {:?}", elapsed);

    if success {
        if debug || to_checkpoint {
            let original_circuit = original_circuit.unwrap();

            let top_sorted_nodes = timed!("Topological sort after local mixing", {
                toposort_with_cached_graph_neighbours(
                    skeleton_graph,
                    graph_neighbors,
                    removed_nodes,
                )
            });

            #[cfg(feature = "trace")]
            log::trace!(
                "Top sort after local mixing: {:?}",
                // node_indices_to_gate_ids(top_sorted_nodes.iter(), &skeleton_graph)
                &top_sorted_nodes
            );

            let mixed_circuit = Circuit::from_top_sorted_nodes(
                &top_sorted_nodes,
                &skeleton_graph,
                &gate_map,
                original_circuit.n(),
            );

            let (is_correct, diff_indices) = check_probabilisitic_equivalence(
                &original_circuit,
                &mixed_circuit,
                probabilitic_eq_check_iterations,
                rng,
            );
            if !is_correct {
                log::error!(
                    "[Error] (Failed equivalence check at) {tag}. Different at indices {:?}",
                    diff_indices
                );

                match toposort(skeleton_graph.deref(), None) {
                    Ok(_) => {
                        log::error!("Top sort did not fail");
                    }
                    Err(e) => {
                        log::error!("Top sort also fails with {:?}", e);
                    }
                }
                assert!(false);
            }

            cb(mixed_circuit);
        }
    }

    log::info!("############################## [run_local_mixing FINISH] {tag} ##############################");
    success
}

pub fn check_probabilisitic_equivalence<G, R: RngCore>(
    circuit0: &Circuit<G>,
    circuit1: &Circuit<G>,
    iterations: usize,
    rng: &mut R,
) -> (bool, Vec<usize>)
where
    G: Gate<Input = [bool]>,
{
    assert_eq!(circuit0.n(), circuit1.n());
    let n = circuit0.n();

    for value in rng
        .sample_iter(Uniform::new(0, 1u128 << n))
        .take(iterations)
    {
        // for value in 0..1u128 << 16 {
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

            return (false, diff_indices);
        }

        // assert_eq!(inputs0, inputs1, "Different at indices {:?}", diff_indices);
    }

    return (true, vec![]);
}

#[cfg(test)]
mod tests {
    use petgraph::{
        algo::{all_simple_paths, connected_components, has_path_connecting, toposort},
        visit::{Dfs, Reversed, Visitable, Walker},
    };
    use rand::{thread_rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[test]
    fn test_local_mixing() {
        env_logger::init();

        let gates = 100;
        let n = 6;
        let mut rng = ChaCha8Rng::from_entropy();
        let (original_circuit, _) =
            sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);

        let (_, _, skeleton_graph, _, _, _, _, _) = prepare_circuit(&original_circuit);
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

        let (
            mut direct_connections,
            mut direct_incoming_connections,
            mut skeleton_graph,
            mut gate_id_to_node_index_map,
            mut gate_map,
            mut graph_neighbors,
            mut active_edges_with_gateids,
            mut latest_id,
        ) = prepare_circuit(&original_circuit);

        let mut removed_nodes = HashSet::new();

        let mut mixing_steps = 0;
        let total_mixing_steps = 1000;

        while mixing_steps < total_mixing_steps {
            log::info!("#### Mixing step {mixing_steps} ####");

            log::info!(
                "Topological order before local mixing iteration: {:?}",
                &node_indices_to_gate_ids(top_sorted_nodes.iter(), &skeleton_graph)
            );

            let success = local_mixing_step::<_>(
                &mut skeleton_graph,
                ell_in,
                ell_out,
                n,
                &mut direct_connections,
                &mut direct_incoming_connections,
                &mut gate_map,
                &mut gate_id_to_node_index_map,
                &mut graph_neighbors,
                &mut removed_nodes,
                &mut active_edges_with_gateids,
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

                let top_sorted_nodes = toposort_with_cached_graph_neighbours(
                    &skeleton_graph,
                    &graph_neighbors,
                    &removed_nodes,
                );

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
                let (is_correct, diff_indices) = check_probabilisitic_equivalence(
                    &original_circuit,
                    &mixed_circuit,
                    1000,
                    &mut rng,
                );
                if !is_correct {
                    println!("[Error] Different at indices {:?}", diff_indices);
                    assert!(false);
                }

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
            let (_, _, skeleton_graph, _, _, _, _, _) = prepare_circuit(&circuit);

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
                &mut HashSet::new(),
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
        let gates = 100;
        let n = 64;
        let ell_out = 4;
        let max_iterations = 10000;
        let mut rng = ChaCha8Rng::from_entropy();

        let mut iter = 0;
        while iter < 10 {
            let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
            let (_, _, skeleton_graph, _, _, _, _, _) = prepare_circuit(&circuit);
            let graph_neighbors = graph_neighbors(&skeleton_graph, &mut HashSet::new());
            let levels = graph_level(&skeleton_graph, &graph_neighbors, &HashSet::new());
            let convex_subgraph = find_convex_fast(
                &skeleton_graph,
                &levels,
                ell_out,
                max_iterations,
                &mut rng,
                &mut HashSet::new(),
            );

            match convex_subgraph {
                Some((start_node, convex_subgraph)) => {
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

    fn find_all_predecessors_of_node(
        node: NodeIndex,
        graph: &Graph<usize, usize>,
    ) -> HashSet<NodeIndex> {
        let mut all_preds = HashSet::new();
        for curr_node in graph.neighbors_directed(node, Direction::Incoming) {
            dfs(
                curr_node,
                &mut HashSet::new(),
                &mut all_preds,
                &mut vec![],
                graph,
                Direction::Incoming,
                &mut HashSet::new(),
            );
        }
        return all_preds;
    }

    #[test]
    fn test_topological_order_of_convex_subset() {
        let gates = 2000;
        let n = 64;
        // TODO: Fails for >= 2 because top sort is random
        let ell_out = 4;
        let max_iterations = 10000;
        let mut rng = ChaCha8Rng::from_entropy();

        let mut iter = 0;
        while iter < 100 {
            let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
            let (_, _, skeleton_graph, _, _, _, _, _) = prepare_circuit(&circuit);
            let graph_neighbors = graph_neighbors(&skeleton_graph, &mut HashSet::new());
            let levels = graph_level(&skeleton_graph, &graph_neighbors, &HashSet::new());

            let convex_subgraph = find_convex_fast(
                &skeleton_graph,
                &levels,
                ell_out,
                max_iterations,
                &mut rng,
                &mut HashSet::new(),
            );

            match convex_subgraph {
                Some((start_node, convex_subgraph)) => {
                    // use DFS within convex set to topologically sort nodes in convex subgraph
                    let mut convex_set_sorted = VecDeque::new();
                    dfs_within_convex_set(
                        start_node,
                        &convex_subgraph,
                        &skeleton_graph,
                        &mut HashSet::new(),
                        &mut convex_set_sorted,
                    );

                    // If node j is after node i, then j cannot be predecessor of i
                    for i in 0..convex_set_sorted.len() {
                        // find predecessors of i
                        let all_preds =
                            find_all_predecessors_of_node(convex_set_sorted[i], &skeleton_graph);
                        for j in i + 1..convex_set_sorted.len() {
                            assert!(!all_preds.contains(&convex_set_sorted[j]));
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
            let (_, _, skeleton_graph, _, _, _, _, _) = prepare_circuit(&circuit);

            let collisions_sets = circuit_to_collision_sets(&circuit);
            let is_wc = is_collisions_set_weakly_connected(&collisions_sets);
            let expected_wc = connected_components(&skeleton_graph) == 1;
            assert_eq!(
                is_wc, expected_wc,
                "Expected {expected_wc} but got {is_wc} for collisions sets {:?}",
                collisions_sets
            );
        }
    }

    struct Stats<T> {
        samples: Vec<T>,
    }

    impl<T> Stats<T>
    where
        T: for<'a> std::iter::Sum<&'a T> + TryInto<f64>,
        <T as TryInto<f64>>::Error: Debug,
    {
        fn new() -> Stats<T> {
            Self {
                samples: Default::default(),
            }
        }

        fn add_sample(&mut self, sample: T) {
            self.samples.push(sample);
        }

        fn average(&self) -> f64 {
            let s: T = self.samples.iter().sum();
            let s: f64 = s.try_into().unwrap();
            s / self.samples.len() as f64
        }
    }

    #[test]
    fn time_convex_subcircuit() {
        env_logger::init();
        let gates = 53000;
        let n = 128;
        let ell_out = 2;
        let max_iterations = 10000;
        let mut rng = ChaCha8Rng::from_entropy();
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let (_, _, skeleton_graph, _, _, _, _, _) = prepare_circuit(&circuit);
        let graph_neighbors = graph_neighbors(&skeleton_graph, &mut HashSet::new());
        let levels = graph_level(&skeleton_graph, &graph_neighbors, &HashSet::new());

        let mut stats = Stats::new();

        for _ in 0..10 {
            let now = std::time::Instant::now();
            let _ = find_convex_fast(
                &skeleton_graph,
                &levels,
                ell_out,
                max_iterations,
                &mut rng,
                &mut HashSet::new(),
            )
            .unwrap();
            stats.add_sample(now.elapsed().as_secs_f64());
        }

        println!("Average find convex runtime: {}", stats.average());
    }

    #[test]
    fn time_blah() {
        env_logger::init();
        let gates = 50000;
        let n = 64;
        let ell_out = 4;
        let mut rng = thread_rng();
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let (_, _, skeleton_graph, _, _, _, _, _) = prepare_circuit(&circuit);
        let level = graph_level(
            &skeleton_graph,
            &graph_neighbors(&skeleton_graph, &mut HashSet::new()),
            &HashSet::new(),
        );

        let mut stats = Stats::new();

        for _ in 0..10000 {
            let start_node = NodeIndex::from(rng.gen_range(0..skeleton_graph.node_count()) as u32);
            let mut convex_set = HashSet::new();
            convex_set.insert(start_node);
            let now = std::time::Instant::now();
            // let _ = trialll(&skeleton_graph, ell_out, max_iterations, &mut rng).unwrap();
            let _ = blah(
                ell_out,
                &mut convex_set,
                &skeleton_graph,
                &level,
                &mut HashSet::new(),
            );
            stats.add_sample(now.elapsed().as_secs_f64());
        }

        println!("Average blah runtime: {}", stats.average());
    }

    #[test]
    fn time_graph_level() {
        let gates = 50000;
        let n = 128;

        let mut rng = rand_chacha::ChaCha8Rng::from_entropy();

        let (original_circuit, _) =
            sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let (_, _, graph, _, _, _, _, _) = prepare_circuit(&original_circuit);
        let graph_neighbors = graph_neighbors(&graph, &mut HashSet::new());

        let n = 10;
        let start = std::time::Instant::now();
        for _ in 0..n {
            graph_level(&graph, &graph_neighbors, &HashSet::new());
        }
        dbg!(start.elapsed() / n);
    }

    #[test]
    fn time_dfs_fast() {
        let gates = 50000;
        let n = 128;

        let mut rng = rand_chacha::ChaCha8Rng::from_entropy();

        let (original_circuit, _) =
            sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let (_, _, graph, _, _, _, _, _) = prepare_circuit(&original_circuit);

        let n = 30;
        let mut t = Duration::default();
        for _ in 0..n {
            let source = NodeIndex::from(rng.gen_range(0..gates as _));
            let start = std::time::Instant::now();
            dfs_fast(
                &graph,
                vec![source],
                Direction::Incoming,
                &mut HashSet::new(),
            );
            t += start.elapsed();
        }
        println!("Find predecessors: {:?}", t / n);

        let mut t = Duration::default();
        for _ in 0..n {
            let source = NodeIndex::from(rng.gen_range(0..gates as _));
            let start = std::time::Instant::now();
            dfs_fast(
                &graph,
                vec![source],
                Direction::Outgoing,
                &mut HashSet::new(),
            );
            t += start.elapsed();
        }
        println!("Find successors: {:?}", t / n);

        for _ in 0..10 {
            let start = NodeIndex::from(rng.gen_range(0..gates as _));
            assert_eq!(
                dfs_fast(
                    &graph,
                    vec![start],
                    Direction::Outgoing,
                    &mut HashSet::new()
                ),
                Dfs::from_parts(vec![start], graph.visit_map())
                    .iter(&graph)
                    .collect()
            );
            assert_eq!(
                dfs_fast(
                    &graph,
                    vec![start],
                    Direction::Incoming,
                    &mut HashSet::new()
                ),
                Dfs::from_parts(vec![start], graph.visit_map())
                    .iter(Reversed(&graph))
                    .collect()
            )
        }
    }

    // #[test]
    // fn perm_trial() {
    //     let gate_count = 300;
    //     let n = 16u8;
    //     // let (circuit, _) =
    //     // sample_circuit_with_base_gate::<2, _, _>(gate_count, n, 1.0, &mut thread_rng());
    //     let mut circuit =
    //         Circuit::new(vec![BaseGate::new(0, 0, [0, 0], 0); gate_count], n as usize);
    //     sample_circuit_with_base_gate_fast(&mut circuit, n, &mut thread_rng());

    //     let bitstring = input_value_to_bitstring_map(n as usize);
    //     let mapp = permutation_map(&circuit, &bitstring);

    //     for i in 0..100 {
    //         let mapp2 = permutation_map(&circuit, &bitstring);

    //         assert_eq!(&mapp, &mapp2);
    //     }
    // }
}
