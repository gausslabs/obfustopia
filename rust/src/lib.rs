use itertools::Itertools;
use petgraph::{
    graph::{self, NodeIndex},
    visit::{IntoNeighborsDirected, NodeRef},
    Direction::Outgoing,
    Graph,
};
use rand::{distributions::Uniform, thread_rng, Rng, RngCore};
use sha2::{Digest, Sha256};
use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
};

trait Gate {
    type Input: ?Sized;
    type Target;
    type Controls;

    fn run(&self, input: &mut Self::Input);
    fn target(&self) -> Self::Target;
    fn controls(&self) -> &Self::Controls;
    fn check_collision(&self, other: &Self) -> bool;
    fn id(&self) -> usize;
}

#[derive(Clone)]
struct BaseGate<const N: usize, D> {
    id: usize,
    target: D,
    controls: [D; N],
    control_func: fn(&[D; N], &[bool]) -> bool,
}

impl<const N: usize, D> Gate for BaseGate<N, D>
where
    D: Into<usize> + Copy + PartialEq,
{
    type Input = [bool];
    type Controls = [D; N];
    type Target = D;

    fn run(&self, input: &mut Self::Input) {
        // control bit XOR target
        input[self.target.into()] =
            input[self.target.into()] ^ (self.control_func)(&self.controls, input);
    }

    fn controls(&self) -> &Self::Controls {
        &self.controls
    }

    fn target(&self) -> Self::Target {
        self.target
    }

    fn check_collision(&self, other: &Self) -> bool {
        other.controls().contains(&self.target()) || self.controls().contains(&other.target())
    }

    fn id(&self) -> usize {
        self.id
    }
}

struct Circuit<G> {
    gates: Vec<G>,
    n: usize,
}

impl<G> Circuit<G>
where
    G: Gate<Input = [bool]>,
{
    fn run(&self, inputs: &mut [bool]) {
        self.gates.iter().for_each(|g| {
            g.run(inputs);
        });
    }
}

impl<G> Circuit<G>
where
    G: Clone,
{
    fn split_circuit(&self, at_gate: usize) -> (Circuit<G>, Circuit<G>) {
        assert!(at_gate < self.gates.len());
        let mut first_gates = self.gates.clone();
        let second_gates = first_gates.split_off(at_gate);
        (
            Circuit {
                gates: first_gates,
                n: self.n,
            },
            Circuit {
                gates: second_gates,
                n: self.n,
            },
        )
    }
}

fn value_to_bitstring_map(n: usize) -> HashMap<usize, Vec<bool>> {
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

fn permutation_map<G>(circuit: &Circuit<G>) -> HashMap<usize, Vec<bool>>
where
    G: Gate<Input = [bool]>,
{
    let bitstring_map = value_to_bitstring_map(circuit.n);
    let mut permutation_map = HashMap::new();
    for i in 0usize..1 << circuit.n {
        let mut inputs = bitstring_map.get(&i).unwrap().clone();
        circuit.run(&mut inputs);
        // assert_ne!(bitstring_map.get(&i).unwrap(), &inputs);
        permutation_map.insert(i, inputs);
    }
    return permutation_map;
}

fn sample_circuit_with_base_gate(
    gate_count: usize,
    n: u8,
    two_prob: f64,
) -> (Circuit<BaseGate<3, u8>>, String) {
    let mut rng = thread_rng();

    let three_replacement_cost = 4; // 3-way gates can be decomposed into 4 2-way gates
    let two_replacement_cost = 1;

    let distribution = Uniform::new(0, n);
    let mut gates = Vec::with_capacity(gate_count);
    let mut curr_gate = 0;
    let mut sample_trace = Sha256::new();
    let mut id = 0;
    while curr_gate < gate_count {
        let if_true_three = rng.gen_bool(1.0 - two_prob);
        let gate = if if_true_three {
            // sample 3 way CNOTs
            let target = rng.sample(distribution);
            let mut wires = HashSet::new();
            wires.insert(target);
            while wires.len() < 4 {
                wires.insert(rng.sample(distribution));
            }
            wires.remove(&target);

            let mut controls = [0; 3];
            controls
                .iter_mut()
                .zip(wires.iter())
                .for_each(|(i, o)| *i = *o);

            curr_gate += three_replacement_cost;

            sample_trace.update(format!(
                "THREE{target}{}{}{}",
                controls[0], controls[1], controls[2]
            ));

            BaseGate::<3, u8> {
                id,
                target: target,
                controls: controls,
                control_func: (|controls, inputs| {
                    inputs[controls[0] as usize]
                        & inputs[controls[1] as usize]
                        & inputs[controls[2] as usize]
                }),
            }
        } else {
            // sample 2 way CNOTs
            let target = rng.sample(distribution);
            let mut wires = HashSet::new();
            wires.insert(target);
            while wires.len() < 3 {
                wires.insert(rng.sample(distribution));
            }
            wires.remove(&target);

            let mut controls = [n; 3];
            controls
                .iter_mut()
                .zip(wires.iter())
                .for_each(|(i, o)| *i = *o);
            assert!(controls[2] == n);

            curr_gate += two_replacement_cost;

            sample_trace.update(format!("TWO{target}{}{}", controls[0], controls[1]));

            BaseGate::<3, u8> {
                id,
                target: target,
                controls: controls,
                control_func: (|controls, inputs| {
                    inputs[controls[0] as usize] & inputs[controls[1] as usize]
                }),
            }
        };
        id += 1;
        gates.push(gate);
    }

    let sample_trace: String = format!("{:X}", sample_trace.finalize());

    (
        Circuit {
            gates,
            n: n as usize,
        },
        sample_trace,
    )
}

fn replacement_circuit<G>(circuit: &Circuit<G>, ell_in: u8) -> Option<Circuit<BaseGate<3, u8>>>
where
    G: Gate<Input = [bool]>,
{
    let bitstring_map = value_to_bitstring_map(circuit.n);
    let desired_perm_map = permutation_map(circuit);

    let max_iterations = 100000000;
    let mut curr_iter = 0;

    let mut replacement_circuit = None;

    let mut visited_circuits = HashMap::new();

    while curr_iter < max_iterations {
        let (random_circuit, circuit_trace) =
            sample_circuit_with_base_gate(ell_in as usize, circuit.n as u8, 0.6);

        if visited_circuits.contains_key(&circuit_trace) {
            let count = visited_circuits.get_mut(&circuit_trace).unwrap();
            *count += 1;
        } else {
            visited_circuits.insert(circuit_trace, 1usize);
        }

        let mut funtionally_equivalent = true;
        for i in 0..1usize << circuit.n {
            let mut inputs = bitstring_map.get(&i).unwrap().clone();
            random_circuit.run(&mut inputs);

            if &inputs != desired_perm_map.get(&i).unwrap() {
                funtionally_equivalent = false;
                break;
            }
        }
        if funtionally_equivalent {
            replacement_circuit = Some(random_circuit);
            break;
        }

        curr_iter += 1;

        // if curr_iter == max_iterations {
        //     replacement_circuit = Some(random_circuit);
        // }
    }

    let mut visited_freq = vec![0; 100];
    visited_circuits.iter().for_each(|(_k, v)| {
        visited_freq[*v] += 1;
    });

    println!("Iteration count: {}", curr_iter);
    println!("Visited frequency: {:?}", visited_freq);

    return replacement_circuit;
}

fn print_permutation_map<G>(circuit: &Circuit<G>)
where
    G: Gate<Input = [bool]>,
{
    let permutation_map = permutation_map(circuit);
    let mut output = vec![];
    for input_v in 0..1usize << circuit.n {
        let bitstring = permutation_map.get(&input_v).unwrap();
        let mut output_v = 0usize;
        for i in 0..circuit.n {
            output_v += ((bitstring[i]) as usize) << i;
        }
        output.push((input_v, output_v));
    }
    println!("{:?}", output);
}

fn print_circuit_with_base_gates<const N: usize, D>(circuit: &Circuit<BaseGate<N, D>>)
where
    D: Into<usize> + Copy + PartialEq,
{
    println!();
    println!("{:-<15}", "");
    for i in 0..circuit.n {
        print!("{:2}", i);
    }
    println!();

    println!("{:-<15}", "");

    // Print 20 rows of values from 0 to 10
    for g in circuit.gates.iter() {
        print!("{:1}", "");
        for j in 0..circuit.n {
            let controls = g
                .controls()
                .iter()
                .map(|v| (*v).into())
                .collect::<Vec<usize>>();
            if g.target().into() == j {
                print!("{:2}", "O");
            } else if controls.contains(&j) {
                print!("{:2}", "I");
            } else {
                print!("{:2}", "x");
            }
        }
        println!();
    }

    println!("{:-<15}", "");
    println!();
}

fn dfs(
    curr_node: NodeIndex,
    visited_with_path: &mut HashSet<NodeIndex>,
    visited: &mut HashSet<NodeIndex>,
    path: &mut Vec<NodeIndex>,
    graph: &Graph<usize, usize>,
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
    for v in graph.neighbors_directed(curr_node.into(), Outgoing) {
        dfs(v, visited_with_path, visited, path, graph);
    }
    path.pop();
    visited.insert(curr_node);
}

fn find_convex_subcircuit<R: RngCore>(
    graph: &Graph<usize, usize>,
    ell_out: usize,
    rng: &mut R,
) -> HashSet<NodeIndex> {
    // find a random source
    // find the unexplored candidate set
    //

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

    return convex_set;
}

fn circuit_to_skeleton_graph<G: Gate>(circuit: &Circuit<G>) -> Graph<usize, usize> {
    let mut all_collision_sets = Vec::with_capacity(circuit.gates.len());
    for (i, gi) in circuit.gates.iter().enumerate() {
        let mut collision_set_i = HashSet::new();
        for (j, gj) in (circuit.gates.iter().enumerate()).skip(i + 1) {
            if gi.check_collision(gj) {
                collision_set_i.insert(j);
            }
        }
        all_collision_sets.push(collision_set_i);
    }

    // Remove intsecting collisions. That is i can collide with j iff there is not k between i < k < j with which both i & j collide
    for (i, _) in circuit.gates.iter().enumerate() {
        for (j, gj) in circuit.gates.iter().enumerate().skip(i + 1) {
            if all_collision_sets[i].contains(&j) {
                let (first, second) = all_collision_sets.split_at_mut(j);
                let collisions_set_i = first.last_mut().unwrap();
                let collisions_set_j = &second.first().unwrap();
                // remove id k from set of i iff k is in set of j (ie j, where j < k, collides with k)
                collisions_set_i.retain(|k| !collisions_set_j.contains(k));
            }
        }
    }

    let mut skeleton = Graph::<usize, usize>::new();
    // add nodes with weights as ids
    let nodes = circuit
        .gates
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

#[cfg(test)]
mod tests {
    use petgraph::algo::all_simple_paths;

    use super::*;

    #[test]
    fn trial() {
        let gates = 50;
        let n = 10;
        let (circuit, _) = sample_circuit_with_base_gate(gates, n, 1.0);
        let mut skeleton_graph = circuit_to_skeleton_graph(&circuit);

        let mut rng = thread_rng();
        let convex_subset = find_convex_subcircuit(&skeleton_graph, 5, &mut rng);
        println!("Convex subset: {:?}", convex_subset);
    }

    #[test]
    fn test_dfs() {
        let gates = 50;
        let n = 10;
        let (circuit, _) = sample_circuit_with_base_gate(gates, n, 1.0);
        let skeleton_graph = circuit_to_skeleton_graph(&circuit);

        let mut visited_with_path = HashSet::new();
        let mut visited = HashSet::new();
        let mut path = vec![];
        let source = NodeIndex::from(2);
        let target = NodeIndex::from(8);
        visited_with_path.insert(target);
        dfs(
            source,
            &mut visited_with_path,
            &mut visited,
            &mut path,
            &skeleton_graph,
        );

        // visited path will always contain `target` even if no path exists from source to target. Here we remove it.
        if visited_with_path.len() == 1 {
            assert!(visited_with_path.remove(&target));
        }

        // println!("Visited nodes: {:?}", &visited_with_path);

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
