use petgraph::visit::{IntoNeighborsDirected, IntoNodeIdentifiers, VisitMap};
use rustc_hash::FxHashMap;
use std::{collections::VecDeque, hash::Hash};

pub struct TopoKahn<N, VM> {
    to_visit: VecDeque<N>,          // Queue for nodes with zero in-degree
    visited: VM,                    // Stores the visited nodes
    in_degree: FxHashMap<N, usize>, // In-degree of each node
}

impl<N, VM> TopoKahn<N, VM>
where
    N: Copy + Eq + Hash,
    VM: VisitMap<N> + Default,
{
    /// Initialize the traversal with the graph and calculate in-degrees
    pub fn new<G>(g: G) -> Self
    where
        G: IntoNeighborsDirected<NodeId = N> + IntoNodeIdentifiers<NodeId = N>,
    {
        let mut in_degree = FxHashMap::default();
        let mut tovisit = VecDeque::new();

        // Calculate the in-degree for each node
        for node in g.node_identifiers() {
            let mut degree = 0;
            for _ in g.neighbors_directed(node, petgraph::Direction::Incoming) {
                degree += 1;
            }
            in_degree.insert(node, degree);

            // If a node has zero in-degree, add it to the queue
            if degree == 0 {
                tovisit.push_back(node);
            }
        }

        TopoKahn {
            to_visit: tovisit,
            visited: VM::default(),
            in_degree,
        }
    }

    /// Return the next node in the topological order traversal, or `None` if done
    pub fn next<G>(&mut self, g: G) -> Option<N>
    where
        G: IntoNeighborsDirected<NodeId = N>,
    {
        // Process nodes with zero in-degree
        while let Some(nix) = self.to_visit.pop_front() {
            if self.visited.is_visited(&nix) {
                continue;
            }

            self.visited.visit(nix);

            // Decrease the in-degree of neighbors and enqueue any that reach zero in-degree
            for neigh in g.neighbors(nix) {
                if let Some(degree) = self.in_degree.get_mut(&neigh) {
                    *degree -= 1;
                    if *degree == 0 {
                        self.to_visit.push_back(neigh);
                    }
                }
            }

            return Some(nix);
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use itertools::Itertools;
    use petgraph::{algo::toposort, graph::NodeIndex};
    use rand::thread_rng;

    use crate::{circuit_to_skeleton_graph, sample_circuit_with_base_gate, tests::Stats};

    use super::TopoKahn;

    #[test]
    fn test_top_sort() {
        let gates = 50000;
        let n = 64;
        let ell_out = 4;
        let mut rng = thread_rng();
        let (circuit, _) = sample_circuit_with_base_gate::<2, u8, _>(gates, n, 1.0, &mut rng);
        let skeleton_graph = circuit_to_skeleton_graph(&circuit);
        dbg!("Started");
        let mut stats = Stats::new();

        for _ in 0..100 {
            let now = std::time::Instant::now();
            // let mut top = TopoKahn::<_, HashSet<NodeIndex>>::new(&skeleton_graph);
            // let _ = top.next(&skeleton_graph).into_iter().collect_vec();
            let _ = toposort(&skeleton_graph, None);
            stats.add_sample(now.elapsed().as_secs_f64());
        }

        println!("Average time {}", stats.average());
    }
}
