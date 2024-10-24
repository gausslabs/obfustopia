use std::{collections::HashMap, fmt::Display};

use itertools::Itertools;
use petgraph::{graph::NodeIndex, Graph};

pub trait Gate {
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
pub struct BaseGate<const N: usize, D> {
    id: usize,
    target: D,
    controls: [D; N],
    control_func: fn(&[D; N], &[bool]) -> bool,
}

impl<const N: usize, D> BaseGate<N, D> {
    pub(crate) fn new(
        id: usize,
        target: D,
        controls: [D; N],
        control_func: fn(&[D; N], &[bool]) -> bool,
    ) -> Self {
        Self {
            id,
            target,
            controls,
            control_func,
        }
    }

    pub(crate) fn control_func(&self) -> &fn(&[D; N], &[bool]) -> bool {
        &self.control_func
    }
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

pub struct Circuit<G> {
    gates: Vec<G>,
    n: usize,
}

impl<G> Circuit<G>
where
    G: Gate<Input = [bool]>,
{
    pub fn run(&self, inputs: &mut [bool]) {
        self.gates.iter().for_each(|g| {
            g.run(inputs);
        });
    }
}

impl<G> Circuit<G>
where
    G: Clone,
{
    pub fn split_circuit(&self, at_gate: usize) -> (Circuit<G>, Circuit<G>) {
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

    pub fn from_top_sorted_nodes(
        top_sorted_nodes: &[NodeIndex],
        skeleton_graph: &Graph<usize, usize>,
        gate_map: &HashMap<usize, G>,
        n: usize,
    ) -> Self {
        Circuit::new(
            top_sorted_nodes
                .iter()
                .map(|node| {
                    gate_map
                        .get(skeleton_graph.node_weight(*node).unwrap())
                        .unwrap()
                        .to_owned()
                })
                .collect_vec(),
            n,
        )
    }
}

impl<G> Circuit<G> {
    pub fn new(gates: Vec<G>, n: usize) -> Self {
        Circuit { gates, n }
    }

    pub fn n(&self) -> usize {
        self.n
    }

    pub fn gates(&self) -> &[G] {
        self.gates.as_ref()
    }
}

impl<const N: usize, D> Display for Circuit<BaseGate<N, D>>
where
    D: Into<usize> + Copy + PartialEq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f)?;
        writeln!(f, "{:-<15}", "")?;
        for i in 0..self.n {
            write!(f, "{:2}", i)?;
        }
        writeln!(f)?;

        writeln!(f, "{:-<15}", "")?;

        // Print 20 rows of values from 0 to 10
        for g in self.gates.iter() {
            write!(f, "{:1}", "")?;
            for j in 0..self.n {
                let controls = g
                    .controls()
                    .iter()
                    .map(|v| (*v).into())
                    .collect::<Vec<usize>>();
                if g.target().into() == j {
                    write!(f, "{:2}", "O")?;
                } else if controls.contains(&j) {
                    write!(f, "{:2}", "I")?;
                } else {
                    write!(f, "{:2}", "x")?;
                }
            }
            writeln!(f)?;
        }

        writeln!(f, "{:-<15}", "")?;
        writeln!(f)?;
        Ok(())
    }
}
