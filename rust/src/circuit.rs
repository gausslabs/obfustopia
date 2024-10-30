use std::{collections::HashMap, fmt::Display};

use bitvec::{array::BitArray, vec::BitVec};
use itertools::Itertools;
use petgraph::{graph::NodeIndex, Graph};
use serde::{Deserialize, Serialize};

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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(
    serialize = "D: Serialize, [D; N]: Serialize",
    deserialize = "D: Deserialize<'de>, [D; N]: Deserialize<'de>"
))]
pub struct BaseGate<const N: usize, D> {
    id: usize,
    target: D,
    controls: [D; N],
    control_func: u8,
}

impl<const N: usize, D> BaseGate<N, D> {
    pub const N_CONTROL_FUNC: u8 = {
        match N {
            2 => 16,
            _ => unimplemented!(),
        }
    };

    pub(crate) fn new(id: usize, target: D, controls: [D; N], control_func: u8) -> Self {
        debug_assert!(control_func < Self::N_CONTROL_FUNC);
        Self {
            id,
            target,
            controls,
            control_func,
        }
    }

    #[inline(always)]
    pub fn id(&self) -> usize {
        self.id
    }

    #[inline(always)]
    pub fn target(&self) -> D
    where
        D: Copy,
    {
        self.target
    }

    #[inline(always)]
    pub fn controls(&self) -> [D; N]
    where
        D: Copy,
    {
        self.controls
    }

    pub(crate) fn control_func(&self) -> u8 {
        self.control_func
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
        match N {
            2 => {
                // Refer to https://i.sstatic.net/tS0my.png for all possible 2-bit input boolean functions
                const TABLE: [bool; 64] = {
                    let mut t = [false; 64];
                    let mut i = 0;
                    while i < 64 {
                        let control_func = i >> 2;
                        let a = (i >> 1) & 1 == 1;
                        let b = i & 1 == 1;
                        t[i] = match control_func {
                            0 => false,
                            1 => a & b,
                            2 => a & (!b),
                            3 => a,
                            4 => (!a) & b,
                            5 => b,
                            6 => a ^ b,
                            7 => a | b,
                            8 => !(a | b),
                            9 => (a & b) | ((!a) & (!b)),
                            10 => !a,
                            11 => !b,
                            12 => (!a) | b,
                            13 => (!b) | a,
                            14 => !(a & b),
                            15 => true,
                            _ => unreachable!(),
                        };
                        i += 1
                    }
                    t
                };
                let idx = ((self.control_func as usize) << 2)
                    ^ ((input[self.controls[0].into()] as usize) << 1)
                    ^ (input[self.controls[1].into()] as usize);
                input[self.target.into()] ^= TABLE[idx];
            }
            _ => unimplemented!(),
        }
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

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
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

    pub fn gates_mut(&mut self) -> &mut [G] {
        self.gates.as_mut()
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
