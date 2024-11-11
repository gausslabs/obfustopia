use bitvec::{array::BitArray, vec::BitVec};
use hashbrown::HashMap;
use itertools::{chain, izip, Itertools};
use petgraph::{graph::NodeIndex, Graph};
use rand::{seq::SliceRandom, RngCore};
use serde::{Deserialize, Serialize};
use std::{fmt::Display, iter::repeat_with};

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

    pub fn control_func(&self) -> u8 {
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
                        let control_func = Base2GateControlFunc::from_u8((i >> 2) as _);
                        let a = (i >> 1) & 1 == 1;
                        let b = i & 1 == 1;
                        t[i] = control_func.evaluate(a, b);
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

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
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

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Base2GateControlFunc {
    F = 0,      // false,
    AND = 1,    // a & b,
    AND_NB = 2, // a & (!b),
    A = 3,      // a,
    AND_NA = 4, // (!a) & b,
    B = 5,      // b,
    XOR = 6,    // a ^ b,
    OR = 7,     // a | b,
    NOR = 8,    // !(a | b),
    EQUIV = 9,  // (a & b) | ((!a) & (!b)),
    NB = 10,    // !b,
    OR_NB = 11, // (!b) | a,
    NA = 12,    // !a,
    OR_NA = 13, // (!a) | b,
    NAND = 14,  // !(a & b),
    T = 15,     // true,
}

impl Base2GateControlFunc {
    const fn from_u8(v: u8) -> Self {
        match v {
            0 => Self::F,
            1 => Self::AND,
            2 => Self::AND_NB,
            3 => Self::A,
            4 => Self::AND_NA,
            5 => Self::B,
            6 => Self::XOR,
            7 => Self::OR,
            8 => Self::NOR,
            9 => Self::EQUIV,
            10 => Self::NB,
            11 => Self::OR_NB,
            12 => Self::NA,
            13 => Self::OR_NA,
            14 => Self::NAND,
            15 => Self::T,
            _ => unreachable!(),
        }
    }

    const fn evaluate(&self, a: bool, b: bool) -> bool {
        match self {
            Self::F => false,
            Self::AND => a & b,
            Self::AND_NB => a & (!b),
            Self::A => a,
            Self::AND_NA => (!a) & b,
            Self::B => b,
            Self::XOR => a ^ b,
            Self::OR => a | b,
            Self::NOR => !(a | b),
            Self::EQUIV => (a & b) | ((!a) & (!b)),
            Self::NB => !b,
            Self::OR_NB => (!b) | a,
            Self::NA => !a,
            Self::OR_NA => (!a) | b,
            Self::NAND => !(a & b),
            Self::T => true,
        }
    }
}

impl Circuit<BaseGate<2, u8>> {
    pub const INFLATIONARY_GATES: [(usize, [(u8, [u8; 2], Base2GateControlFunc); 4]); 144] = {
        const ENCODED: [usize; 144] = [
            4350003, 4331715, 3179571, 1636995124, 4737099, 1384931404, 2396235, 2368803, 4727955,
            154213012, 105457420, 3152139, 1689289876, 1216659, 306406180, 1198371, 820419, 811275,
            12804147, 11568179, 1628672052, 12720835, 13125707, 10850379, 10757923, 1376608332,
            1680901268, 1282195, 1388536100, 1264419, 886467, 876811, 13116563, 162601620,
            113846028, 11540747, 12720323, 1628606516, 3245107, 12738611, 13182099, 1187587340,
            3218187, 1227954836, 9605267, 1680966804, 9274563, 9200395, 314794788, 9586979,
            13126219, 1376543308, 2462283, 2434339, 1637060660, 11633715, 4332227, 4415539,
            9670803, 1689355412, 9209539, 9265931, 1380147492, 9653027, 4793491, 1179198732,
            11606795, 1236343444, 4737611, 10785355, 10823459, 1384997452, 1376542796, 10757411,
            10784843, 4802635, 1236342932, 11606283, 1179199244, 4794003, 9652515, 1380148004,
            9199883, 9209027, 1680901780, 9605779, 4416051, 4397251, 11568691, 1628607028, 2369315,
            2461771, 1384996940, 13191243, 9587491, 314794276, 9265419, 9275075, 1689290388,
            9671315, 1227954324, 3217675, 1187587852, 13182611, 12739123, 3180083, 1637061172,
            12786371, 11541259, 113845516, 162601108, 13117075, 811787, 885955, 1263907,
            1388536612, 1217171, 1689355924, 1384931916, 10822947, 10850891, 13191755, 12785859,
            1636995636, 11634227, 12804659, 877323, 820931, 1198883, 306405668, 1282707,
            1680967316, 3152651, 105456908, 154212500, 4728467, 2434851, 2396747, 1376608844,
            4803147, 1628672564, 3245619, 4397763, 4350515,
        ];

        use Base2GateControlFunc::{A, NA};

        let mut t = [(0, [(0, [0; 2], A); 4]); 144];
        let mut i = 0;
        while i < 144 {
            let mut encoded = ENCODED[i];
            t[i].0 = encoded & 0b111;
            encoded >>= 3;
            let mut j = 0;
            while j < t[i].0 {
                t[i].1[j] = (
                    (encoded & 0b11) as u8,
                    [((encoded >> 2) & 0b11) as u8, ((encoded >> 4) & 0b11) as u8],
                    if (encoded >> 6) & 1 == 0 { A } else { NA },
                );
                encoded >>= 7;
                j += 1;
            }
            i += 1;
        }
        t
    };

    pub fn sample_mutli_stage_cipher(n: usize, mut rng: impl RngCore) -> Self {
        let log_n = n.next_power_of_two().ilog2() as usize;

        let stages = [true, false, true].map(|is_inflationary| {
            let pi = {
                let mut indices = (0..n as u8).collect_vec();
                indices.shuffle(&mut rng);
                indices
            };

            let layers = (0..log_n)
                .map(|l| {
                    let step = 3usize.pow(l as u32);
                    let chunk_step = 3 * step;
                    (0..n)
                        .step_by(chunk_step)
                        .flat_map(|offset| {
                            (offset..)
                                .take(step)
                                .map(|i| [i % n, (i + step) % n, (i + step + step) % n])
                        })
                        .take((n + 2) / 3)
                        .collect_vec()
                })
                .collect_vec();

            let pi_layers = layers
                .into_iter()
                .map(|triplets| {
                    triplets
                        .into_iter()
                        .map(|[i, j, k]| [pi[i], pi[j], pi[k]])
                        .collect_vec()
                })
                .collect_vec();

            if is_inflationary {
                izip!(
                    pi_layers.into_iter().flatten(),
                    Self::INFLATIONARY_GATES.choose_multiple(&mut rng, log_n * ((n + 2) / 3) * 3)
                )
                .flat_map(|(triplet, &(m, gates))| {
                    gates.into_iter().take(m).map(
                        move |(target, [control0, control1], control_func)| {
                            (
                                triplet[target as usize],
                                [triplet[control0 as usize], triplet[control1 as usize]],
                                control_func as u8,
                            )
                        },
                    )
                })
                .collect_vec()
            } else {
                izip!(
                    pi_layers.into_iter().flatten(),
                    repeat_with(|| rng.next_u32())
                        .flat_map(|v| v.to_le_bytes())
                        .map(|v| v % BaseGate::<2, u8>::N_CONTROL_FUNC)
                )
                .map(|(triplet, control_func)| (triplet[0], [triplet[1], triplet[2]], control_func))
                .collect_vec()
            }
        });

        Self::new(
            izip!(0.., stages.into_iter().flatten())
                .map(|(id, (target, controls, control_func))| {
                    BaseGate::new(id, target, controls, control_func)
                })
                .collect(),
            n as _,
        )
    }
}

#[cfg(test)]
mod test {
    use crate::circuit::{Base2GateControlFunc, BaseGate, Circuit};
    use core::array::from_fn;
    use itertools::{chain, izip, Itertools};
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;
    use std::collections::HashSet;

    #[test]
    fn inflationary_gates() {
        // Appendix B: Inflationary gates in https://arxiv.org/pdf/2011.06546
        #[allow(clippy::zero_prefixed_literal)]
        const TABLE: [usize; 144] = [
            03567421, 03657412, 03745621, 03746512, 05367241, 05637214, 05723641, 05726314,
            06357142, 06537124, 06713542, 06715324, 07345261, 07346152, 07523461, 07526134,
            07613452, 07615234, 12476530, 12654730, 12657403, 12746503, 14276350, 14632750,
            14637205, 14726305, 16254370, 16257043, 16432570, 16437025, 16702543, 16704325,
            17246053, 17426035, 17602453, 17604235, 21475630, 21564730, 21567403, 21745603,
            24175360, 24531760, 24537106, 24715306, 25164370, 25167043, 25431670, 25437016,
            25701643, 25704316, 27145063, 27415036, 27501463, 27504136, 30475621, 30476512,
            30564721, 30654712, 34075261, 34076152, 34520761, 34526107, 34610752, 34615207,
            35064271, 35420671, 35426017, 35604217, 36054172, 36410572, 36415027, 36504127,
            41273650, 41362750, 41367205, 41723605, 42173560, 42351760, 42357106, 42713506,
            43162570, 43167025, 43251670, 43257016, 43701625, 43702516, 47123065, 47213056,
            47301265, 47302156, 50273641, 50276314, 50362741, 50632714, 52073461, 52076134,
            52340761, 52346107, 52610734, 52613407, 53062471, 53240671, 53246017, 53602417,
            56032174, 56210374, 56213047, 56302147, 60173542, 60175324, 60351742, 60531724,
            61073452, 61075234, 61340752, 61345207, 61520734, 61523407, 63051472, 63140572,
            63145027, 63501427, 65031274, 65120374, 65123047, 65301247, 70162543, 70164325,
            70251643, 70254316, 70431625, 70432516, 71062453, 71064235, 71240653, 71420635,
            72051463, 72054136, 72140563, 72410536, 74031265, 74032156, 74120365, 74210356,
        ];

        use Base2GateControlFunc::{A, NA};

        let permutation = |gates: &[(u8, [u8; 2], Base2GateControlFunc)]| {
            let circuit = Circuit::new(
                izip!(0.., gates)
                    .map(|(id, &(target, controls, control_func))| {
                        BaseGate::new(id, target, controls, control_func as _)
                    })
                    .collect(),
                3,
            );
            (0..1 << 3)
                .map(|inputs| {
                    let mut inputs = (0..3).map(|i| (inputs >> i) & 1 == 1).collect_vec();
                    circuit.run(&mut inputs);
                    inputs.iter().rfold(0, |v, bit| (v << 1) ^ *bit as usize)
                })
                .fold(0, |v, outputs| (v * 10) + outputs)
        };

        let wire_permutation = [
            (0, 1, 2),
            (0, 2, 1),
            (1, 0, 2),
            (1, 2, 0),
            (2, 0, 1),
            (2, 1, 0),
        ];

        // A
        let a_permutations = wire_permutation
            .into_iter()
            .cartesian_product(0..1 << 4)
            .map(|((w0, w1, w2), control_funcs)| {
                let [c0, c1, c2, c3] =
                    from_fn(|i| if (control_funcs >> i) & 1 == 1 { A } else { NA });
                let gates = vec![
                    (w1, [w0, w2], c0),
                    (w1, [w2, w0], c1),
                    (w0, [w1, w2], c2),
                    (w2, [w1, w0], c3),
                ];
                (permutation(&gates), gates)
            })
            .collect_vec();
        assert_eq!(a_permutations.iter().map(|(p, _)| p).unique().count(), 24);
        assert!(HashSet::from_iter(a_permutations.iter().map(|(p, _)| *p))
            .is_subset(&HashSet::from(TABLE)));

        // B
        let b_permutations = wire_permutation
            .into_iter()
            .cartesian_product(0..1 << 4)
            .map(|((w0, w1, w2), control_funcs)| {
                let [c0, c1, c2, c3] =
                    from_fn(|i| if (control_funcs >> i) & 1 == 1 { A } else { NA });
                let gates = vec![
                    (w2, [w1, w0], c0),
                    (w0, [w1, w2], c1),
                    (w1, [w2, w0], c2),
                    (w1, [w0, w2], c3),
                ];
                (permutation(&gates), gates)
            })
            .collect_vec();
        assert_eq!(b_permutations.iter().map(|(p, _)| p).unique().count(), 24);
        assert!(HashSet::from_iter(b_permutations.iter().map(|(p, _)| *p))
            .is_subset(&HashSet::from(TABLE)));

        // C
        let c_permutations = wire_permutation
            .into_iter()
            .cartesian_product(0..1 << 3)
            .map(|((w0, w1, w2), control_funcs)| {
                let [c0, c1, c2] = from_fn(|i| if (control_funcs >> i) & 1 == 1 { A } else { NA });
                let gates = vec![(w0, [w2, w1], c0), (w2, [w1, w0], c1), (w1, [w0, w2], c2)];
                (permutation(&gates), gates)
            })
            .collect_vec();
        assert_eq!(c_permutations.iter().map(|(p, _)| p).unique().count(), 48);
        assert!(HashSet::from_iter(c_permutations.iter().map(|(p, _)| *p))
            .is_subset(&HashSet::from(TABLE)));

        // D
        let d_permutations = wire_permutation
            .into_iter()
            .cartesian_product(0..1 << 3)
            .map(|((w0, w1, w2), control_funcs)| {
                let [c0, c1, c2] = from_fn(|i| if (control_funcs >> i) & 1 == 1 { A } else { NA });
                let gates = vec![(w1, [w0, w2], c0), (w2, [w1, w0], c1), (w0, [w2, w1], c2)];
                (permutation(&gates), gates)
            })
            .collect_vec();
        assert_eq!(d_permutations.iter().map(|(p, _)| p).unique().count(), 48);
        assert!(HashSet::from_iter(d_permutations.iter().map(|(p, _)| *p))
            .is_subset(&HashSet::from(TABLE)));

        // All
        assert_eq!(
            chain![
                &a_permutations,
                &b_permutations,
                &c_permutations,
                &d_permutations,
            ]
            .map(|(p, _)| p)
            .unique()
            .count(),
            144
        );

        // From encoded
        let table = Circuit::<BaseGate<2, u8>>::INFLATIONARY_GATES
            .into_iter()
            .map(|(m, gates)| permutation(&gates[..m]))
            .collect::<HashSet<_>>();
        assert_eq!(table.len(), 144);
        assert!(table.is_subset(&HashSet::from(TABLE)));
    }

    #[test]
    fn sample_mutli_stage_cipher() {
        let mut rng = ChaCha8Rng::from_entropy();
        let circuit = Circuit::sample_mutli_stage_cipher(64, &mut rng);

        dbg!(circuit.n());
        dbg!(circuit.gates().len());
    }
}
