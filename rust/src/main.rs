use rand::{distributions::Uniform, thread_rng, Rng};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};

trait Gate {
    type Input: ?Sized;
    type Target;
    type Controls;

    fn run(&self, input: &mut Self::Input);
    fn target(&self) -> Self::Target;
    fn controls(&self) -> &Self::Controls;
}

struct BaseGate<const N: usize, D> {
    target: D,
    controls: [D; N],
    control_func: fn(&[D; N], &[bool]) -> bool,
}

impl<const N: usize, D> Gate for BaseGate<N, D>
where
    D: Into<usize> + Copy,
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
                target: target,
                controls: controls,
                control_func: (|controls, inputs| {
                    inputs[controls[0] as usize] & inputs[controls[1] as usize]
                }),
            }
        };
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

    let mut visited_circuits = HashSet::new();

    while curr_iter < max_iterations {
        let (random_circuit, circuit_trace) =
            sample_circuit_with_base_gate(ell_in as usize, circuit.n as u8, 1.0);

        if visited_circuits.contains(&circuit_trace) {
            println!("Circuit sampled twice: {}", circuit_trace);
            print_circuit_with_base_gates(&random_circuit);
            println!();
            continue;
        } else {
            visited_circuits.insert(circuit_trace);
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

    println!("Iteration count: {}", curr_iter);

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
    D: Into<usize> + Copy,
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

fn main() {
    let ell_out = 2;
    let ell_in = 5;
    let n = 7;
    let (circuit, _) = sample_circuit_with_base_gate(ell_out, n, 1.0);
    print_circuit_with_base_gates(&circuit);

    let replacement_circuit = replacement_circuit(&circuit, ell_in).unwrap();
    print_circuit_with_base_gates(&replacement_circuit);
    println!("Input permutation map: ");
    print_permutation_map(&circuit);
    println!("Output permutation map: ");
    print_permutation_map(&replacement_circuit);
}
