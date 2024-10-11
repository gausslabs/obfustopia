from enum import Enum
import random
import copy

N_DEFAULT = 10



class ControlFunction(Enum):
    AND = 1
    OR = 2


class Gate:
    def __init__(
        self, 
        target: int, 
        controls: list[int],
        control_function: ControlFunction, 
    ):
        '''
        target: index of target wire
        controls: indices of control wires
        '''
        self.id = None
        self.target = target
        self.controls = controls
        self.control_function = control_function
        pass

    def run(self, input_wires: list[bool]):
        control_bit = False
        if self.control_function == ControlFunction.AND:
            control_bit = input_wires[self.controls[0]]
            for i in range(1, len(self.controls)):
                control_bit = control_bit and input_wires[self.controls[i]]
        elif self.control_function == ControlFunction.OR:
            control_bit = input_wires[self.controls[0]]
            for i in range(1, len(self.controls)):
                control_bit = control_bit or input_wires[self.controls[i]]
        else:
            assert False
        input_wires[self.target] = input_wires[self.target] ^ control_bit


class ReversibleCircuit:
    def __init__(self, gates: [Gate], n:int = N_DEFAULT):
        self.gates = gates
        self.n = n

        # Assign ids to gates
        for i in range(0, len(self.gates)):
            self.gates[i].id = i

    def active_wires(self) -> set[int]:
        wires = set()
        for g in self.gates:
            wires.add(g.target)
            for j in g.controls:
                wires.add(j)

        return wires

    def run(self, input_wires: list[bool]):
        assert len(input_wires) == self.n
        for g in self.gates:
            g.run(input_wires=input_wires)

    def permutation_map(self) -> dict[int: int]:
        # isolate the active wires and calculate the permutation for the active wires
        # TODO: change this to no. of active wires
        # active_wires = self.active_wires()
        count_active_wires = self.n

        permutation_map = {}
        for perm_in in range(0, 1<<count_active_wires):
            # construct input list, starting with 0th wire
            input = []
            for i in range(0, count_active_wires):
                input.append(bool((perm_in >> i) & 1))
            
            output = copy.deepcopy(input)
            self.run(input_wires=output)
            perm_out = 0
            for i in range(0, count_active_wires):
                perm_out += (int(output[i])<<i)
            # print(input, output)
            permutation_map[perm_in] = perm_out

        return permutation_map

    def print_circuit(self) -> str:
        out = ''
        for i in range(0, self.n):
            out += f"---"
        out += "\n"

        for i in range(0, self.n):
            out += f" {i} "
        out += "\n"

        for i in range(0, self.n):
            out += f"---"
        out += "\n"

        for g in self.gates:
            for i in range(0, self.n):
                if i == g.target:
                    out += f" O "
                elif i in g.controls:
                    out += f" I "
                else:
                    out += f" _ "
            
            # gate 
            if g.control_function == ControlFunction.AND:
                out += f" f(AND,{len(g.controls)})"
            elif g.control_function == ControlFunction.OR:
                out += f" f(OR,{len(g.controls)})"
            out += "\n"
        return out

def sample_control_function():
    '''
    Sample a control function at random
    '''
    return list(ControlFunction)[random.randrange(0, len(ControlFunction))]

def sample_wire(n: int, not_in: [list]) -> int: 
    assert len(not_in) < n

    wire = random.randrange(0, n)
    while wire in not_in:
        wire = random.randrange(0, n)
    return wire

def find_alternate(circuit: ReversibleCircuit, out_gates: int) -> ReversibleCircuit:
    '''
    `out_gates` must be >= gates in circuit for efficient runtime
    '''
    permutation_map = circuit.permutation_map()
    wires = circuit.n

    random_circuit = sample_random_circuit(wires=wires, gate_count=out_gates, max_control_wires=3)
    random_perm_map = random_circuit.permutation_map()
    count = 1
    while permutation_map != random_perm_map:
        random_circuit = sample_random_circuit(wires=wires, gate_count=out_gates,  max_control_wires=3)
        random_perm_map = random_circuit.permutation_map()
        count +=1
        print(count)

    return random_circuit

def sample_random_circuit(wires: int, gate_count: int, max_control_wires: int=2) ->  ReversibleCircuit:
    assert max_control_wires >= 2

    # TODO: sample gates with more than 2 control wires requires decomposing wires into gates using 2 control wires.
    # We should mantain a heuristic that modifies no. of gates left as the circuit is sampled. For example, 3-CCNOT is equivalent to  4 gates. 

    gates = []
    gate_count = gate_count
    while gate_count >= 0:
        control_f = ControlFunction.AND
        target_wire = sample_wire(n=wires, not_in=[])
        input_wires = []

        # sample no. of control wires 1 can use
        # no_of_controls = random.randint(0, wires-1)

        tmp = random.randrange(2, max_control_wires+1)
        if tmp == 2:
            gate_count -= 1
        elif tmp == 3:
            gate_count -= 4

        # keep it simple for now; stick with 2 input wires
        not_in = [target_wire]
        for _ in range(0, tmp):
            w = sample_wire(n=wires, not_in=not_in)
            input_wires.append(w)
            not_in.append(w)

        gates.append(
            Gate(
                target=target_wire,
                controls=input_wires,
                control_function=control_f
            )
        )

    return ReversibleCircuit(
        gates=gates, 
        n=wires
    )
            
# circuit = sample_random_circuit(wires=5, gate_count=2)
# circuit0 = ReversibleCircuit(
#     gates=[
#         Gate(target=2, controls=[0, 1], control_function=ControlFunction.AND),
#         Gate(target=1, controls=[0, 2], control_function=ControlFunction.AND),
#     ],
#     n=3
# )

circuit1 = ReversibleCircuit(
    gates=[
        Gate(target=2, controls=[0, 1], control_function=ControlFunction.AND),
        Gate(target=1, controls=[2, 3], control_function=ControlFunction.AND),
    ],
    n=4
)

alternate_circuit = find_alternate(circuit=circuit1, out_gates=10)
print(alternate_circuit.print_circuit())
# print(circuit1.print_circuit())
