from enum import Enum
import random
import copy
from utils import sample_wire, draw_directed_graph
from graph import GraphGate, GraphReversibleCircuit, skeleton_graph, SkeletonGraph
from typing import Callable


TwoBitControl = Callable[[bool, bool], bool]
ThreeBitControl = Callable[[bool, bool, bool], bool]

# Refer to https://i.sstatic.net/tS0my.png for all possible 2-bit input boolean functions
two_bit_base_controls: dict[int, TwoBitControl] = {
   
    0: lambda a, b: False,
    1: lambda a, b: a and b,
    2: lambda a, b: a and (not b),
    3: lambda a, b: a, 
    4: lambda a, b: (not a) and b,
    5: lambda a, b: b,
    6: lambda a, b: a ^ b,
    7: lambda a, b: a or b,
    8: lambda a, b: not (a or b),
    9: lambda a, b: (a and b) or ((not a) and (not b)),
    10: lambda a, b: not a,
    11: lambda a, b: not b,
    12: lambda a, b: (not a) or b,
    13: lambda a, b: (not b) or a,
    14: lambda a, b: not (a and b),
    15: lambda a, b: True,
}

three_bit_base_controls: dict[int, ThreeBitControl] = {
    0: lambda a, b, c: a and b and c
}

def execute_base_control(control_id: int, a: bool, b: bool):
    '''
    Refer to https://i.sstatic.net/tS0my.png for all possible 2-bit input boolean functions
    '''
    assert control_id < 16

    if control_id == 0:
        return False
    elif control_id == 1:
        return a and b
    elif control_id == 2:
        return a and (not b)
    elif control_id == 3:
        return a
    elif control_id == 4:
        return (not a) and b
    elif control_id == 5:
        return b
    elif control_id == 6:
        return a ^ b
    elif control_id == 7:
        return a or b
    elif control_id == 8:
        return not (a or b)
    elif control_id == 9:
        return (a and b) or ((not a) and (not b))
    elif control_id == 10:
        return not a
    elif control_id == 11:
        return not b
    elif control_id == 12:
        return (not a) or b
    elif control_id == 13:
        return (not b) or a
    elif control_id == 14:
        return not (a and b)
    elif control_id == 15:
        return True
    
def sample_base_control() -> int:
    # return 1
    return random.randrange(0, 16)

class BaseGate(GraphGate):

    def __init__(
        self, 
        control_id: int,
        control_0: int, 
        control_1: int,
        target: int
    ):
        self._id = 0
        self._control_id = control_id
        self._control_0 = control_0
        self._control_1 = control_1
        self._target = target
    
    def run(self, input_wires: list[bool]):
        control_bit = execute_base_control(self._control_id, input_wires[self._control_0], input_wires[self._control_1])
        input_wires[self._target] = input_wires[self._target] ^ control_bit

    def id(self) -> int:
        return self._id

    def control0(self) -> int:
        return self._control_0

    def control1(self) -> int:
        return self._control_1

    def control_id(self) -> int:
        return self._control_id

    def target(self) -> int:
        return self._target

class BaseReversibleCircuit(GraphReversibleCircuit):
    def __init__(self, gates: [BaseGate], n: int, sampling_trace: str=None):
        self._gates = gates
        self._n = n
        self._sampling_trace = sampling_trace

        # set gate ids
        for (index, g) in enumerate(self._gates):
            g._id = index
    
    def run(self, input: list[bool]):
        assert len(input) == self._n

        for g in self._gates:
            g.run(input)
    
    def gates(self) -> list[BaseGate]:
        return self._gates

    def print_circuit(self) -> str:
        out = ''
        for i in range(0, self._n):
            out += f"---"
        out += "\n"

        for i in range(0, self._n):
            out += f" {i} "
        out += "\n"

        for i in range(0, self._n):
            out += f"---"
        out += "\n"

        for g in self._gates:
            for i in range(0, self._n):
                if i == g.target():
                    out += f" O "
                elif i == g.control0() or i == g.control1():
                    out += f" I "
                else:
                    out += f" _ "
            
            # gate 
            out += f" c_id: {g.control_id()}"
            out += "\n"
        return out
    
def _sample_random_reversible_circuit(n: int, gate_count: int):

    gates = []
    sampling_trace = ""
    for i in range(0, gate_count):
        target = sample_wire(n, not_in=[])
        not_in = [target]

        control0 = sample_wire(n=n, not_in=not_in)
        not_in.append(control0)
        control1 = sample_wire(n=n, not_in=not_in)

        control_id = sample_base_control()

        sampling_trace += f"{target},{control0},{control1},{control_id},"

        gates.append(
            BaseGate(
                control_id=control_id,
                control_0=control0,
                control_1=control1,
                target=target,
            )
        )

    return BaseReversibleCircuit(
        gates=gates,
        n=n,
        sampling_trace=sampling_trace
    )


def input_output_permutation(circuit: BaseReversibleCircuit) -> dict[int: int]:
    n = circuit._n

    permutation_map = {}
    for v_in in range(0, 1<<n):
        input_wires = []
        for i in range(0, n):
            input_wires.append(
                bool((v_in >> i) & 1)
            )
        
        circuit.run(input=input_wires)

        v_out = 0
        for i in range(0, n):
            v_out += (int(input_wires[i]) << i)

        permutation_map[v_in] = v_out

    return permutation_map

def check_input_output_permutation(circuit: BaseReversibleCircuit, permutation_map: dict[int: int]) -> bool:
    n = circuit._n

    flag = True
    for v_in in range(0, 1<<n):
        input_wires = []
        for i in range(0, n):
            input_wires.append(
                bool((v_in >> i) & 1)
            )
        
        circuit.run(input=input_wires)

        v_out = 0
        for i in range(0, n):
            v_out += (int(input_wires[i]) << i)

        if permutation_map[v_in] != v_out:
            flag = False
            break

    return flag
        

def find_replacement(graph: SkeletonGraph):
    g0 = skeleton.circuit().gates()[1]
    g1 = skeleton.circuit().gates()[list(skeleton.collisions()[1])[0]]

    gates = [g0, g1]

    active_wires = set()
    for g in gates:
        active_wires.add(g.control0())
        active_wires.add(g.control1())
        active_wires.add(g.target())
    active_wires = list(active_wires)
    active_wires.sort()

    # map from old wire id to new wire id
    old_to_new_map = {}
    for (new, old) in enumerate(active_wires):
        old_to_new_map[old] = new

    new_gates = []
    for g in gates:
        new_gates.append(
            BaseGate(
                control_id=g.control_id(),
                control_0=old_to_new_map[g.control0()],
                control_1=old_to_new_map[g.control1()],
                target=old_to_new_map[g.target()],
            )
        )

    # new reversible circuit
    circuit_to_replace = BaseReversibleCircuit(
        gates=new_gates,
        n=len(active_wires)
    )
    permutation_map = input_output_permutation(circuit=circuit_to_replace)

    print("No. of wires: ", circuit_to_replace._n)
    print("Permutation map: ", permutation_map)
    print(circuit_to_replace.print_circuit())

    ell_in = 10
    exhausted_circuits = set()
    curr_circuit = _sample_random_reversible_circuit(n=circuit_to_replace._n, gate_count=ell_in)
    exhausted_circuits.add(curr_circuit._sampling_trace)
    # curr_permutation_map = input_output_permutation(circuit=curr_circuit)
    count = 0
    while True:
        found = check_input_output_permutation(circuit=curr_circuit, permutation_map=permutation_map)
        if found: 
            break

        curr_circuit = _sample_random_reversible_circuit(n=circuit_to_replace._n, gate_count=ell_in)

        if curr_circuit._sampling_trace in exhausted_circuits:
            print("Sampled TWICE: ", curr_circuit._sampling_trace)
        else:
            exhausted_circuits.add(curr_circuit._sampling_trace)

        count += 1
        if count == 10000000:
            break
    print("Permutation map (out): ", input_output_permutation(circuit=curr_circuit))
    print(curr_circuit.print_circuit())
    print("Total Iterations: ", count)
    



circuit = _sample_random_reversible_circuit(n=10, gate_count=10)
skeleton = skeleton_graph(circuit=circuit)
find_replacement(graph=skeleton)

# def trial(): 
#     circuit_to_replace = _sample_random_reversible_circuit(
#         n=5, 
#         gate_count=2
#     )
#     permutation_map = input_output_permutation(circuit=circuit_to_replace)

#     print("No. of wires: ", circuit_to_replace._n)
#     print("Permutation map: ", permutation_map)
#     print(circuit_to_replace.print_circuit())

#     ell_in = 5
#     curr_circuit = _sample_random_reversible_circuit(n=circuit_to_replace._n, gate_count=ell_in)
#     curr_permutation_map = input_output_permutation(circuit=curr_circuit)
#     count = 0
#     while curr_permutation_map != permutation_map:
#         curr_circuit = _sample_random_reversible_circuit(n=circuit_to_replace._n, gate_count=ell_in)
#         curr_permutation_map = input_output_permutation(circuit=curr_circuit)
#         # print("Permutation map: ", curr_permutation_map)
#         count += 1
#         if count == 2000000:
#             break
#     print("Total Iterations: ", count)
# # trial()






# print(list(skeleton._collisions[0])[0])

# draw_directed_graph(edges=skeleton.directed_edges())
