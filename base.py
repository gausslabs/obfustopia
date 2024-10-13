from enum import Enum
import random
import copy
from utils import sample_wire, draw_directed_graph, export_gephi, run_community_detection
from graph import GraphGate, GraphReversibleCircuit, skeleton_graph, SkeletonGraph
from typing import Callable, Union
import networkx as nx


TwoBitControl = Callable[[bool, bool], bool]
ThreeBitControl = Callable[[bool, bool, bool], bool]
FourBitControl = Callable[[bool, bool, bool, bool], bool]

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


four_bit_base_controls: dict[int, FourBitControl] = {
    0: lambda a, b, c, d: a and b and c and d
}

    
def sample_base_control() -> int:
    # return 1
    return random.randrange(0, 16)

class BaseGate(GraphGate):

    def __init__(
        self, 
        control_function: Union[ThreeBitControl, TwoBitControl, FourBitControl],
        target: int,
        control_0: int, 
        control_1: int,
        control_2: int=None,
        control_3: int=None,
    ):
        if control_function.__code__.co_argcount == 4:
            assert control_3 is not None
            assert control_2 is not None
        elif control_function.__code__.co_argcount == 3:
            assert control_2 is not None
            assert control_3 is None
        else:
            assert control_2 is None
            assert control_3 is None
        
        self._id = 0
        self._control_function = control_function
        self._control_0 = control_0
        self._control_1 = control_1
        self._control_2 = control_2
        self._control_3 = control_3
        self._target = target
    
    def run(self, input_wires: list[bool]):
        control_bit = False
        if self._control_function.__code__.co_argcount == 2:
            control_bit = self._control_function(input_wires[self._control_0], input_wires[self._control_1])
        elif self._control_function.__code__.co_argcount == 3:            
            control_bit = self._control_function(input_wires[self._control_0], input_wires[self._control_1], input_wires[self._control_2])
        else: 
            control_bit = self._control_function(input_wires[self._control_0], input_wires[self._control_1], input_wires[self._control_2], input_wires[self._control_3])
        
        input_wires[self._target] = input_wires[self._target] ^ control_bit

    def id(self) -> int:
        return self._id

    def control0(self) -> int:
        return self._control_0

    def control1(self) -> int:
        return self._control_1

    def control2(self) -> int:
        return self._control_2

    def control3(self) -> int:
        return self._control_3

    def control_function(self) -> Union[ThreeBitControl, TwoBitControl]:
        return self._control_function

    def target(self) -> int:
        return self._target

class BaseReversibleCircuit(GraphReversibleCircuit):
    def __init__(self, gates: [BaseGate], n: int, sampling_trace: str=None):
        self._gates = gates
        self._n = n
        self._sampling_trace = sampling_trace
        self._gates_dict = {}

        # set gate ids
        for (index, g) in enumerate(self._gates):
            g._id = index
            self._gates_dict[index] = g
    
    def run(self, input: list[bool]):
        assert len(input) == self._n

        for g in self._gates:
            g.run(input)
    
    def gates(self) -> list[BaseGate]:
        return self._gates

    def gates_dict(self, id: int) -> BaseGate:
        g = self._gates_dict[id]
        assert g is not None
        return g

    def break_into_2_way_gates(self):
        # TODO: check whether there's need to break. No need to break if there no gates with more than 2 controls
        new_gates = []
        new_wires = self._n+1
        wire_k = self._n # new wire add; used as temporary storage
        for g in self._gates:
            if g.control2() is None:
                new_gates.append(copy.deepcopy(g))
            else:
                if g.control3() is not None:
                    print("No replacement strategy for 4 input controls")
                else:
                    wire0 = g.control0()
                    wire1 = g.control1()
                    wire2 = g.target()
                    wire3 = g.control2()
                    wire4 = wire_k

                    new_gates.append(
                        BaseGate(
                            control_function=two_bit_base_controls[1],
                            target=wire4,
                            control_0=wire1, 
                            control_1=wire3
                        )
                    )

                    new_gates.append(
                        BaseGate(
                            control_function=two_bit_base_controls[1],
                            target=wire2,
                            control_0=wire0, 
                            control_1=wire4
                        )
                    )

                    new_gates.append(
                        BaseGate(
                            control_function=two_bit_base_controls[1],
                            target=wire4,
                            control_0=wire1, 
                            control_1=wire3
                        )
                    )

                    new_gates.append(
                        BaseGate(
                            control_function=two_bit_base_controls[1],
                            target=wire2,
                            control_0=wire0, 
                            control_1=wire4
                        )
                    )

        return BaseReversibleCircuit(
            gates=new_gates,
            n=new_wires
        )



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
                elif g.control2() is not None and g.control2() == i:
                    out += f" I "
                else:
                    out += f" _ "
            
            # gate 
            out += f" c_id: {g.control_function()}"
            out += "\n"
        return out
    
def _sample_random_reversible_circuit_strategy_1(n: int, gate_count: int):

    gates = []
    sampling_trace = ""
    for i in range(0, gate_count):
        target = sample_wire(n, not_in=[])
        not_in = [target]

        control0 = sample_wire(n=n, not_in=not_in)
        not_in.append(control0)
        control1 = sample_wire(n=n, not_in=not_in)

        sampling_trace += f"{target},{control0},{control1},"

        gates.append(
            BaseGate(
                control_function=two_bit_base_controls[1],
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

    
def _sample_random_reversible_circuit_strategy_2(n: int, gate_count: int, max_controls: int):
    assert n >= max_controls+1

    gates = []
    sampling_trace = ""
    curr_gate_count = 0
    while curr_gate_count < gate_count:
        target = sample_wire(n, not_in=[])
        not_in = [target]

        control0 = None
        control1 = None
        control2 = None
        control3 = None
        control_function = None
        
        if max_controls == 2:
            control0 = sample_wire(n=n, not_in=not_in)
            not_in.append(control0)
            control1 = sample_wire(n=n, not_in=not_in)
            control_function = two_bit_base_controls[1] # CCNOT
            curr_gate_count += 1
        elif max_controls == 3:
            if random.choice([True, False]):
                control0 = sample_wire(n=n, not_in=not_in)
                not_in.append(control0)
                control1 = sample_wire(n=n, not_in=not_in)
                control_function = two_bit_base_controls[1] # CCNOT
                curr_gate_count += 1
            else:
                control0 = sample_wire(n=n, not_in=not_in)
                not_in.append(control0)
                control1 = sample_wire(n=n, not_in=not_in)
                not_in.append(control1)
                control2 = sample_wire(n=n, not_in=not_in)
                control_function = three_bit_base_controls[0] # CCCNOT
                curr_gate_count += 4
        elif max_controls == 4:
            choice = random.choice([0, 2])
            if choice == 0:
                control0 = sample_wire(n=n, not_in=not_in)
                not_in.append(control0)
                control1 = sample_wire(n=n, not_in=not_in)
                control_function = two_bit_base_controls[1] # CCNOT
                curr_gate_count += 1
            elif choice == 1:
                control0 = sample_wire(n=n, not_in=not_in)
                not_in.append(control0)
                control1 = sample_wire(n=n, not_in=not_in)
                not_in.append(control1)
                control2 = sample_wire(n=n, not_in=not_in)
                control_function = three_bit_base_controls[0] # CCCNOT
                curr_gate_count += 4
            elif choice == 2:
                control0 = sample_wire(n=n, not_in=not_in)
                not_in.append(control0)
                control1 = sample_wire(n=n, not_in=not_in)
                not_in.append(control1)
                control2 = sample_wire(n=n, not_in=not_in)
                not_in.append(control2)
                control3 = sample_wire(n=n, not_in=not_in)
                control_function = four_bit_base_controls[0] # CCCCNOT
                curr_gate_count += 8


        sampling_trace += f"{target},{control0},{control1},{control2},{control3},"

        gates.append(
            BaseGate(
                control_function=control_function,
                control_0=control0,
                control_1=control1,
                control_2=control2,
                control_3=control3,
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
        

def find_replacement(circuit_to_replace: BaseReversibleCircuit, ell_in: int, max_controls: int=2) -> BaseReversibleCircuit:
    permutation_map = input_output_permutation(circuit=circuit_to_replace)

    print("No. of wires: ", circuit_to_replace._n)
    # print("Permutation map: ", permutation_map)
    # print(circuit_to_replace.print_circuit())

    exhausted_circuits = set()
    curr_circuit = _sample_random_reversible_circuit_strategy_2(n=circuit_to_replace._n, gate_count=ell_in, max_controls=max_controls)
    exhausted_circuits.add(curr_circuit._sampling_trace)
    # curr_permutation_map = input_output_permutation(circuit=curr_circuit)
    count = 0
    while True:
        found = check_input_output_permutation(circuit=curr_circuit, permutation_map=permutation_map)
        if found: 
            break

        curr_circuit = _sample_random_reversible_circuit_strategy_2(n=circuit_to_replace._n, gate_count=ell_in, max_controls=max_controls)

        if curr_circuit._sampling_trace in exhausted_circuits:
            # print("Sampled TWICE: ", curr_circuit._sampling_trace)
            pass
        else:
            exhausted_circuits.add(curr_circuit._sampling_trace)

        count += 1
        if count == 10000000:
            break
    # print("Permutation map (out): ", input_output_permutation(circuit=curr_circuit))
    # print(curr_circuit.print_circuit())
    # print("Total Iterations: ", count)
    return curr_circuit

def find_convex_subset(main_graph: nx.Graph, convex_set_size: int):
    '''
    TODO: Why can't this function return toloptically sorted convex subgraph
    '''
    
    T = convex_set_size

    v = random.choice(list(main_graph.nodes()))
    convex_set = {v}


    root = v
    explored_candidates = set()

    # generate a set of candidates to explore
    to_explore_canidates = []
    for node in convex_set:
        for e in main_graph.edges(node):
            to_explore_canidates.append(e[1])

    while len(convex_set) < T:
        if to_explore_canidates.__len__() == 0:
            print("Cannot find convex graph")
            break
    
        subset_to_check_against = copy.deepcopy(convex_set)

        # find next
        # take a random element in the convex set. Expand it by adding randomly one of its edges (At the moment we restrict to outgoing edges. But that isn't necessary)
        candidate = to_explore_canidates.pop()

        # optimistically add candidate to the set. Then check whether the graph remains convex. 
        convex_set.add(candidate)
        
        visited = set()
        greedy_add_for_convex = set() #TODO: the moment greedy set grows larger than T it is safe to terminate explortation for the candidate
        for r in subset_to_check_against:
            # start DFS
            
            # next = (list(graph.out_edges(r))[0])[1]
                
            all_paths = []
            path = []
            path.append(r)
            while len(path) > 0:
                
                tmp = list(main_graph.out_edges(path[-1]))

                next = None
                while next==None or next in visited:
                    if len(tmp) == 0:
                        next = None
                        break

                    next = tmp.pop()[1]

                # print(path, next, candidate)

                if next == None:
                    visited.add(path.pop())
                elif next == candidate:
                    all_paths.append(copy.deepcopy(path))
                    visited.add(path.pop())
                    # TODO: pop the path entirely because the candidate is found. 
                    # But I suppose we should keep exploring to find all path 
                    # because we want to make the set convex
                else:
                    path.append(next)
            
            print(all_paths)
            for p in all_paths:
                for n in p:
                    if n not in convex_set:
                        greedy_add_for_convex.add(n)
            
        if greedy_add_for_convex.__len__() != 0:
            # print(list(greedy_add_for_convex))
            # check whether there's space to add them?
            if greedy_add_for_convex.__len__() + len(convex_set) <= T:

                # add candidates
                for node in greedy_add_for_convex:
                    for e in main_graph.edges(node):
                        if e[1] not in explored_candidates:
                            to_explore_canidates.append(e[1])
                    
                convex_set = convex_set.union(greedy_add_for_convex)
            else:
                convex_set.remove(candidate)

        explored_candidates.add(candidate)
                
    return list(convex_set)

    ####### Find the subgraph to repalce. Topoligical sort it. Then convert it into a revesible circuit to compute the permutation #####

def mixing_iteration(main_circuit: BaseReversibleCircuit, main_graph: nx.Graph, ell_out: int, ell_in: int):
    # extract a subgraph in of convex se
    convex_set = find_convex_subset(main_graph=main_graph, convex_set_size=ell_out)

    G_convex = main_graph.subgraph(list(convex_set))
    # topological sort the gates for correct dependencies. The reversivle circuit of concex subgraph G should reflect the dependencies
    gates_id = list(nx.topological_sort(G=G_convex))
    print(gates_id)
    try:
        # Try to find a cycle
        cycle = nx.find_cycle(main_graph, orientation="original")
        print(True)  # Cycle exists
    except nx.NetworkXNoCycle:
        print(False)  # No cycle exists
    # print(list(nx.all_simple_paths(G=main_graph, source=gates_id[0], target=gates_id[1])))
    for f in nx.all_simple_paths(G=main_graph, source=gates_id[0], target=gates_id[1]):
        print(f)

    # construct C_OUT
    # \omega_out = active wires of C_OUT
    omega_out = set()
    for id in gates_id:
        g = main_circuit.gates_dict(id)
        assert g.control2() == None
        assert g.control3() == None
        omega_out.add(
            g.control0()
        )
        omega_out.add(
            g.control1()
        )
        omega_out.add(
            g.target()
        )

    old_to_new_map = {}
    new_to_old_map = {}
    for (index, wire) in enumerate(omega_out):
        old_to_new_map[wire] = index
        new_to_old_map[index] = wire

    gates = []
    for id in gates_id:
        g = main_circuit.gates_dict(id)
        gates.append(
            BaseGate(
                control_0=old_to_new_map[g.control0()],
                control_1=old_to_new_map[g.control1()],
                # control_2=old_to_new_map[g.control2()],
                # control_3=old_to_new_map[g.control3()],
                target=old_to_new_map[g.target()],
                control_function=g.control_function()
            )
        )
    c_out = BaseReversibleCircuit(gates=gates, n=len(omega_out))
    print("======C_OUT======")
    print(c_out.print_circuit())

    # C_IN with gates with maybe 3-4 control wires
    c_dash_in = find_replacement(circuit_to_replace=c_out, ell_in=ell_in, max_controls=3)
    print("======C'_IN======")
    print(c_dash_in.print_circuit())

    # C_IN with gates with only 2 control wires
    c_in = c_dash_in.break_into_2_way_gates()
    print("======C_IN======")
    print(c_in.print_circuit())

    # Find immediate predecessors and immediate sucessors of subgraph c_out
    imm_predecessors = set()
    imm_successors = set()
    for id in gates_id:
        for incoming_edge in main_graph.in_edges(id):
            imm_predecessors.add(incoming_edge[0])
        for outgoing_edge in main_graph.out_edges(id):
            imm_successors.add(outgoing_edge[1])
    imm_predecessors.difference_update(set(gates_id))
    imm_successors.difference_update(set(gates_id))

    print(imm_predecessors, imm_successors)

    # Find outsiders O
    # DFS from predeccessors and successors
    visited = set()
    imm_predecessors = list(imm_predecessors)
    while len(imm_predecessors) > 0:
        edges = list(main_graph.in_edges(imm_predecessors[-1]))

        next = None
        while next == None or next in visited:
            if len(edges) == 0:
                next = None
                break
            next = edges.pop()[0]
        
        if next == None:
            visited.add(imm_predecessors.pop())
        else:
            imm_predecessors.append(next)

    imm_successors = list(imm_successors)
    while len(imm_successors) > 0:
        edges = list(main_graph.out_edges(imm_successors[-1]))
        next = None
        while next == None or next in visited:
            if len(edges) == 0:
                next = None
                break
            next = edges.pop()[1]
        
        if next == None:
            visited.add(imm_successors.pop())
        else:
            imm_successors.append(next)
    print(main_graph.nodes(), gates_id)
    print(visited.difference(set(list(main_graph.nodes()))))
    # DFS from successors 

    # pop the nodes in subgraph C_OUT
    

    

    

# circuit = _sample_random_reversible_circuit_strategy_2(n=10, gate_count=10, max_controls=2)
# skeleton = skeleton_graph(circuit=circuit)

main_circuit = _sample_random_reversible_circuit_strategy_2(n=128, gate_count=1000, max_controls=2)
skeleton = skeleton_graph(circuit=main_circuit)
main_graph = skeleton.nx_graph()
mixing_iteration(main_circuit=main_circuit, main_graph=main_graph, ell_in=10, ell_out=2)


# draw_directed_graph(edges=skeleton.directed_edges())
# export_gephi(edges=skeleton.directed_edges())
# find_replacement(graph=skeleton)
# run_community_detection(edges=skeleton.directed_edges())

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
