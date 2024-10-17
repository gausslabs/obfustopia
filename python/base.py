from enum import Enum
import random
import copy
from utils import sample_wire, draw_directed_graph, export_gephi, run_community_detection
from graph import GraphGate, GraphReversibleCircuit, skeleton_graph, SkeletonGraph, check_collision
from typing import Callable, Union
import networkx as nx
from itertools import chain

DEBUG = True

GLOBAL_SERIAL = 0
GLOBAL_GATE_DICT = {}

# random.seed(3222)


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
        id: int=0
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
        
        self._id = id
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

    def __str__(self) -> str:
        return f"Gate[{self.id()}]: T={self.target()} C0={self.control0()} C1={self.control1()}"


class BaseReversibleCircuit(GraphReversibleCircuit):
    def __init__(self, gates: [BaseGate], n: int, sampling_trace: str=None):
        self._gates = gates
        self._n = n
        self._sampling_trace = sampling_trace
        self._collision_sets = None
    
    def run(self, input: list[bool]):
        assert len(input) == self._n

        for g in self._gates:
            # if g.id() == 85:
            #     print("#########")
            #     print(f"Inputs: {input[g.control0()]} {input[g.control1()]} {input[g.target()]}")
            g.run(input)
            # if g.id() == 85:
            #     print(f"Outputs: {input[g.control0()]} {input[g.control1()]} {input[g.target()]}")
            #     print("#########")

    def assign_serial_ids_to_gates(self): 
        for (index, g) in enumerate(self._gates):
            g._id = index
    
    def gates(self) -> list[BaseGate]:
        return self._gates

    def break_into_2_way_gates(self):
        new_gates = []
        new_wires = self._n+1
        wire_k = self._n # new wire add; used as temporary storage
        atleast_1_3_gate = False
        for g in self._gates:
            if g.control2() is None:
                new_gates.append(copy.deepcopy(g))
            else:
                if g.control3() is not None:
                    print("No replacement strategy for 4 input controls")
                else:
                    atleast_1_3_gate  = True
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

        # This assumption is used elsewhere 
        assert atleast_1_3_gate

        return BaseReversibleCircuit(
            gates=new_gates,
            n=new_wires
        )

    
    def collision_sets(self) -> dict[int: set[int]]:
        assert self._collision_sets is not None
        return self._collision_sets

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

def global_vars_from_gates(gates: list[BaseGate]):
    global GLOBAL_SERIAL
    global GLOBAL_GATE_DICT

    max_id = 0
    for g in gates:
        max_id = max(max_id, g.id())
        GLOBAL_GATE_DICT[g.id()] = copy.deepcopy(g)

    GLOBAL_SERIAL = max_id

def add_more_gates(gates: list[BaseGate]):
    global GLOBAL_GATE_DICT

    for g in gates:
        GLOBAL_GATE_DICT[g.id()] = g
    
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
            print("Sampled TWICE: ", curr_circuit._sampling_trace)
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

def dfs_with_edge_fn(source: int, visited: set[int], edges_fn):
    '''
    Depth first search of all nodes starting from source node until the end (ie no further exploration is possible). If `edges_fn` returns
    predecessors (resp. successors) then DFS is a upwards traversal (resp. downwards traversal)
    '''

    if source == None or source in visited:
        return 
    else:
        for next_node in edges_fn(source):
            dfs_with_edge_fn(next_node, visited, edges_fn)
        visited.add(source)


def find_nodes_on_paths_from_source_to_target(main_graph: nx.Graph, source: int, target: int) -> set[int]:
    '''
    This function is a slight modication of DFS algorithm. It is based on observation that we don't require to find all paths, instead we require
    to find all nodes on any path from source to target. To do so, we simply run the DFS algorithm but observe that if node D is on a path from S to T
    then all nodes on a path from S to D are also on a path from S to T. Thus we can prune exploration space whenever a node that is fully explored and on some path
    from S to T is reached. 

    - If a path exists then target and source are guaranteed to be in the set
    '''

    paths = []
    path = [source]
    visited = set()
    visited_with_paths = set()
    corr_edges = [list(main_graph.out_edges(source))]
    while len(path) > 0:

        # find outgoing edges from path[-1]
        curr_node = path[-1]

        if curr_node == target:
            # paths.append(copy.deepcopy(path))
            for node in path:
                visited_with_paths.add(node)
            path.pop()
            corr_edges.pop()


        elif curr_node in visited and curr_node in visited_with_paths:
            for node in path:
                visited_with_paths.add(node)

        else:
            outgoing_edges = corr_edges[-1]

            next_node = None 
            while next_node == None or next_node in visited:
                if len(outgoing_edges) == 0:
                    next_node = None    
                    break
                
                next_node = outgoing_edges.pop()[1]

            if next_node is not None:
                path.append(next_node)
                corr_edges.append(list(main_graph.out_edges(next_node)))
            else:
                visited.add(path.pop())
                corr_edges.pop()

    return visited_with_paths


def find_convex_subset(main_graph: nx.Graph, convex_set_size: int):
    '''
    TODO: Why can't this function return toloptically sorted convex subgraph
    '''
    
    T = convex_set_size

    times = 0
    while times < 100:

        v = random.choice(list(main_graph.nodes()))
        convex_set = {v}

        explored_candidates = set()

        # set of candiadtes to explore
        unenxplored_candidates = []
        for node in convex_set:
            for e in main_graph.edges(node):
                unenxplored_candidates.append(e[1])

        while len(convex_set) < T:
            
            if unenxplored_candidates.__len__() == 0:
                break

            candidate = random.choice(unenxplored_candidates)
            unenxplored_candidates.remove(candidate)

            # Union of to_add set over all nodes in current subgraph
            to_add_set_union = set()

            for r in convex_set:
                source = r 
                target = candidate

                to_add_set = find_nodes_on_paths_from_source_to_target(
                    main_graph=main_graph, 
                    source=source, 
                    target=target
                )

                if len(to_add_set) != 0:
                    assert source in to_add_set
                    assert target in to_add_set

                # User Networkx to find all simple paths from source to target and check that they all exist in to_add_set
                # 
                # Note that Networkx all_simple_paths function takes really long occasionally
                # len(to_add_set.difference(set(chain.from_iterable(list(nx.all_simple_paths(source=source, target=target, G=main_graph)))))) == 0

                to_add_set_union = to_add_set_union.union(to_add_set)

            # remove nodes in the existing convex set.
            to_add_set_union.difference_update(convex_set)
            
            if len(to_add_set_union) + len(convex_set) <= T:
                # Update convext set with nodes in to_add set
                convex_set = convex_set.union(to_add_set_union)

                # For newly added nodes add their outgoing edges to unexplored_nodes
                for node in to_add_set:
                    if node not in explored_candidates:
                        unenxplored_candidates.append(node)

            explored_candidates.add(candidate)


        # return of convex set has necessary size
        if len(convex_set) == T:            
            return list(convex_set)
        else:
            times += 1
    
    return None

def mixing_iteration(main_circuit: BaseReversibleCircuit, main_graph: nx.Graph, ell_out: int, ell_in: int, max_controls: int=2):
    global GLOBAL_GATE_DICT
    global GLOBAL_SERIAL

    assert nx.is_directed_acyclic_graph(G=main_graph) == True

    # extract a subgraph in of convex se
    convex_set = find_convex_subset(main_graph=main_graph, convex_set_size=ell_out)

    if convex_set == None:
        print("Didn't find a convex set")
        assert False
        return

    # topological sort the gates for correct dependencies. The reversivle circuit of convex subgraph G should reflect the dependencies
    G_convex = main_graph.subgraph(list(convex_set))
    gates_id = list(nx.topological_sort(G=G_convex))

    if DEBUG: 
        print("--- C_OUT gates ---")
        for g in gates_id:
            print(GLOBAL_GATE_DICT[g])
        print("--- ----------- ---")

    # print("#### Gates that target wire 36 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 36:
    #         print(GLOBAL_GATE_DICT[node])
    # print("#### Gates that target wire 48 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 48:
    #         print(GLOBAL_GATE_DICT[node])
    # print("#### Gates that target wire 49 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 49:
    #         print(GLOBAL_GATE_DICT[node])
    # print("#### Gates that target wire 56 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 56:
    #         print(GLOBAL_GATE_DICT[node])

    # print("More information about gate 85")
    # print("     Predecessors: ", main_graph.in_edges(85))
    # print("     Successors  : ", main_graph.out_edges(85))


    # construct C_OUT
    # \omega_out = active wires of C_OUT
    omega_out = set()
    for id in gates_id:
        g = GLOBAL_GATE_DICT[id]
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

    if DEBUG:
        print("Old to new wire map: ", old_to_new_map)
        print("New to old wire map: ", new_to_old_map)

    gates = []
    for id in gates_id:
        g = GLOBAL_GATE_DICT[id]
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
    c_dash_in = find_replacement(circuit_to_replace=c_out, ell_in=ell_in, max_controls=max_controls)
    print("======C'_IN======")
    print(c_dash_in.print_circuit())
    assert nx.is_weakly_connected(skeleton_graph(circuit=c_dash_in).nx_graph())

    # C_IN with gates with only 2 control wires
    c_in = c_dash_in.break_into_2_way_gates()
    # print("======C_IN======")
    # print(c_in.print_circuit())

    # Check that C_IN is equivalent to C'_IN
    if DEBUG:
        test_circuit_decomposition(circuit1=c_dash_in)

    # map C_IN to a circuit with n wires. 
    # Assume that C'_IN has at-least 1 3 way gate. Thus, C_IN has 1 more active wire than C'_IN
    cin_gates = []
    # map the new active wire to random wire that is not in omega_out
    k_wire = random.randrange(start=0, stop=main_circuit._n)
    while k_wire in omega_out:
        k_wire = random.randrange(start=0, stop=main_circuit._n)
    new_to_old_map[c_in._n-1] = k_wire
    if DEBUG:
        print("k_wire: ", k_wire)
    for g in c_in.gates():
        GLOBAL_SERIAL += 1
        cin_gates.append(
            BaseGate(
               control_0=new_to_old_map[g.control0()],
               control_1=new_to_old_map[g.control1()],
               control_function=g.control_function(),
               target=new_to_old_map[g.target()],
               id=GLOBAL_SERIAL
            )
        )
    if DEBUG:
        print("--- C_IN gates ---")
        for g in cin_gates:
            print(g)
        print("--- ---------- ---")

    #  print(nx.is_directed_acyclic_graph(G=skeleton_graph(circuit=BaseReversibleCircuit(gates=cin_gates), n=).nx_graph()))

    ##### Re-construct the skeleton graph with C_IN and immediate predecesssors/successors of C_OUT #####

    imm_predecessors = set()
    for id in gates_id:
        dfs_with_edge_fn(source=id, visited=imm_predecessors, edges_fn=lambda node: map(lambda x: x[0], main_graph.in_edges(node)))
    imm_predecessors.difference_update(set(gates_id))
    imm_successors = set()
    for id in gates_id:
        dfs_with_edge_fn(source=id, visited=imm_successors, edges_fn=lambda node: map(lambda x: x[1], main_graph.out_edges(node)))
    imm_successors.difference_update(set(gates_id))

    if DEBUG:
        print("Immediate Pred. of C_OUT: ", imm_predecessors)
        print("Immediate Succ. of C_OUT: ", imm_successors)

    # imm_predecessors_gates = map(lambda node: main_circuit.gates_dict(node), nx.topological_sort(main_graph.subgraph(imm_predecessors)))
    # imm_successors_gates = map(lambda node: main_circuit.gates_dict(node), nx.topological_sort(main_graph.subgraph(imm_successors)))

    # The collision sets represent the dependecy chain within the C_IN. 
    cin_collision_sets = []
    for i in range(0, len(cin_gates)):
        set_i = set()
        for j in range(i+1, len(cin_gates)):
            if check_collision(gate0=cin_gates[i], gate1=cin_gates[j]):
                set_i.add(j)
        cin_collision_sets.append(set_i)
    # remove cases where there exists a node k between i and j with which both i and j collide
    for i in range(0, len(cin_gates)):
        for j in range(i+1, len(cin_gates)):
            if j in cin_collision_sets[i]:
                # remove all node with which j also collides
                inter = cin_collision_sets[i].intersection(cin_collision_sets[j])
                for v in inter:
                    cin_collision_sets[i].remove(v)


    # After resolving dependecy chain within C_IN we need to connect it with the immediate predecessors of C_OUT
    # For each immediate predecessor of C_OUT find the first gate in C_IN that it collides with in all dependency chains within C_IN. 
    # In other words (1) first find all the gates in C_IN the predecessor collides with (2) For each gate i in C_IN that collides with predecessor
    # remove the intersection of i and j where i collides with j and j > i.
    imm_predecessors_collisions = {}
    for imm_pred in imm_predecessors:
        g = GLOBAL_GATE_DICT[imm_pred]
        collides_with = set()
        for (index, c_g) in enumerate(cin_gates):
            # collision is only valid if there exist no other gate < index that collides with c_g
            if check_collision(gate0=g, gate1=c_g):
                does_smaller_index_collide = False
                for smaller_index in collides_with:
                    if index in cin_collision_sets[smaller_index]:
                        does_smaller_index_collide = True
                if does_smaller_index_collide == False:
                    collides_with.add(index)
        imm_predecessors_collisions[imm_pred] = collides_with
    if DEBUG:
        print("Imm Pred. Collisions: ", imm_predecessors_collisions)

    # Now we're left to add outgoing edges from C_IN to immediate successors of C_OUT. For each immediate successor find the last gate
    # in C_IN it collides with among all dependency chains of C_IN. In other words, starting from last gate in C_IN check whether any gate i 
    # collides with immediate predecessor. If it does, then only add an edge from i to immediate predecessor iff immediate predecessor also does
    # not collide with j, where j > i and j collides with i
    imm_successors_collisions = {}
    for imm_succ in imm_successors:
        g = GLOBAL_GATE_DICT[imm_succ]
        collides_with = set()
        for index in reversed(range(0, len(cin_gates))):
            if check_collision(gate0=g, gate1=cin_gates[index]):
                does_index_collide_with_larger_index = False
                for larger_index in collides_with:
                    if larger_index in cin_collision_sets[index]:
                        does_index_collide_with_larger_index = True
                if does_index_collide_with_larger_index == False:
                    collides_with.add(index)
        imm_successors_collisions[imm_succ] = collides_with
    if DEBUG:
        print("Imm Succ. Collisions: ", imm_successors_collisions)

    ##### Find edges to add from `outsiders` to gates in C_IN, if they collide. #####
    # Recall outsiders are set of nodes that may collide with gate in C_IN due to introduction of new wires

    # Find outsiders O
    visited_up = set()
    for id in gates_id:
        dfs_with_edge_fn(source=id, visited=visited_up, edges_fn=lambda node: map(lambda x: x[0], main_graph.in_edges(node)))

    visited_down = set()
    for id in gates_id:
        dfs_with_edge_fn(source=id, visited=visited_down, edges_fn=lambda node: map(lambda x: x[1], main_graph.out_edges(node)))

    visited = visited_up.union(visited_down)

    # Checks that outsider set is correct. That is, no node in outside_set must be neither successor not predecessor of any node in subgraph
    outside_set = set(list(main_graph.nodes())).difference(visited)
    for node in outside_set:
        for subgraph_node in gates_id:
            # Node should be neither a predecessor nor a successor
            assert nx.has_path(source=node, target=subgraph_node, G=main_graph) == False
            assert nx.has_path(source=subgraph_node, target=node, G=main_graph) == False
    if DEBUG:
        print("Outside set: ", outside_set)
    # We need to check whether any of the outsiders collide with any of the gates in C_IN. If they do then make them predeccessor or successor of the gate they collid with in C_IN. 
    # But within the outsider set I don't want to create unecessary dependencies. Let's say there are two nodes in outsider set A and B and A collides with B. Both A and B collide with new gate
    # C in C_IN. I don't want to draw a dependency from both A and B to C. Instead only B should have a dependency to C. 

    # Initially I had assumed that we can filter out outside nodes that don't touch wire k. But doing so is incorrect. 
    # Outside node can still collide with a gate in C_IN even if it does not touches the new wire k. For example, they 
    # may collide with new gate that does not touches wire k. 
    #
    # to_remove = set()
    # for node in outside_set:
    #     g = GLOBAL_GATE_DICT[node]
    #     if g.control0() != k_wire and g.control1() != k_wire and g.target() != k_wire:
    #         to_remove.add(node)
    # outside_set.difference_update(to_remove)
    # if DEBUG:
    #     print("Outside set post removal of gate that don't touch k_wire: ", outside_set)

    # filter out gates that don't collide with any gate in C_IN
    to_remove = set()
    for node in outside_set:
        gi = GLOBAL_GATE_DICT[node]
        should_be_removed = True
        for gj in cin_gates:
            if check_collision(gate0=gi, gate1=gj) == True:
                should_be_removed = False
        if should_be_removed:
            to_remove.add(gi)
    outside_set.difference_update(to_remove)
    if DEBUG:
        print("Outside set post removal of gates that don't collide with any of C_IN gates (final): ", outside_set)
    
    # Initially I had assumed that if A depends on B, then we an ignore A because B suffices to express the dependency. 
    # But doing so is incorrect. Because B may collide with a later gate in C_IN whereas A may collide with some earlier gate
    # in C_IN. 
    # remove_nodes = set()
    # remove the nodes which have succecors (or prdecessors) in the list.
    # for i in outside_set:
    #     for j in outside_set:
    #         if i != j:
    #             gi = main_circuit.gates_dict(i)
    #             gj = main_circuit.gates_dict(j)
    #             if nx.has_path(G=main_graph, source=i,  target=j):
    #                 remove_nodes.add(i)
        # for j in range(0, len(outside_set_list)):
            # if j in main_circuit.collision_sets()[i]:
                # remove_nodes.add(i)
    # outside_set.difference_update(remove_nodes)

    # if DEBUG:
    #     print("Outside set final: ", outside_set)

    ##### Update the main circuit and main graph #####

    # (1) Update the main graph by replacing C_OUT with C_IN

    # Add c_in gates to the main circuit
    add_more_gates(gates=cin_gates)

    # Remove nodes of C_OUT
    for id in gates_id:
        main_graph.remove_node(id)
        del GLOBAL_GATE_DICT[id]

    # Add nodes and edges for internal dependency withing C_IN
    to_add_edges = []
    for i in range(0, len(cin_collision_sets)):
        for j in cin_collision_sets[i]:
            to_add_edges.append((cin_gates[i].id(),cin_gates[j].id()))

    # Add edges from immediate predecessors to gates in C_IN
    for imm_pred in imm_predecessors_collisions:
        for j in imm_predecessors_collisions[imm_pred]:
            to_add_edges.append((imm_pred, cin_gates[j].id()))
    
    # Add edges from gates in C_IN to immediate successors
    for imm_succ in imm_successors_collisions:
        for j in imm_successors_collisions[imm_succ]:
            to_add_edges.append((cin_gates[j].id(), imm_succ))

    main_graph.add_edges_from(to_add_edges)

    # Check that graph is still acyclic after the update
    assert nx.is_directed_acyclic_graph(G=main_graph) == True

    # (2) C_IN may have more active wires than C_OUT. Below we add dependencies induced due to more active wires. 

    # For each node in outside_set find the first gate among all dependency chains that it collides with. That is, for
    # each i in C_IN add an edge from node in outside set iff i collides with the node and there is not gate j in C_IN
    # where j < i and collides with the node as well
    outside_collisions_dict = {}
    for node in outside_set:
        g = GLOBAL_GATE_DICT[node]
        collides_with = set()
        for (index, cg) in enumerate(cin_gates):
            if check_collision(gate0=g, gate1=cg):
                does_index_collide_with_smaller_index = False
                for smaller_index in collides_with:
                    assert smaller_index < index
                    if index in cin_collision_sets[smaller_index]:
                        does_index_collide_with_smaller_index = True
                if does_index_collide_with_smaller_index == False:
                    collides_with.add(index)
        outside_collisions_dict[node] = collides_with
    to_add_edges = []
    for node in outside_collisions_dict:
        for index in outside_collisions_dict[node]:
            to_add_edges.append((node, cin_gates[index].id()))
    if DEBUG: 
        print("Outside set edges: ", to_add_edges)
    main_graph.add_edges_from(to_add_edges)  

    # print("#### Gates that target wire 36 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 36:
    #         print(GLOBAL_GATE_DICT[node])
    # print("#### Gates that target wire 48 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 48:
    #         print(GLOBAL_GATE_DICT[node])
    # print("#### Gates that target wire 49 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 49:
    #         print(GLOBAL_GATE_DICT[node])
    # print("#### Gates that target wire 56 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 56:
    #         print(GLOBAL_GATE_DICT[node])

    # print("More information about gate 85")
    # print("     Predecessors: ", main_graph.in_edges(85))
    # print("     Successors  : ", main_graph.out_edges(85))
    # print("GATE 11 more information: ")
    # print(f"    in_edges: ", list(main_graph.in_edges(11)))
    # print(f"    out_edges: ", list(main_graph.out_edges(11)))
    # print("GATE: ", GLOBAL_GATE_DICT[6])
    # print("GATE: ", GLOBAL_GATE_DICT[7])
    # print("#### Gates that target wire 24 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 24:
    #         print(GLOBAL_GATE_DICT[node])
    # print("#### Gates that target wire 53 ####")
    # for node in main_graph.nodes():
    #     if GLOBAL_GATE_DICT[node].target() == 53:
    #         print(GLOBAL_GATE_DICT[node])

    assert nx.is_directed_acyclic_graph(G=main_graph) == True


def skeleton_graph_to_reversible_circuit(main_graph: nx.Graph, gates_dict: dict[int: BaseGate], n: int) -> BaseReversibleCircuit:
    ordered_gates = list(nx.topological_sort(G=main_graph))
    gates = []
    for g_id in ordered_gates:
        gates.append(copy.deepcopy(gates_dict[g_id]))

    return BaseReversibleCircuit(
        gates=gates,
        n=n
    )


def test_circuit_decomposition(circuit1=BaseReversibleCircuit):
    circuit2 = circuit1.break_into_2_way_gates()

    for value in range(0, 1<<5):
        input = []
        for i in range(0, 5):
            input.append(bool((value >> i)&1))
        
        output1 = copy.deepcopy(input)
        circuit1.run(input=output1)

        output2 = copy.deepcopy(input)
        output2.append(True)
        circuit2.run(input=output2)

        assert output1 == output2[:-1]
        assert output2[-1] == True

    # print(circuit_3.print_circuit())
    # print(circuit_2.print_circuit())

# test_circuit_decomposition(circuit1=_sample_random_reversible_circuit_strategy_2(n=5, gate_count=20, max_controls=3))

main_circuit = _sample_random_reversible_circuit_strategy_2(n=128, gate_count=1000, max_controls=2)
main_circuit.assign_serial_ids_to_gates()
global_vars_from_gates(gates=main_circuit._gates)
skeleton = skeleton_graph(circuit=main_circuit)
main_circuit._collision_sets = skeleton.collisions()
main_graph = skeleton.nx_graph()
assert nx.is_weakly_connected(G=main_graph) == True
print(list(nx.topological_sort(G=main_graph)))
mix_iterations = 10
for i in range(0, mix_iterations):
    print(f"######### ITERATION {i} #########")
    c_before = skeleton_graph_to_reversible_circuit(main_graph=main_graph, gates_dict=GLOBAL_GATE_DICT, n=main_circuit._n)
    # print("Topological ordering of gates (before): ", list(nx.topological_sort(G=main_graph)))
    random_ell_out = random.randrange(2, 8)
    print("\ell_OUT: ", random_ell_out)
    mixing_iteration(main_circuit=main_circuit, main_graph=main_graph, ell_in=10, ell_out=random_ell_out, max_controls=3)
    print("Topological ordering of gates (after ): ", list(nx.topological_sort(G=main_graph)))
    # Check circuit equivalence after iteration 
    c_after = skeleton_graph_to_reversible_circuit(main_graph=main_graph, gates_dict=GLOBAL_GATE_DICT, n=main_circuit._n)

    # print("##### Main Circuit #####")
    # for g in main_circuit.gates():
    #     print(g)
    # print("##### Mixed Circuit #####")
    # for g in mixed_circuit.gates():
    #     print(g)


    for i in range(0, 1000):
        random_value = random.randrange(0, 1<<main_circuit._n)
        random_input = []
        for i in range(0, main_circuit._n):
            random_input.append(bool((random_value>>i)&1))
        output1 = copy.deepcopy(random_input)
        c_before.run(input=output1)
        output2 = copy.deepcopy(random_input)
        c_after.run(input=output2)

        mismatching_indices = []
        for (index, (i0, i1)) in enumerate(zip(output1, output2)):
            if i0 != i1:
                mismatching_indices.append(index)
        
        if output1 != output2:
            print("Output mismatch indices: ", mismatching_indices)

        assert output1 == output2


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
