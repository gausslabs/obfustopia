import random
import networkx as nx
import matplotlib.pyplot as plt
from enum import Enum

N_DEFAULT = 12

class ControlFunction(Enum):
    AND = 1
    OR = 2

class Gate:
    def __init__(self, target: int, input0: int, input1: int, control_function: ControlFunction=ControlFunction.AND, n: int = N_DEFAULT):
        self.id = None
        self.target = target
        self.input0 = input0
        self.input1 = input1
        self.n = n
        self.control_function = control_function
        pass

class ReversibleCircuit:
    def __init__(self, gates: [Gate]):
        self.gates = gates

        # Assign ids to gates
        for i in range(0, len(self.gates)):
            self.gates[i].id = i

def check_collision(gate0: Gate, gate1: Gate) -> bool:
    assert gate0.n == gate1.n
    return gate0.target == gate1.input0 or gate0.target == gate1.input1 or gate1.target == gate0.input0 or gate1.target == gate0.input1

def draw_directed_graph(edges: [list]):
    G = nx.DiGraph()

    # Add nodes and directed edges
    G.add_edges_from(edges)

    # Draw the graph
    pos = nx.spring_layout(G)  # Position nodes using Fruchterman-Reingold force-directed algorithm
    nx.draw(G, pos, with_labels=True, node_color='lightblue', node_size=200, font_size=5, font_color='black', arrowstyle='->', arrowsize=10)

    plt.title("Directed Graph")
    plt.show()

def skeleton_graph(circuit: ReversibleCircuit):
    sets = []
    for i in range(0, len(circuit.gates)):
        curr_set = set()
        for j in range(i+1, len(circuit.gates)):
            if check_collision(gate0=circuit.gates[i], gate1=circuit.gates[j]):
                curr_set.add(circuit.gates[j].id)
        sets.append(curr_set)
    
    # gate i finds intersection with gate j and removes the intersecting gates from its set. This is because i cannot have an edge to gate k if there exists gate j between i and k which collides with both i and k.
    for i in range(0, len(circuit.gates)):
        for j in range(i+1, len(circuit.gates)):
            inter = sets[i].intersection(sets[j])
            # i removes intersection because i collides with j and j happen to collide with the intersection
            for v in inter:
                sets[i].remove(v)

    # prepare edges
    edges = []
    for i in range(0, len(circuit.gates)):
        for j in sets[i]:
            edges.append((i, j)) 
        
    return edges


def random_reversible_circuit(gate_count: int, n: int = N_DEFAULT) -> ReversibleCircuit:
    gates = []
    for i in range(0, gate_count):
        target = random.randint(0, n)
        input0 = random.randint(0, n)
        while input0 == target:
            input0 = random.randint(0, n)
        input1 = random.randint(0, n)
        while input1 == target or input1 == input0:
            input1 = random.randint(0, n)
        gates.append(Gate(target=target, input0=input0, input1=input1, n=n))

    return ReversibleCircuit(gates=gates)

# circuit0 = ReversibleCircuit(gates=[
#     Gate(11, 3, 2),
#     Gate(4, 1, 6),
#     Gate(3, 2, 1),
#     Gate(7, 4, 5),
#     Gate(4, 3, 2),
#     Gate(5,3, 7),
#     Gate(6, 9, 1),
# ])

circuit0 = random_reversible_circuit(gate_count=100, n=1000)

draw_directed_graph(edges=skeleton_graph(circuit=circuit0))
