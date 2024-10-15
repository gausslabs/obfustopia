import random
from enum import Enum
from utils import draw_directed_graph
import networkx as nx
import copy

class GraphGate:
    def id(self) -> int:
        pass

    def control0(self) -> int:
        pass

    def control1(self) -> int:
        pass

    def target(self) -> int:
        pass

class GraphReversibleCircuit:
    def gates(self) -> list[GraphGate]:
        pass

class SkeletonGraph(): 
    def __init__(self, collisions: list[set[int]], circuit: GraphReversibleCircuit):
        self._collisions = collisions
        self._circuit = circuit
    
    def directed_edges(self) -> list[(int, int)]:
        # prepare edges
        edges = []
        for i in range(0, len(self._circuit.gates())):
            for j in self._collisions[i]:
                edges.append((i, j)) 
        
        return edges

    def collisions(self) -> list[set[int]]:
        return self._collisions
    
    def circuit(self) -> GraphReversibleCircuit:
        return self._circuit

    def nx_graph(self) -> nx.Graph:
        graph = nx.DiGraph()
        graph.add_edges_from(self.directed_edges())
        return graph
   
def check_collision(gate0: GraphGate, gate1: GraphGate) -> bool:
    return gate0.target() == gate1.control0() or gate0.target() == gate1.control1() or gate1.target() == gate0.control0() or gate1.target() == gate0.control1()

def skeleton_graph(circuit: GraphReversibleCircuit) -> SkeletonGraph:
    sets = []
    total_gates = len(circuit.gates())

    for i in range(0, total_gates):
        curr_set = set()
        for j in range(i+1, total_gates):
            if check_collision(gate0=circuit.gates()[i], gate1=circuit.gates()[j]):
                curr_set.add(circuit.gates()[j].id())
        sets.append(curr_set)
    
    # gate i finds intersection with gate j and removes the intersecting gates from its set. This is because i cannot have an edge to gate k if there exists gate j between i and k which collides with both i and k.
    for i in range(0, total_gates):
        for j in range(i+1, total_gates):
            if sets[i].__contains__(j):
                inter = sets[i].intersection(sets[j])
                # i removes intersection because i collides with j and j happen to collide with the intersection
                for v in inter:
                    sets[i].remove(v)

    collisions = {}
    for i in range(0, total_gates):
        collisions[i] = copy.deepcopy(sets[i])

    return SkeletonGraph(collisions=collisions, circuit=circuit)
