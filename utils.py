import random
import networkx as nx
import matplotlib.pyplot as plt

def sample_wire(n: int, not_in: [list]) -> int: 
    assert len(not_in) < n

    wire = random.randrange(0, n)
    while wire in not_in:
        wire = random.randrange(0, n)
    return wire

def draw_directed_graph(edges: [list]):
    G = nx.DiGraph()

    # Add nodes and directed edges
    G.add_edges_from(edges)

    # Draw the graph
    pos = nx.spring_layout(G)  # Position nodes using Fruchterman-Reingold force-directed algorithm
    nx.draw(G, pos, with_labels=True, node_color='lightblue', node_size=200, font_size=5, font_color='black', arrowstyle='->', arrowsize=10)

    plt.title("Directed Graph")
    plt.show()
