import random
import networkx as nx
import matplotlib.pyplot as plt
from networkx.algorithms.community import greedy_modularity_communities


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

    print(G.edges())
    print(list(nx.topological_sort(G=G)))


    # Draw the graph
    pos = nx.spring_layout(G,k=0.15, iterations=20)  # Position nodes using Fruchterman-Reingold force-directed algorithm
    nx.draw(G, pos, with_labels=True, node_color='lightblue', node_size=50, font_size=5, font_color='black', arrowstyle='->', arrowsize=10)

    plt.title("Directed Graph")
    plt.show()

def export_gephi(edges: [list]):
    G = nx.DiGraph()

    # Add nodes and directed edges
    G.add_edges_from(edges)
    nx.write_gexf(G, "mygraph.gexf")

def run_community_detection(edges: [list]):
    G = nx.DiGraph()
    G.add_edges_from(edges)
    # Add nodes and edges to your graph
    communities = greedy_modularity_communities(G, resolution=11)  # Identifying communities

    # Extract a specific community as a subgraph
    for (index, community) in enumerate(communities):
        subgraph = G.subgraph(community)  # Extracting a convex-like subgraph
        nx.write_gexf(subgraph, f"subgrap-com{index}.gexf") 