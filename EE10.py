# Stage 3 Brute‐Force Enumeration: Verifying R + Acyclicity + Weak Connectivity
# -----------------------------------------------------------------------------
# Axioms for Stage 3:
#   1. R: ∃ at least one directed edge (including self-loops)
#   2. Acyclicity: no self-loops, no 2-cycles (i→j and j→i)
#   3. Weak Connectivity: treating edges as undirected, the graph is connected
#
# We search over all directed graphs on 2 nodes (0 and 1).

from itertools import product

nodes = [0, 1]
edges = [(i, j) for i in nodes for j in nodes]

def is_weakly_connected(adj):
    # Undirected connectivity: nodes connected if there's any edge between them
    # For 2 nodes, connectivity holds if adj[0,1] or adj[1,0]
    return adj[(0,1)] or adj[(1,0)]

def satisfies_stage3(adj):
    # 1. Existence of at least one directed edge
    if not any(adj[e] for e in edges):
        return False
    # 2. No self-loops
    if adj[(0,0)] or adj[(1,1)]:
        return False
    # 3. No 2-cycles
    if adj[(0,1)] and adj[(1,0)]:
        return False
    # 4. Weak connectivity
    if not is_weakly_connected(adj):
        return False
    return True

# Enumerate all possible adjacency assignments
for bits in product([False, True], repeat=len(edges)):
    adj = {edge: present for edge, present in zip(edges, bits)}
    if satisfies_stage3(adj):
        print("Stage 3: Found a model satisfying R + Acyclicity + Weak Connectivity:")
        # Display adjacency matrix rows [to 0, to 1]
        for i in nodes:
            print([1 if adj[(i,j)] else 0 for j in nodes])
        break
