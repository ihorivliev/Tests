# Stage 1 Brute-Force Enumeration: Verifying Axiom R
# --------------------------------------------------
# Axiom R: ∃ a, b such that R(a, b) holds.
# We search over all directed graphs on 2 nodes (0 and 1), 
# including possible self-loops, and report the first model 
# with at least one directed edge.

from itertools import product

# Domain: nodes 0 and 1
nodes = [0, 1]
# All possible directed edges (including self-loops)
edges = [(i, j) for i in nodes for j in nodes]

# Enumerate all possible adjacency assignments (2^(4) = 16 possibilities)
for bits in product([False, True], repeat=len(edges)):
    # Build adjacency mapping
    adj = {edge: present for edge, present in zip(edges, bits)}
    # Check Axiom R: at least one directed relation exists
    if any(adj.values()):
        print("Stage 1: Axiom R satisfied by the following graph:")
        # Display adjacency matrix
        matrix = [[1 if adj[(i, j)] else 0 for j in nodes] for i in nodes]
        for row in matrix:
            print(row)
        break

