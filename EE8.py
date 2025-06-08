# Stage 2 Brute‐Force Enumeration: Verifying R + Acyclicity
# ----------------------------------------------------------
# Axioms for Stage 2:
#   1. R: ∃ at least one directed edge (including self-loops)
#   2. Acyclicity: no self-loops, no 2-cycles (i→j and j→i)
#
# We search over all directed graphs on 2 nodes (0 and 1).

from itertools import product

nodes = [0, 1]
edges = [(i, j) for i in nodes for j in nodes]

def satisfies_stage2(adj):
    # 1. Existence: at least one edge present
    if not any(adj[e] for e in edges):
        return False
    # 2. No self-loops
    if adj[(0,0)] or adj[(1,1)]:
        return False
    # 3. No 2-cycles
    if adj[(0,1)] and adj[(1,0)]:
        return False
    return True

# Enumerate all 2^4 possible adjacency assignments
for bits in product([False, True], repeat=len(edges)):
    adj = {edge: present for edge, present in zip(edges, bits)}
    if satisfies_stage2(adj):
        print("Stage 2: Found a model satisfying R + Acyclicity:")
        # Display adjacency matrix rows [to 0, to 1]
        for i in nodes:
            print([1 if adj[(i,j)] else 0 for j in nodes])
        break

