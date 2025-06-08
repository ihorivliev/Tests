# Stage 6: Automorphism and Reading-Path Tests on the Stage-4 Model
# -------------------------------------------------------------------
# We use the example adjacency from Stage 4:
#   4-node directed graph with edges: 2->0, 2->1, 3->0, 3->1
#
# Tests:
# 1. Detect non-trivial graph automorphisms (map-territory failure).
# 2. Find a topological ordering (reading-path), demonstrating trivial 'emergent time'.

import itertools

# Define the adjacency matrix from Stage 4
nodes = [0, 1, 2, 3]
adj = {
    0: {0: False, 1: False, 2: False, 3: False},
    1: {0: False, 1: False, 2: False, 3: False},
    2: {0: True,  1: True,  2: False, 3: False},
    3: {0: True,  1: True,  2: False, 3: False},
}

# 1. Automorphism Detection
def is_automorphism(perm):
    # perm: tuple of image of each node, i.e. perm[i] is image of i
    for u, v in itertools.product(nodes, repeat=2):
        if adj[u][v] != adj[perm[u]][perm[v]]:
            return False
    return True

# Find all automorphisms
autos = []
for perm in itertools.permutations(nodes):
    if is_automorphism(perm):
        autos.append(perm)

print("Automorphisms found (as tuples mapping i->perm[i]):")
for perm in autos:
    print(perm)

# Identify non-trivial automorphisms (perm != identity)
non_trivial = [perm for perm in autos if perm != tuple(nodes)]
print("\nNon-trivial automorphisms:")
for perm in non_trivial:
    print(perm)

# 2. Topological Ordering (Reading-Path)
# For a DAG, perform a simple Kahn's algorithm to find one topological sort.
in_degree = {u: 0 for u in nodes}
for u, v in itertools.product(nodes, repeat=2):
    if adj[u][v]:
        in_degree[v] += 1

# Kahn's algorithm
order = []
queue = [u for u in nodes if in_degree[u] == 0]
while queue:
    u = queue.pop(0)
    order.append(u)
    for v in nodes:
        if adj[u][v]:
            in_degree[v] -= 1
            if in_degree[v] == 0:
                queue.append(v)

print("\nOne topological ordering (reading-path):", order)
