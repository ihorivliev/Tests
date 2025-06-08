# Stage 4: Testing Fractality with R + Acyclicity + Weak Connectivity
# ---------------------------------------------------------------------
# Domain: 4 nodes (0-3)
# Conditions to satisfy:
#   1. R: at least one directed edge exists.
#   2. Acyclic: no directed cycles.
#   3. Weak connectivity: the undirected version of the graph is connected.
#   4. Fractality (for size=1 patterns): For every node i, there exists j != i
#      such that i and j have identical sets of incoming and outgoing neighbors.
#
# We brute-force all directed graphs without self-loops on 4 nodes.

from itertools import product
from collections import deque

nodes = list(range(4))
# all possible directed edges (i, j) for i != j
edges = [(i, j) for i in nodes for j in nodes if i != j]

def has_cycle(adj):
    """Detect any directed cycle using DFS."""
    visited = {u: 0 for u in nodes}  # 0=unvisited,1=visiting,2=visited
    def dfs(u):
        visited[u] = 1
        for v in nodes:
            if adj[u][v]:
                if visited[v] == 1:
                    return True
                if visited[v] == 0 and dfs(v):
                    return True
        visited[u] = 2
        return False
    return any(visited[u] == 0 and dfs(u) for u in nodes)

def is_weakly_connected(adj):
    """Check if the underlying undirected graph is connected."""
    visited = set([nodes[0]])
    queue = deque([nodes[0]])
    while queue:
        u = queue.popleft()
        for v in nodes:
            if adj[u][v] or adj[v][u]:
                if v not in visited:
                    visited.add(v)
                    queue.append(v)
    return len(visited) == len(nodes)

def check_fractality(adj):
    """Check if every node has a 'twin' with identical neighbor sets."""
    # Precompute in/out neighbor sets
    out_neighbors = {u: {v for v in nodes if adj[u][v]} for u in nodes}
    in_neighbors  = {u: {v for v in nodes if adj[v][u]} for u in nodes}
    for i in nodes:
        found_twin = False
        for j in nodes:
            if i != j:
                if out_neighbors[i] == out_neighbors[j] and in_neighbors[i] == in_neighbors[j]:
                    found_twin = True
                    break
        if not found_twin:
            return False
    return True

# Brute-force search
example = None
for bits in product([False, True], repeat=len(edges)):
    # Build adjacency matrix
    adj = {u: {v: False for v in nodes} for u in nodes}
    for (edge, present) in zip(edges, bits):
        adj[edge[0]][edge[1]] = present
    # Condition 1: at least one edge
    if not any(any(row.values()) for row in adj.values()):
        continue
    # Condition 2: acyclic
    if has_cycle(adj):
        continue
    # Condition 3: weak connectivity
    if not is_weakly_connected(adj):
        continue
    # Condition 4: fractality for single-node patterns
    if not check_fractality(adj):
        continue
    example = adj
    break

print("Stage 4: R + Acyclicity + Weak Connectivity + Fractality model found?",
      "YES" if example else "NO")
if example:
    print("Example adjacency:")
    for u in nodes:
        print([1 if example[u][v] else 0 for v in nodes])
