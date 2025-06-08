# Stage 5: Strengthening Fractality to Size-2 Subgraphs
# ------------------------------------------------------
# We extend Stage 4 by requiring fractality not only for single-node patterns
# but also for every pair of nodes. That is:
#   For every size-2 subgraph P = {i, j}, there exists a disjoint pair Q = {k, l},
#   k < l, Q != P, such that the induced subgraphs on P and Q are isomorphic
#   (same edges among them).
#
# We keep the previous axioms:
#   1. R: at least one edge
#   2. Acyclicity: no directed cycles
#   3. Weak Connectivity: undirected connectedness
#   4. Fractality (size-1): every node has a twin
#   5. Fractality (size-2): new requirement
#
# Domain: 4 nodes (0–3), brute-force all directed graphs without self-loops.

from itertools import product, combinations
from collections import deque

nodes = list(range(4))
# all possible directed edges (i, j) for i != j
edges = [(i, j) for i in nodes for j in nodes if i != j]

def has_cycle(adj):
    visited = {u: 0 for u in nodes}
    def dfs(u):
        visited[u] = 1
        for v in nodes:
            if adj[u][v]:
                if visited[v] == 1 or (visited[v] == 0 and dfs(v)):
                    return True
        visited[u] = 2
        return False
    return any(visited[u] == 0 and dfs(u) for u in nodes)

def is_weakly_connected(adj):
    visited = {nodes[0]}
    queue = deque([nodes[0]])
    while queue:
        u = queue.popleft()
        for v in nodes:
            if adj[u][v] or adj[v][u]:
                if v not in visited:
                    visited.add(v)
                    queue.append(v)
    return len(visited) == len(nodes)

def twin_single(adj):
    # Single-node fractality: each node has a twin
    out_n = {u: {v for v in nodes if adj[u][v]} for u in nodes}
    in_n  = {u: {v for v in nodes if adj[v][u]} for u in nodes}
    for i in nodes:
        if not any(i != j and out_n[i]==out_n[j] and in_n[i]==in_n[j] for j in nodes):
            return False
    return True

def twin_pair(adj):
    # Size-2 fractality: each unordered pair P has a disjoint twin Q
    def induced(adj, pair):
        # returns sorted tuple of booleans for edges within the pair: (i->j, j->i)
        i, j = pair
        return (adj[i][j], adj[j][i])
    all_pairs = list(combinations(nodes, 2))
    patterns = {pair: induced(adj, pair) for pair in all_pairs}
    for P, pat in patterns.items():
        # find a Q != P, disjoint, with same pat
        if not any(Q != P and set(Q).isdisjoint(P) and patterns[Q] == pat for Q in all_pairs):
            return False
    return True

# Brute-force search
found = False
for bits in product([False, True], repeat=len(edges)):
    # build adjacency matrix
    adj = {u: {v: False for v in nodes} for u in nodes}
    for (e, val) in zip(edges, bits):
        adj[e[0]][e[1]] = val
    # 1. at least one edge
    if not any(any(row.values()) for row in adj.values()):
        continue
    # 2. acyclic
    if has_cycle(adj):
        continue
    # 3. weakly connected
    if not is_weakly_connected(adj):
        continue
    # 4. single-node fractality
    if not twin_single(adj):
        continue
    # 5. size-2 fractality
    if not twin_pair(adj):
        continue
    found = adj
    break

print("Stage 5: All axioms with size-2 fractality satisfiable?", "YES" if found else "NO")
if found:
    print("Example adjacency:")
    for u in nodes:
        print([1 if found[u][v] else 0 for v in nodes])
