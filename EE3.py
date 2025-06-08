# Stage 3 Brute‐Force: R + Acyclicity + Strong Connectivity
# ------------------------------------------------------------
# This script exhaustively searches all directed graphs on 3 nodes
# to check whether any graph simultaneously satisfies:
#   1. ∃ at least one edge R(a,b)
#   2. Acyclic (no directed cycles)
#   3. Strongly connected (every node reaches every node)
#
# We expect no such graph exists (unsatisfiable).

from itertools import product

# Domain: nodes 0,1,2
nodes = [0, 1, 2]

def has_cycle(adj):
    """Return True if directed graph has any cycle."""
    visited = [0]*3  # 0=unvisited,1=visiting,2=visited
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
    for u in nodes:
        if visited[u] == 0 and dfs(u):
            return True
    return False

def is_strongly_connected(adj):
    """Return True if graph is strongly connected."""
    def reachable(u, v):
        stack = [u]
        seen = {u}
        while stack:
            x = stack.pop()
            for w in nodes:
                if adj[x][w] and w not in seen:
                    seen.add(w)
                    stack.append(w)
        return v in seen
    for u in nodes:
        for v in nodes:
            if not reachable(u, v):
                return False
    return True

models = []
# Enumerate all 3x3 adjacency matrices (2^9 possibilities)
for bits in product([0,1], repeat=9):
    # Build adjacency matrix
    adj = [[False]*3 for _ in nodes]
    it = iter(bits)
    for i in nodes:
        for j in nodes:
            adj[i][j] = bool(next(it))
    # 1. Must have at least one edge
    if not any(any(row) for row in adj):
        continue
    # 2. Must be acyclic
    if has_cycle(adj):
        continue
    # 3. Must be strongly connected
    if is_strongly_connected(adj):
        models.append(adj)

print("Stage 3: Acyclic + Strong Connectivity models found?", "YES" if models else "NO")
if models:
    print("Example model adjacency matrix:")
    for row in models[0]:
        print(row)
