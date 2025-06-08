# deterministic_stress_test.py

import itertools

def test_deterministic(n):
    """
    Deterministic strong-wall example for any n:
    - sub_map[p] = (p-1) mod n
    - K_map[p]   = p+1
    """
    patterns = list(range(n))
    sub_map = [(p-1) % n for p in patterns]
    K_map = [p+1 for p in patterns]
    # Kolmogorov bound: K[p] <= K[sub_map[p]] + 1
    kb_ok = all(K_map[p] <= K_map[sub_map[p]] + 1 for p in patterns)
    
    # Check no nontrivial bijection preserves/increases K globally
    identity = tuple(patterns)
    strong_wall = True
    for perm in itertools.permutations(patterns):
        if perm == identity:
            continue
        if all(K_map[perm[p]] <= K_map[p] for p in patterns):
            strong_wall = False
            break
    return kb_ok, strong_wall, sub_map, K_map

# Test for various n
for n in [4, 7, 9]:
    kb_ok, strong_wall, sub_map, K_map = test_deterministic(n)
    print(f"n={n:2d}: Kolmogorov bound OK? {kb_ok}, Strong wall? {strong_wall}")
    print(" sub_map sample:", sub_map[:5], "...")
    print(" K_map sample:  ", K_map[:5], "...\n")
