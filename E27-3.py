# deterministic_strong_wall_example.py

def deterministic_example(n):
    """
    Constructs:
    - sub_map[p] = (p+1) % n
    - K_map[p] = ((p+1) % n) + 1  # values 1..n
    Checks:
    - Kolmogorov bound: K[p] <= K[sub_map[p]] + 1
    - Strong wall: no non-identity bijection f with K[f[p]] <= K[p] for all p
    """
    patterns = list(range(n))
    sub_map = [(p+1) % n for p in patterns]
    K_map = [((p+1) % n) + 1 for p in patterns]
    
    # Check Kolmogorov bound
    kb_ok = all(K_map[p] <= K_map[sub_map[p]] + 1 for p in patterns)
    
    # Check strong-wall: test all permutations
    import itertools
    identity = tuple(patterns)
    strong_wall = True
    for perm in itertools.permutations(patterns):
        if perm == identity:
            continue
        # check if this bijection is complexity-nonincreasing
        if all(K_map[perm[p]] <= K_map[p] for p in patterns):
            strong_wall = False
            break
    
    return kb_ok, strong_wall, sub_map, K_map

# Demonstrate for n = 3, 6, 9
for n in [3, 6, 9]:
    kb_ok, strong_wall, sub_map, K_map = deterministic_example(n)
    print(f"n={n}: Kolmogorov bound OK? {kb_ok}, Strong-wall? {strong_wall}")
    print("  sub_map sample:", sub_map[:5], "...")
    print("  K_map sample:  ", K_map[:5], "...\n")
