import itertools

# Define a small finite "universe" of 4 patterns: 0, 1, 2, 3
patterns = [0, 1, 2, 3]

# 1) SubPattern mappings: for each pattern p, sub_map[p] != p
subpattern_maps = [
    combo for combo in itertools.product(patterns, repeat=len(patterns))
    if all(combo[i] != i for i in patterns)
]

# 2) Complexity assignments K(p) ∈ {1, 2, 3, 4}
complexity_maps = list(itertools.product([1, 2, 3, 4], repeat=len(patterns)))

continuum_models = []
strong_wall_models = []

# Precompute all non-identity permutations
perms = [perm for perm in itertools.permutations(patterns) if perm != tuple(patterns)]

for sub_map in subpattern_maps:
    for K_map in complexity_maps:
        # Kolmogorov bound: K(p) <= K(sub_map[p]) + 1
        if not all(K_map[p] <= K_map[sub_map[p]] + 1 for p in patterns):
            continue
        # Continuum: K_map must use all values 1,2,3,4
        if set(K_map) != {1, 2, 3, 4}:
            continue
        # Found continuum model
        continuum_models.append((sub_map, K_map))
        
        # Check no nontrivial bijection decreasing complexity
        has_nontrivial = False
        for perm in perms:
            if all(K_map[perm[p]] <= K_map[p] for p in patterns):
                has_nontrivial = True
                break
        if not has_nontrivial:
            strong_wall_models.append((sub_map, K_map))

# Report
print(f"✅ Continuum models (4-pattern, K ∈ {{1,2,3,4}}): {len(continuum_models)}")
if continuum_models:
    _, K_map = continuum_models[0]
    print("Example continuum K:", {p: K_map[p] for p in patterns})

print(f"✅ Strong Wall models (no nontrivial complexity-nonincreasing bijection): {len(strong_wall_models)}")
if strong_wall_models:
    _, K_map = strong_wall_models[0]
    print("Example strong wall K:", {p: K_map[p] for p in patterns})
