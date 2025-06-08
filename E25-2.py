import itertools

# Define patterns
patterns = [0, 1, 2]

# Precompute subpattern maps
subpattern_maps = [
    combo for combo in itertools.product(patterns, repeat=3)
    if all(combo[i] != i for i in patterns)
]

# Complexity and cost maps
complexity_maps = list(itertools.product([1, 2, 3], repeat=3))
cost_maps = list(itertools.product([1, 2, 3], repeat=3))

continuum_models = []
strong_wall_models = []

for sub_map in subpattern_maps:
    for K_map in complexity_maps:
        if not all(K_map[p] <= K_map[sub_map[p]] + 1 for p in patterns):
            continue
        if set(K_map) != {1, 2, 3}:
            continue
        for C_map in cost_maps:
            if all(C_map[p] >= K_map[p] for p in patterns):
                continuum_models.append((sub_map, K_map, C_map))
                
                # Strong wall: no non-trivial bijection decreasing complexity
                exists_nontrivial = False
                for perm in itertools.permutations(patterns):
                    if perm == tuple(patterns):  # skip identity
                        continue
                    if all(K_map[perm[p]] <= K_map[p] for p in patterns):
                        exists_nontrivial = True
                        break
                if not exists_nontrivial:
                    strong_wall_models.append((sub_map, K_map, C_map))

print(f"✅ Continuum models: {len(continuum_models)}")
if continuum_models:
    _, K_map, _ = continuum_models[0]
    print("Example continuum K:", {p: K_map[p] for p in patterns})

print(f"✅ Strong Wall models (no nontrivial complexity-nonincreasing bijection): {len(strong_wall_models)}")
if strong_wall_models:
    _, K_map, _ = strong_wall_models[0]
    print("Example strong wall K:", {p: K_map[p] for p in patterns})
