import itertools

patterns = [0, 1, 2]

# 1) All SubPattern mappings (p → sub[p] ≠ p)
subpattern_maps = [
    combo for combo in itertools.product(patterns, repeat=3)
    if all(combo[i] != i for i in patterns)
]

# 2) Complexity K ∈ {1,2,3}^3
complexity_maps = list(itertools.product([1, 2, 3], repeat=3))

continuum_models = []
strong_wall_models = []

for sub_map in subpattern_maps:
    for K_map in complexity_maps:
        # K(p) ≤ K(sub_map[p]) + 1
        if not all(K_map[p] <= K_map[sub_map[p]] + 1 for p in patterns):
            continue
        # full continuum spans {1,2,3}
        if set(K_map) != {1, 2, 3}:
            continue
        continuum_models.append((sub_map, K_map))
        
        # check nontrivial bijections
        has_nontrivial = False
        for perm in itertools.permutations(patterns):
            if perm == tuple(patterns):
                continue  # skip identity
            if all(K_map[perm[p]] <= K_map[p] for p in patterns):
                has_nontrivial = True
                break
        if not has_nontrivial:
            strong_wall_models.append((sub_map, K_map))

print(f"✅ Continuum models: {len(continuum_models)}")
print(f"✅ Strong Wall models: {len(strong_wall_models)}")
