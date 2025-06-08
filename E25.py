import itertools

# Define a small finite "universe" of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# 1) SubPattern mappings: for each pattern p, sub_map[p] != p
subpattern_maps = [
    combo for combo in itertools.product(patterns, repeat=len(patterns))
    if all(combo[i] != i for i in patterns)
]

# 2) Complexity assignments K(p) ∈ {1, 2, 3}
complexity_maps = list(itertools.product([1, 2, 3], repeat=len(patterns)))

# 3) Erasure cost assignments C(p) ∈ {1, 2, 3}
cost_maps = list(itertools.product([1, 2, 3], repeat=len(patterns)))

# Containers
continuum_models = []
strong_wall_models = []

# Iterate combinations
for sub_map in subpattern_maps:
    for K_map in complexity_maps:
        # Kolmogorov bound: K(p) <= K(sub_map[p]) + 1
        if not all(K_map[p] <= K_map[sub_map[p]] + 1 for p in patterns):
            continue
        # Check continuum: K_map must use all values 1,2,3
        if set(K_map) != {1, 2, 3}:
            continue
        
        # At this point, K_map realizes full continuum
        
        # Landauer bound test for cost_maps
        for C_map in cost_maps:
            if all(C_map[p] >= K_map[p] for p in patterns):
                continuum_models.append((sub_map, K_map, C_map))
                
                # Strong Wall of Description test:
                # No bijection f: patterns->patterns with K(f(p)) <= K(p) for all p
                exists_bijection = False
                for perm in itertools.permutations(patterns):
                    # perm is a tuple f(0),f(1),f(2)
                    if all(K_map[perm[p]] <= K_map[p] for p in patterns):
                        exists_bijection = True
                        break
                if not exists_bijection:
                    strong_wall_models.append((sub_map, K_map, C_map))

# Reports
print(f"✅ Continuum models found (full complexity range): {len(continuum_models)}")
if continuum_models:
    sub_map, K_map, C_map = continuum_models[0]
    print("\nExample continuum model:")
    print("  SubPattern mapping:", {p: sub_map[p] for p in patterns})
    print("  Complexity K(p):    ", {p: K_map[p] for p in patterns})
    print("  Erasure cost C(p):  ", {p: C_map[p] for p in patterns})

print(f"\n✅ Strong Wall models (no complexity‐nonincreasing bijection): {len(strong_wall_models)}")
if strong_wall_models:
    sub_map, K_map, C_map = strong_wall_models[0]
    print("\nExample strong wall model:")
    print("  Complexity K(p):    ", {p: K_map[p] for p in patterns})
    print("  No bijection f with K(f(p))<=K(p).")
