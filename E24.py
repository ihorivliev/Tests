from itertools import product

# Define a small finite "universe" of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# 1) SubPattern (self-model) mappings: for each pattern p, sub_map[p] != p
subpattern_maps = [
    combo for combo in product(patterns, repeat=len(patterns))
    if all(combo[i] != i for i in patterns)
]

# 2) Kolmogorov complexity assignments K(p) ∈ {1, 2, 3}
complexity_maps = list(product([1, 2, 3], repeat=len(patterns)))

# 3) Erasure cost assignments C(p) ∈ {1, 2, 3}
cost_maps = list(product([1, 2, 3], repeat=len(patterns)))

valid_models = []
for sub_map in subpattern_maps:
    for K_map in complexity_maps:
        # Check Kolmogorov bound: K(p) <= K(sub_map[p]) + 1
        if not all(K_map[p] <= K_map[sub_map[p]] + 1 for p in patterns):
            continue
        # K(p) >= 1 is inherently satisfied by domain choice
        
        for C_map in cost_maps:
            # Landauer bound: erasure cost ≥ complexity
            if all(C_map[p] >= K_map[p] for p in patterns):
                valid_models.append((sub_map, K_map, C_map))

# Report
print(f"✅ Complexity & Cost models found: {len(valid_models)}")

# Show an example model
if valid_models:
    sub_map, K_map, C_map = valid_models[0]
    print("\nExample model:")
    print("  SubPattern mapping:", {p: sub_map[p] for p in patterns})
    print("  Complexity K(p):    ", {p: K_map[p] for p in patterns})
    print("  Erasure cost C(p):  ", {p: C_map[p] for p in patterns})
