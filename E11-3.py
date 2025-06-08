# analyze_models.py

import itertools
from collections import Counter

# Define a small finite "universe" of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# Generate all possible Step functions: mapping each pattern to one of the patterns
step_functions = list(itertools.product(patterns, repeat=len(patterns)))

# Generate all possible MaxSteps assignments: for each pattern, choose a bound in {1,2,3}
max_steps_assignments = list(itertools.product([1, 2, 3], repeat=len(patterns)))

def compute_reachable(step_map, start, max_n):
    reachable = {0: {start}}
    for n in range(1, max_n + 1):
        reachable[n] = {step_map[node] for node in reachable[n - 1]}
    return reachable

# Collect all satisfying models
models = []
for step_map in step_functions:
    for max_steps in max_steps_assignments:
        valid = True
        for i in patterns:
            reachable = compute_reachable(step_map, i, max_steps[i])
            if i in reachable[max_steps[i]]:
                valid = False
                break
        if valid:
            models.append((step_map, max_steps))

# Summary statistics
print(f"Total models found: {len(models)}")

# Frequency of each distinct step mapping
step_counts = Counter(step_map for step_map, _ in models)
print("\nStep mapping frequencies:")
for step_map, count in step_counts.items():
    print(f"  {dict(enumerate(step_map))}: {count} models")

# For each step mapping, list all its max_steps assignments
print("\nModels grouped by Step mapping:")
for step_map, count in step_counts.items():
    print(f"\nStep mapping: {dict(enumerate(step_map))} ({count} models)")
    assignments = [max_steps for sm, max_steps in models if sm == step_map]
    for max_steps in assignments:
        print("  MaxSteps:", dict(enumerate(max_steps)))
