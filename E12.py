# brute_force_temporal_ordering.py

import itertools

# Define a small finite "universe" of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# Generate all possible Step functions: mapping each pattern to one of the patterns
step_functions = list(itertools.product(patterns, repeat=len(patterns)))

# Generate all possible MaxSteps assignments: for each pattern, choose a bound in {1,2,3}
max_steps_assignments = list(itertools.product([1, 2, 3], repeat=len(patterns)))

def build_path(start, step_map, N):
    """
    Given a start node, deterministic step_map (tuple), and length N,
    return the path of N+1 positions: [p0, p1, ..., pN].
    """
    path = [start]
    for _ in range(N):
        path.append(step_map[path[-1]])
    return path

# Filter models that satisfy:
# 1) No cycle at the maximum bound (already ensured by previous script if desired).
# 2) Unique positions on the reading path for each pattern.
valid_models = []

for step_map in step_functions:
    for max_steps in max_steps_assignments:
        # Check 1: no cycle at bound
        cycle_ok = True
        for p in patterns:
            path = build_path(p, step_map, max_steps[p])
            if path[-1] == p:
                cycle_ok = False
                break
        if not cycle_ok:
            continue

        # Check 2: uniqueness of positions for each pattern's path
        unique_ok = True
        for p in patterns:
            N = max_steps[p]
            path = build_path(p, step_map, N)
            if len(path) != len(set(path)):
                unique_ok = False
                break
        if unique_ok:
            valid_models.append((step_map, max_steps))

# Report results
print(f"Total models with strict temporal ordering: {len(valid_models)}\n")

for idx, (step_map, max_steps) in enumerate(valid_models, start=1):
    print(f"Model {idx}:")
    print("  Step mapping:   ", {i: step_map[i] for i in patterns})
    print("  MaxSteps mapping:", {i: max_steps[i] for i in patterns})
    print()
