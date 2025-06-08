# brute_force_time.py
import itertools
import sys

# Define a small finite "universe" of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# Generate all possible Step functions: mapping each pattern to one of the patterns
# There are 3^3 = 27 such functions
step_functions = list(itertools.product(patterns, repeat=len(patterns)))

# Generate all possible MaxSteps assignments: for each pattern, choose a bound in {1,2,3}
# There are 3^3 = 27 such assignments
max_steps_assignments = list(itertools.product([1, 2, 3], repeat=len(patterns)))

def compute_reachable(step_map, start, max_n):
    """
    Given a step_map (tuple of length 3) and start node,
    compute reachable nodes at each depth up to max_n.
    Returns a dict: depth -> set of reachable nodes.
    """
    reachable = {0: {start}}
    for n in range(1, max_n + 1):
        prev = reachable[n - 1]
        curr = set()
        for node in prev:
            curr.add(step_map[node])
        reachable[n] = curr
    return reachable

# Try all combinations
for step_map in step_functions:
    for max_steps in max_steps_assignments:
        valid = True
        # Check no-cycle axiom: for each pattern i,
        # the reachable set at depth max_steps[i] must NOT contain i
        for i in patterns:
            reachable = compute_reachable(step_map, i, max_steps[i])
            if i in reachable[max_steps[i]]:
                valid = False
                break
        if valid:
            print("✅ Found a model satisfying the Reading-Path axioms!")
            print("Step mapping:", {i: step_map[i] for i in patterns})
            print("MaxSteps mapping:", {i: max_steps[i] for i in patterns})
            sys.exit(0)


print("❌ No model found (unexpected).")
