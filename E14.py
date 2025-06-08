# brute_force_slice_functionality.py

import itertools

# Small universe of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# All possible Slice flags: each pattern may or may not be a Slice
# Represent as dict: pattern -> bool
slice_flag_combos = list(itertools.product([False, True], repeat=len(patterns)))

# All possible Interpret mappings: for each (slice_pattern, target_pattern) pair, assign output 0 or 1
# First, define all functions as dict of ((s, p) -> 0/1)
interpret_entries = list(itertools.product([0, 1], repeat=len(patterns)*len(patterns)))
# Helper to convert a flat tuple to nested dict
def make_interpret_map(flat):
    interp = {}
    idx = 0
    for s in patterns:
        for p in patterns:
            interp[(s, p)] = flat[idx]
            idx += 1
    return interp

valid_count = 0
example = None

for flags in slice_flag_combos:
    slice_flags = {i: flags[i] for i in patterns}
    # Need at least two distinct slices
    slices = [i for i in patterns if slice_flags[i]]
    if len(slices) < 2:
        continue

    for flat_map in interpret_entries:
        interp_map = make_interpret_map(flat_map)
        
        # Check property: exists two distinct slices s1, s2 and a pattern p
        # such that interp[s1,p] != interp[s2,p]
        found = False
        for s1, s2 in itertools.permutations(slices, 2):
            for p in patterns:
                if interp_map[(s1, p)] != interp_map[(s2, p)]:
                    found = True
                    break
            if found:
                break
        
        if found:
            valid_count += 1
            if example is None:
                example = (slice_flags, interp_map)
            # break  # comment out to count all models

print(f"✅ Slice functionality models found: {valid_count}")
if example:
    slice_flags, interp_map = example
    print("\nExample model:")
    print("  IsSlice flags:", slice_flags)
    # Print interpret outputs for this example
    for s in patterns:
        if slice_flags[s]:
            print(f"    Interpret({s}, p):", [interp_map[(s, p)] for p in patterns])
