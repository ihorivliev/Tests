# brute_force_slice_cognition.py

import itertools

# Define a small finite "universe" of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# 1) Slice flags: at least two slices
slice_flag_combos = [
    combo for combo in itertools.product([False, True], repeat=len(patterns))
    if sum(combo) >= 2
]

# 2) Observer flags: at least one observer
observer_flag_combos = [
    combo for combo in itertools.product([False, True], repeat=len(patterns))
    if sum(combo) >= 1
]

# 3) Interpret maps: for each (slice, pattern) pair, assign 0 or 1
#    Total 2^(3*3) = 512 possible maps
interpret_entries = list(itertools.product([0, 1], repeat=len(patterns)*len(patterns)))

def valid_slice(slice_flags, interp_flat):
    """
    Check: exists two distinct slices s1,s2 and a pattern p
           such that interp[s1,p] != interp[s2,p].
    interp_flat is a flat tuple of length 9, index = s*3 + p.
    """
    slices = [i for i, is_slice in enumerate(slice_flags) if is_slice]
    for s1, s2 in itertools.permutations(slices, 2):
        for p in patterns:
            if interp_flat[s1 * len(patterns) + p] != interp_flat[s2 * len(patterns) + p]:
                return True
    return False

valid_count = 0
example = None

# Combine slice functionality and cognition (Perceive = Interpret)
for slice_flags in slice_flag_combos:
    for interp_flat in interpret_entries:
        if not valid_slice(slice_flags, interp_flat):
            continue
        for obs_flags in observer_flag_combos:
            # Cognition holds by setting Perceive = interp. No further check needed.
            valid_count += 1
            if example is None:
                # Record the first valid model
                example = (slice_flags, obs_flags, interp_flat)

print(f"✅ Slice + Cognition models found: {valid_count}\n")
if example:
    slice_flags, obs_flags, interp_flat = example
    print("Example model:")
    print("  IsSlice flags:   ", dict(enumerate(slice_flags)))
    print("  IsObserver flags:", dict(enumerate(obs_flags)))
    # Show Interpret values for the first two slices in the example
    slices_list = [i for i, f in enumerate(slice_flags) if f]
    for s in slices_list:
        print(f"    Interpret({s}, p):",
              [interp_flat[s * len(patterns) + p] for p in patterns])
