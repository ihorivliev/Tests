# brute_force_slice_cog_selfmodel.py

import itertools

# Finite universe of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# 1) Slice flags: need at least two slices
slice_flag_combos = [
    combo for combo in itertools.product([False, True], repeat=len(patterns))
    if sum(combo) >= 2
]

# 2) Observer flags: need at least one observer
observer_flag_combos = [
    combo for combo in itertools.product([False, True], repeat=len(patterns))
    if sum(combo) >= 1
]

# 3) Interpret mappings: for each (slice, pattern) assign 0 or 1
#    Total possibilities = 2^(3*3) = 512
interpret_entries = list(itertools.product([0, 1], repeat=len(patterns) * len(patterns)))

# 4) SubPattern (self-model) mappings: for each pattern p, sub_map[p] != p
#    Total possibilities = 2^3 = 8
subpattern_maps = [
    combo for combo in itertools.product(patterns, repeat=len(patterns))
    if all(combo[i] != i for i in patterns)
]

def valid_slice(slice_flags, interp_flat):
    """Check slice functionality: exists two distinct slices s1,s2 and a pattern p such that Interpret differs."""
    slices = [i for i, flag in enumerate(slice_flags) if flag]
    for s1, s2 in itertools.permutations(slices, 2):
        for p in patterns:
            if interp_flat[s1 * len(patterns) + p] != interp_flat[s2 * len(patterns) + p]:
                return True
    return False

valid_count = 0
example = None

# Combine slice, cognition, and self-modeling
for slice_flags in slice_flag_combos:
    for interp_flat in interpret_entries:
        if not valid_slice(slice_flags, interp_flat):
            continue
        for obs_flags in observer_flag_combos:
            # For each observer flagged p, ensure subpattern_map provides SelfModel(p) != p
            for sub_map in subpattern_maps:
                # All sub_map satisfy sub_map[p] != p by construction
                valid_count += 1
                if example is None:
                    example = (slice_flags, obs_flags, interp_flat, sub_map)
            # (We count all combinations; no further filtering needed)

# Output results
print(f"✅ Slice + Cognition + Self-Model models found: {valid_count}\n")

if example:
    slice_flags, obs_flags, interp_flat, sub_map = example
    print("Example model:")
    print("  IsSlice flags:   ", dict(enumerate(slice_flags)))
    print("  IsObserver flags:", dict(enumerate(obs_flags)))
    print("  SubModel map:    ", dict(enumerate(sub_map)))
    slices_list = [i for i, f in enumerate(slice_flags) if f]
    for s in slices_list[:2]:
        print(f"    Interpret({s}, p):", [interp_flat[s * len(patterns) + p] for p in patterns])

