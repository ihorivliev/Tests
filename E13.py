import itertools

# Define a small finite "universe" of 3 patterns: 0, 1, 2
patterns = [0, 1, 2]

# Helper: all mappings from patterns to values in domain
def all_maps(domain, patterns):
    return list(itertools.product(domain, repeat=len(patterns)))

# 1. Structure and Feeling in {0,1}
structure_maps = all_maps([0, 1], patterns)
feeling_maps   = all_maps([0, 1], patterns)

# 2. Combinatorics: for each p, exists q != p with same structure
def check_combinatorics(struct_map):
    for i, si in enumerate(struct_map):
        if not any(j != i and struct_map[j] == si for j in range(len(patterns))):
            return False
    return True

# 3. Describe: describe_map[p] != p
describe_maps = []
for prod in itertools.product(patterns, repeat=len(patterns)):
    if all(prod[i] != i for i in patterns):
        describe_maps.append(prod)

# 4. FindSubPattern: sub_map[p] != p
subpattern_maps = describe_maps  # same constraint: != itself

# Count satisfying models
count = 0
example = None
for struct in structure_maps:
    # universal principle: if struct[i]==struct[j], then feeling[i]==feeling[j]
    for feel in feeling_maps:
        valid = True
        for i in patterns:
            for j in patterns:
                if struct[i] == struct[j] and feel[i] != feel[j]:
                    valid = False
                    break
            if not valid:
                break
        if not valid:
            continue

        # combinatorics
        if not check_combinatorics(struct):
            continue

        # describe & subpattern
        for desc in describe_maps:
            for sub in subpattern_maps:
                # no further constraints between desc and sub
                count += 1
                if example is None:
                    example = (struct, feel, desc, sub)

print(f"✅ Integrated axioms models found: {count}")
if example:
    struct, feel, desc, sub = example
    print("\nExample model:")
    print("  Structure:", dict(enumerate(struct)))
    print("  Feeling:  ", dict(enumerate(feel)))
    print("  Describe: ", dict(enumerate(desc)))
    print("  SubPattern:", dict(enumerate(sub)))
