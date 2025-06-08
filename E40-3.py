# No‐Mercy Brute‐Force Stress‐Test for the 'Existe' Framework
# -----------------------------------------------------------
# Domain: Three patterns {0,1,2}
# Axioms (apply to all ordered pairs):
#   1. Structural Subordination:
#      If IsPartOf(i,j) and i != j, then K[i] < K[j]
#   2. Temporal Linearity:
#      If Step(i) == Step(j), then i == j

from itertools import product

# Domain definitions
patterns = [0, 1, 2]
K_values = [0, 1, 2]  # Possible K-complexity values
bools = [False, True]

# Check if a given assignment satisfies both axioms
def satisfies_axioms(K, part_of, step):
    # Structural Subordination for all pairs
    for i, j in product(patterns, repeat=2):
        if part_of[(i, j)] and i != j and not (K[i] < K[j]):
            return False
    # Temporal Linearity for all pairs
    for i, j in product(patterns, repeat=2):
        if step[i] == step[j] and i != j:
            return False
    return True

# Test A: Find any model satisfying the axioms
model_found = False
for K_assign in product(K_values, repeat=len(patterns)):
    K_dict = dict(zip(patterns, K_assign))
    # Enumerate all 'IsPartOf' relations
    for part_assign in product(bools, repeat=len(patterns)**2):
        part_of = { (i, j): part_assign[i*len(patterns) + j] for i in patterns for j in patterns }
        # Enumerate all 'Step' functions
        for step_assign in product(patterns, repeat=len(patterns)):
            step = dict(zip(patterns, step_assign))
            if satisfies_axioms(K_dict, part_of, step):
                print("Test A: Axioms satisfiable → YES")
                print("  Example model:")
                print("    K =", K_dict)
                print("    IsPartOf =", {k: v for k, v in part_of.items() if v})
                print("    Step =", step)
                model_found = True
                break
        if model_found:
            break
    if model_found:
        break
if not model_found:
    print("Test A: Axioms satisfiable → NO")

print("\nTest B: Is a 2‐cycle in IsPartOf possible?")
cycle_ok = False
for K_assign in product(K_values, repeat=len(patterns)):
    K_dict = dict(zip(patterns, K_assign))
    # Force a 2-cycle between 0 and 1
    part_of = {(i, j): False for i in patterns for j in patterns}
    part_of[(0,1)] = True
    part_of[(1,0)] = True
    for step_assign in product(patterns, repeat=len(patterns)):
        step = dict(zip(patterns, step_assign))
        if satisfies_axioms(K_dict, part_of, step):
            cycle_ok = True
            break
    if cycle_ok:
        break
print("  2‐cycle allowed under axioms?" , "YES → theory fails!" if cycle_ok else "NO → cycles excluded")

print("\nTest C: Is temporal merging possible?")
merge_ok = False
for K_assign in product(K_values, repeat=len(patterns)):
    K_dict = dict(zip(patterns, K_assign))
    part_of = {(i, j): False for i in patterns for j in patterns}
    # Force time merge: Step(0)=Step(1)=0
    step = {0: 0, 1: 0, 2: 2}
    if satisfies_axioms(K_dict, part_of, step):
        merge_ok = True
        break
print("  Temporal merging allowed?" , "YES → paradox!" if merge_ok else "NO → merging excluded")
