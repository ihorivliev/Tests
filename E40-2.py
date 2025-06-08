# No‐Mercy Brute‐Force Stress‐Test for the 'Existe' Framework
# -----------------------------------------------------------
# Applies the two axioms from the (fabricated) report:
#   1. Structural Subordination: (IsPartOf(p,w) ∧ p≠w) → K(p) < K(w)
#   2. Temporal Linearity: (Step(p1)==Step(p2)) → p1 == p2
# Then explores consistency, cycle‐freedom, and time‐merging in a tiny universe {0,1}.

from itertools import product

# Domain
patterns = [0, 1]
K_vals = [0, 1]  # possible K(p) values
bools = [False, True]

# Helper to evaluate the two axioms at given assignment
def check_axioms(K, part, step):
    # Axiom 1 for (0,1) and (1,0)
    ax1_01 = (not part[(0,1)]) or (K[0] < K[1])
    ax1_10 = (not part[(1,0)]) or (K[1] < K[0])
    # Axiom 2: (Step(0)==Step(1)) -> 0==1 (false), so must have Step(0)!=Step(1)
    ax2    = (step[0] != step[1])
    return ax1_01 and ax1_10 and ax2

# Test A: Find any model satisfying both axioms
model_A = None
for K0, K1 in product(K_vals, repeat=2):
    for p01, p10 in product(bools, repeat=2):
        for s0, s1 in product(patterns, repeat=2):
            K_assign = {0: K0, 1: K1}
            part_assign = {(0,1): p01, (1,0): p10}
            step_assign = {0: s0, 1: s1}
            if check_axioms(K_assign, part_assign, step_assign):
                model_A = (K_assign, part_assign, step_assign)
                break
        if model_A: break
    if model_A: break

print("Test A: Axioms alone satisfiable? →", "YES" if model_A else "NO")
if model_A:
    K_assign, part_assign, step_assign = model_A
    print("  Example assignment:")
    print("    K =", K_assign)
    print("    IsPartOf(0,1) =", part_assign[(0,1)], "IsPartOf(1,0) =", part_assign[(1,0)])
    print("    Step(0) =", step_assign[0], "Step(1) =", step_assign[1])
print()

# Test B: Can we force a 2‐cycle in IsPartOf under the axioms?
cycle_exists = False
for K0, K1 in product(K_vals, repeat=2):
    for s0, s1 in product(patterns, repeat=2):
        K_assign = {0: K0, 1: K1}
        part_assign = {(0,1): True, (1,0): True}
        step_assign = {0: s0, 1: s1}
        if check_axioms(K_assign, part_assign, step_assign):
            cycle_exists = True
            break
    if cycle_exists: break

print("Test B: 2‐cycle allowed under axioms? →", "YES (theory fails!)" if cycle_exists else "NO (cycles excluded)")
print()

# Test C: Can time merge (Step(0)==Step(1) with 0!=1)?
merge_exists = False
for K0, K1 in product(K_vals, repeat=2):
    for p01, p10 in product(bools, repeat=2):
        for s in patterns:
            # enforce Step(0)==Step(1)==s
            step_assign = {0: s, 1: s}
            K_assign = {0: K0, 1:K1}
            part_assign = {(0,1): p01, (1,0): p10}
            if check_axioms(K_assign, part_assign, step_assign):
                merge_exists = True
                break
        if merge_exists: break
    if merge_exists: break

print("Test C: Temporal merging allowed? →", "YES (time paradox!)" if merge_exists else "NO (merging excluded)")

