# EEE1-2_pure.py
# ---------------
# Signature:
#  • Domain = {0,1}
#  • Predicate P(x)
#  • Binary operation ◇(x,y) → {0,1}
#
# We test four sample formulas and their negations.
# No pandas, no ace_tools—just pure Python and itertools.

from itertools import product

# Domain and all ordered pairs
nodes = [0, 1]
pairs = [(i, j) for i in nodes for j in nodes]

# Formula evaluators:
def f1(P, op):
    # ∀x. P(x)
    return P[0] and P[1]

def f2(P, op):
    # ∃x. ¬P(x)
    return (not P[0]) or (not P[1])

def f3(P, op):
    # ∀x,y. op(x,y) == x
    return all(op[(i, j)] == i for (i, j) in pairs)

def f4(P, op):
    # ∃x,y. op(x,y) != x
    return any(op[(i, j)] != i for (i, j) in pairs)

tests = [
    ("∀x. P(x)",       f1),
    ("∃x. ¬P(x)",      f2),
    ("∀x,y. ◇(x,y)=x", f3),
    ("∃x,y. ◇(x,y)≠x", f4),
]

def check(formula):
    sat = False
    nsat = False
    # all possible assignments of P: 2^2 = 4 possibilities
    for P_bits in product([False, True], repeat=2):
        P = {0: P_bits[0], 1: P_bits[1]}
        # all possible definitions of ◇: each (i,j) maps to 0 or 1 → 2^4=16 possibilities
        for op_vals in product(nodes, repeat=len(pairs)):
            op = {pairs[k]: op_vals[k] for k in range(len(pairs))}
            result = formula(P, op)
            if result:
                sat = True
            else:
                nsat = True
            if sat and nsat:
                # both satisfiable and its negation satisfiable
                return True, True
    return sat, nsat

# Run and print results
print(f"{'Formula':<20}  {'Sat?':<5}  {'¬Formula Sat?':<14}")
print("-"*45)
for desc, func in tests:
    sat, nsat = check(func)
    print(f"{desc:<20}  {str(sat):<5}  {str(nsat):<14}")
