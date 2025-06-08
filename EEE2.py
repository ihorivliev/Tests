# Stage 2: Deep No‐Mercy Test with Commutativity Axiom (Python 3 only)
# --------------------------------------------------------------------
# Domain = {0,1}
# Predicate: P(x)
# Binary op: op(x,y) ∈ {0,1}
# Axiom C: ∀x,y. op(x,y) = op(y,x)
#
# Formulas:
#  F1: ∀x. P(x)
#  F2: ∃x. ¬P(x)
#  F3: ∀x,y. op(x,y) = x
#  F4: ∃x,y. op(x,y) ≠ x
#  F5: ∀x,y. op(x,y) = op(y,x)  (commutativity)
#  F6: ∃x,y. op(x,y) ≠ op(y,x)
#
# For each formula, we determine if both it *and* its negation remain
# satisfiable under Axiom C (True/True means under‐constrained).

from itertools import product

nodes = [0, 1]
pairs = [(i, j) for i in nodes for j in nodes]

def eval_F1(P, op): return P[0] and P[1]
def eval_F2(P, op): return (not P[0]) or (not P[1])
def eval_F3(P, op): return all(op[(i,j)] == i    for (i,j) in pairs)
def eval_F4(P, op): return any(op[(i,j)] != i    for (i,j) in pairs)
def eval_F5(P, op): return all(op[(i,j)] == op[(j,i)] for (i,j) in pairs)
def eval_F6(P, op): return any(op[(i,j)] != op[(j,i)] for (i,j) in pairs)

tests = [
    ("∀x. P(x)"                   , eval_F1),
    ("∃x. ¬P(x)"                  , eval_F2),
    ("∀x,y. op(x,y)=x"            , eval_F3),
    ("∃x,y. op(x,y)≠x"            , eval_F4),
    ("∀x,y. op(x,y)=op(y,x)"      , eval_F5),
    ("∃x,y. op(x,y)≠op(y,x)"      , eval_F6),
]

def commutes(op):
    # Check Axiom C on op
    return all(op[(i,j)] == op[(j,i)] for (i,j) in pairs)

def test_under_axiom(formula_eval):
    sat = False
    nsat = False
    # Enumerate all P-assignments (4 total)
    for P_bits in product([False, True], repeat=2):
        P = {0: P_bits[0], 1: P_bits[1]}
        # Enumerate all op-assignments (16 total), filter by commutativity
        for op_vals in product([0,1], repeat=len(pairs)):
            op = {pairs[k]: op_vals[k] for k in range(len(pairs))}
            if not commutes(op): continue
            val = formula_eval(P, op)
            if val: sat = True
            else:   nsat = True
            if sat and nsat:
                return True, True
    return sat, nsat

# Run and print results
print(f"{'Formula':<30} {'Sat?':<5} {'¬Formula Sat?':<14}")
print("-"*55)
for desc, func in tests:
    sat, nsat = test_under_axiom(func)
    print(f"{desc:<30} {str(sat):<5} {str(nsat):<14}")
