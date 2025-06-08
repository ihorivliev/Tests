# Stage 2 Extended: Axioms of Commutativity, Idempotence, and Neutral Element
# ---------------------------------------------------------------------------
# Domain: {0,1}
# Signature:
#   P(x)               - unary predicate
#   op(x, y) -> {0,1}  - binary operation
#
# Axioms:
#   C: ∀x,y. op(x,y) = op(y,x)          (commutativity)
#   I: ∀x.   op(x,x) = x                (idempotence)
#   N: ∃e. ∀x. op(e,x)=x and op(x,e)=x   (existence of neutral element)
#
# We test the following formulas under these axioms:
#   F1: ∀x. P(x)
#   F2: ∃x. ¬P(x)
#   F3: ∀x,y. op(x,y) = x
#   F4: ∃x,y. op(x,y) ≠ x
#   F5: ∀x,y. op(x,y) = op(y,x)
#   F6: ∃x,y. op(x,y) ≠ op(y,x)
#   F7: ∀x. op(x,x) = x
#   F8: ∃e. ∀x. op(e,x)=x ∧ op(x,e)=x

from itertools import product

nodes = [0, 1]
pairs = [(i, j) for i in nodes for j in nodes]

# Helper functions for axioms
def is_commutative(op):
    return all(op[(i, j)] == op[(j, i)] for (i, j) in pairs)

def is_idempotent(op):
    return all(op[(i, i)] == i for i in nodes)

def has_neutral(op):
    for e in nodes:
        if all(op[(e, x)] == x and op[(x, e)] == x for x in nodes):
            return True
    return False

def satisfies_axioms(op):
    return is_commutative(op) and is_idempotent(op) and has_neutral(op)

# Formula evaluators
def F1(P, op): return P[0] and P[1]
def F2(P, op): return (not P[0]) or (not P[1])
def F3(P, op): return all(op[(i, j)] == i for (i, j) in pairs)
def F4(P, op): return any(op[(i, j)] != i for (i, j) in pairs)
def F5(P, op): return is_commutative(op)
def F6(P, op): return not is_commutative(op)
def F7(P, op): return is_idempotent(op)
def F8(P, op): return has_neutral(op)

tests = [
    ("∀x. P(x)",                   F1),
    ("∃x. ¬P(x)",                  F2),
    ("∀x,y. op(x,y)=x",            F3),
    ("∃x,y. op(x,y)≠x",            F4),
    ("∀x,y. op(x,y)=op(y,x)",      F5),
    ("∃x,y. op(x,y)≠op(y,x)",      F6),
    ("∀x. op(x,x)=x",              F7),
    ("∃e. ∀x. e neutral (op)",     F8),
]

def test_formula(func):
    sat = False
    nsat = False
    # Enumerate op assignments
    for op_vals in product(nodes, repeat=len(pairs)):
        op = {pairs[k]: op_vals[k] for k in range(len(pairs))}
        if not satisfies_axioms(op):
            continue
        # Enumerate P assignments
        for P_bits in product([False, True], repeat=len(nodes)):
            P = {nodes[k]: P_bits[k] for k in range(len(nodes))}
            val = func(P, op)
            if val:
                sat = True
            else:
                nsat = True
            if sat and nsat:
                return True, True
    return sat, nsat

# Run tests
results = []
for desc, func in tests:
    sat, nsat = test_formula(func)
    results.append((desc, sat, nsat))

# Display results
print(f"{'Formula':<30} {'Sat?':<5} {'¬Formula Sat?':<14}")
print("-"*55)
for desc, sat, nsat in results:
    print(f"{desc:<30} {str(sat):<5} {str(nsat):<14}")
