# Stage 3: No‑Mercy Audit with Full Axioms (C, I, N, A, U, F)
# -----------------------------------------------------------
# Domain: {0,1}
# Signature:
#   P(x)             - unary predicate
#   op(x, y) -> {0,1} - binary operation
#
# Axioms:
#   C: ∀x,y. op(x,y) = op(y,x)                       (commutativity)
#   I: ∀x.   op(x,x) = x                             (idempotence)
#   N: ∃e. ∀x. op(e,x)=x ∧ op(x,e)=x                  (neutral element exists)
#   A: ∀x,y,z. op(x,op(y,z)) = op(op(x,y),z)         (associativity)
#   U: Unique neutral: any e,e' both neutral ⇒ e=e'
#   F: ∀x,y. P(x) ∧ P(y) ↔ P(op(x,y))                (prime-filter condition)
#
# We test the following formulas under these axioms:
#   F1: ∀x. P(x)
#   F2: ∃x. ¬P(x)
#   F3: ∀x,y. op(x,y)=x
#   F4: ∃x,y. op(x,y)≠x
#   F5: ∀x,y. op(x,y)=op(y,x)
#   F6: ∃x,y. op(x,y)≠op(y,x)
#   F7: ∀x. op(x,x)=x
#   F8: ∃e. ∀x. op(e,x)=x ∧ op(x,e)=x
#   F9: ∀x,y,z. op(x,op(y,z)) = op(op(x,y),z)
#   F10: ∃x,y,z. op(x,op(y,z)) ≠ op(op(x,y),z)
#   F11: ∀e,e'. (e,e' neutral) ⇒ e=e'
#   F12: ∃e≠e'. e,e' both neutral
#   F13: ∀x,y. (P(x) and P(y)) == P(op(x,y))
#   F14: ∃x,y. (P(x) and P(y)) != P(op(x,y))

from itertools import product

nodes = [0, 1]
pairs = [(i, j) for i in nodes for j in nodes]

# Axiom checkers
def is_commutative(op):
    return all(op[(i, j)] == op[(j, i)] for (i, j) in pairs)

def is_idempotent(op):
    return all(op[(i, i)] == i for i in nodes)

def neutrals(op):
    return [e for e in nodes if all(op[(e, x)] == x and op[(x, e)] == x for x in nodes)]

def has_neutral(op):
    return len(neutrals(op)) >= 1

def unique_neutral(op):
    return len(neutrals(op)) <= 1

def is_associative(op):
    return all(op[(i, op[(j, k)])] == op[(op[(i, j)], k)] for i, j, k in product(nodes, repeat=3))

def satisfies_op_axioms(op):
    return (is_commutative(op) and is_idempotent(op)
            and has_neutral(op) and unique_neutral(op)
            and is_associative(op))

# Formula evaluators
def F1(P, op): return P[0] and P[1]
def F2(P, op): return (not P[0]) or (not P[1])
def F3(P, op): return all(op[(i, j)] == i for (i, j) in pairs)
def F4(P, op): return any(op[(i, j)] != i for (i, j) in pairs)
def F5(P, op): return is_commutative(op)
def F6(P, op): return not is_commutative(op)
def F7(P, op): return is_idempotent(op)
def F8(P, op): return has_neutral(op)
def F9(P, op): return is_associative(op)
def F10(P, op): return any(op[(i, op[(j, k)])] != op[(op[(i, j)], k)] for i, j, k in product(nodes, repeat=3))
def F11(P, op): return unique_neutral(op)
def F12(P, op): return any(e != e_p for e in neutrals(op) for e_p in neutrals(op) if e != e_p)
def F13(P, op): 
    return all((P[i] and P[j]) == P[op[(i, j)]] for (i, j) in pairs)
def F14(P, op): 
    return any((P[i] and P[j]) != P[op[(i, j)]] for (i, j) in pairs)

tests = [
    ("∀x. P(x)",      F1),
    ("∃x. ¬P(x)",     F2),
    ("∀x,y. op(x,y)=x", F3),
    ("∃x,y. op(x,y)≠x", F4),
    ("∀x,y. op(x,y)=op(y,x)", F5),
    ("∃x,y. op(x,y)≠op(y,x)", F6),
    ("∀x. op(x,x)=x",   F7),
    ("∃e. ∀x. op(e,x)=x ∧ op(x,e)=x", F8),
    ("∀x,y,z. assoc",  F9),
    ("∃x,y,z. ≠ assoc", F10),
    ("∀e,e'. unique neutral", F11),
    ("∃e≠e'. two neutrals",   F12),
    ("∀x,y. P(x)&P(y)↔P(op(x,y))", F13),
    ("∃x,y. (P(x)&P(y))≠P(op(x,y))", F14),
]

# Collect all models satisfying axioms
models = []
# Enumerate all op assignments (2^4 = 16)
for op_vals in product(nodes, repeat=len(pairs)):
    op = {pairs[k]: op_vals[k] for k in range(len(pairs))}
    if not satisfies_op_axioms(op):
        continue
    # For each op, enumerate P assignments (2^2 = 4)
    for P_bits in product([False, True], repeat=len(nodes)):
        P = {nodes[k]: P_bits[k] for k in range(len(nodes))}
        # P must satisfy filter axiom F13
        if not F13(P, op):
            continue
        models.append((P, op))

# Now test each formula
print(f"{'Formula':<30} {'Sat?':<5} {'¬Formula Sat?':<14}")
print("-"*55)
for desc, func in tests:
    sat = any(func(P, op) for (P, op) in models)
    nsat = any(not func(P, op) for (P, op) in models)
    print(f"{desc:<30} {str(sat):<5} {str(nsat):<14}")

