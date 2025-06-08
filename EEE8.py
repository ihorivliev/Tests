# Stage 5: No‑Mercy Audit with Unit‑in‑Filter Axiom
# --------------------------------------------------
# Domain: {0,1}
# Signature:
#   P(x)             - unary predicate
#   op(x, y) -> {0,1} - binary operation
#
# Axioms C, I, N, A, U, F as before, plus:
#   V: ∀x. (neutral element e satisfies ∀y. op(e,y)=y and op(y,e)=y) → P(e)
#   This ensures the neutral element is in the filter.
#
# We'll test:
#   F17: ∀x. (∀y. op(x,y)=y) → P(x)
#   F18: ∃x. (∀y. op(x,y)=y) ∧ ¬P(x)
#   F22: ∃x. P(x)

from itertools import product

nodes = [0, 1]
pairs = [(i, j) for i in nodes for j in nodes]

# Axiom checkers (C, I, N, A, U as before)
def is_commutative(op): return all(op[(i,j)]==op[(j,i)] for i,j in pairs)
def is_idempotent(op):  return all(op[(i,i)]==i for i in nodes)
def neutrals(op):        return [e for e in nodes if all(op[(e,x)]==x and op[(x,e)]==x for x in nodes)]
def has_neutral(op):     return len(neutrals(op)) >= 1
def unique_neutral(op):  return len(neutrals(op)) == 1
def is_associative(op):  return all(op[(i, op[(j,k)])] == op[(op[(i,j)],k)] 
                                      for i,j,k in product(nodes, repeat=3))

# Build all models satisfying original axioms + filter + V
def valid_models():
    models = []
    for op_vals in product(nodes, repeat=len(pairs)):
        op = {pairs[k]: op_vals[k] for k in range(len(pairs))}
        if not (is_commutative(op) and is_idempotent(op)
                and has_neutral(op) and unique_neutral(op)
                and is_associative(op)):
            continue
        e_list = neutrals(op)
        if len(e_list) != 1:
            continue
        e = e_list[0]
        # Enumerate P assignments, but require prime-filter F and V
        for bits in product([False, True], repeat=len(nodes)):
            P = {nodes[k]: bits[k] for k in range(len(nodes))}
            # Prime-filter: ∀i,j: P(i)&P(j) ↔ P(op(i,j))
            if not all((P[i] and P[j]) == P[op[(i,j)]] for i,j in pairs):
                continue
            # Axiom V: neutral element in filter
            if not P[e]:
                continue
            models.append((op, P))
    return models

models = valid_models()

# Formula evaluators
def F17(op, P): # ∀x. (neutral → P)
    return all((all(op[(x,y)]==y for y in nodes) <= P[x]) for x in nodes)
def F18(op, P): # ∃x. neutral ∧ ¬P(x)
    return any((all(op[(x,y)]==y for y in nodes) and not P[x]) for x in nodes)
def F22(op, P): # ∃x. P(x)
    return any(P[x] for x in nodes)

tests = [
    ("F17: ∀x. neutral→P", F17),
    ("F18: ∃x. neutral∧¬P(x)", F18),
    ("F22: ∃x. P(x)"       , F22),
]

print(f"{'Formula':<25} {'Sat?':<5} {'¬Formula Sat?':<14}")
print("-"*50)
for desc, func in tests:
    sat = any(func(op, P) for op, P in models)
    nsat = any(not func(op, P) for op, P in models)
    print(f"{desc:<25} {str(sat):<5} {str(nsat):<14}")
