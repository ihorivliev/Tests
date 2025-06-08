# Stage 4: Expanded No‑Mercy Audit with Additional Formulas
# ----------------------------------------------------------
# We reuse models satisfying:
#   C: commutativity
#   I: idempotence
#   N: existence of a unique neutral element
#   A: associativity
#   U: unique neutral
#   F: prime-filter condition for P
#
# Additional formulas:
#  F15: ∀x,y. op(x, op(x,y)) = op(x,y)    (absorption)
#  F16: ∃x,y. op(x, op(x,y)) ≠ op(x,y)    (negation of absorption)
#  F17: ∀x. [(∀y. op(x,y)=y) → P(x)]     (neutral implies P)
#  F18: ∃x. [(∀y. op(x,y)=y) ∧ ¬P(x)]     (negation of F17)
#  F19: ∀x. op(x,x)=x                    (reflexivity of ≤; trivial)
#  F20: ∀x,y. (op(x,y)=x ∧ op(y,x)=y) → x=y  (antisymmetry)
#  F21: ∀x,y,z. ((op(x,y)=x ∧ op(y,z)=y) → op(x,z)=x)  (transitivity)
#
from itertools import product

nodes = [0,1]
pairs = [(i,j) for i in nodes for j in nodes]

# Reuse axiom checkers
def is_commutative(op): return all(op[(i,j)]==op[(j,i)] for i,j in pairs)
def is_idempotent(op):   return all(op[(i,i)]==i for i in nodes)
def neutrals(op):         return [e for e in nodes if all(op[(e,x)]==x and op[(x,e)]==x for x in nodes)]
def has_neutral(op):      return len(neutrals(op)) >= 1
def unique_neutral(op):   return len(neutrals(op)) == 1
def is_associative(op):   return all(op[(i, op[(j,k)])] == op[(op[(i,j)],k)] for i,j,k in product(nodes, repeat=3))
def satisfies_model(op, P):
    # op axioms
    if not (is_commutative(op) and is_idempotent(op) and has_neutral(op)
            and unique_neutral(op) and is_associative(op)):
        return False
    # filter axiom: ∀x,y. P(x) ∧ P(y) ↔ P(op(x,y))
    for i,j in pairs:
        if (P[i] and P[j]) != P[op[(i,j)]]:
            return False
    return True

# Build all valid models (op,P)
models = []
for op_vals in product(nodes, repeat=len(pairs)):
    op = {pairs[k]: op_vals[k] for k in range(len(pairs))}
    for P_bits in product([False, True], repeat=len(nodes)):
        P = {nodes[k]: P_bits[k] for k in range(len(nodes))}
        if satisfies_model(op, P):
            models.append((op, P))

# Formula evaluators
def F15(op,P):
    return all(op[(i, op[(i,j)])] == op[(i,j)] for i,j in pairs)
def F16(op,P):
    return any(op[(i, op[(i,j)])] != op[(i,j)] for i,j in pairs)
def F17(op,P):
    # ∀x. (∀y. op(x,y)=y) --> P(x)
    for x in nodes:
        if all(op[(x,y)]==y for y in nodes) and not P[x]:
            return False
    return True
def F18(op,P):
    # ∃x. (∀y. op(x,y)=y) and not P(x)
    return any(all(op[(x,y)]==y for y in nodes) and not P[x] for x in nodes)
def F19(op,P):
    return all(op[(x,x)]==x for x in nodes)
def F20(op,P):
    # (le(x,y) and le(y,x)) -> x==y
    for x,y in product(nodes,repeat=2):
        if op[(x,y)]==x and op[(y,x)]==y and x!=y:
            return False
    return True
def F21(op,P):
    for x,y,z in product(nodes,repeat=3):
        if op[(x,y)]==x and op[(y,z)]==y and op[(x,z)]!=x:
            return False
    return True

tests = [
    ("F15: absorption", F15),
    ("F16: ¬absorption", F16),
    ("F17: neutral → P", F17),
    ("F18: ¬(neutral → P)", F18),
    ("F19: op(x,x)=x (reflexivity)", F19),
    ("F20: antisymmetry", F20),
    ("F21: transitivity", F21),
]

# Evaluate tests
print(f"{'Formula':<25} {'Sat?':<5} {'¬Formula Sat?':<14}")
print("-"*50)
for desc, func in tests:
    sat = any(func(op,P) for op,P in models)
    nsat = any(not func(op,P) for op,P in models)
    print(f"{desc:<25} {str(sat):<5} {str(nsat):<14}")

