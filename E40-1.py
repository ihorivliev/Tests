from z3 import Solver, DeclareSort, Consts, Function, IntSort, BoolSort, And, Implies

# No‐Mercy Stress‐Test for the 'Existe' Framework
# ----------------------------------------------
# Applies the two axioms from the (fabricated) report:
#   1. Structural Subordination: (IsPartOf(p,w) ∧ p≠w) → K(p) < K(w)
#   2. Temporal Linearity: (Step(p1)==Step(p2)) → p1 == p2
# Then probes consistency, cycle‐freedom, and time‐merging.

# 1. Define a tiny universe of two patterns
Pattern = DeclareSort('Pattern')
p1, p2 = Consts('p1 p2', Pattern)

# 2. Uninterpreted functions
K       = Function('K', Pattern, IntSort())
IsPartOf = Function('IsPartOf', Pattern, Pattern, BoolSort())
Step    = Function('Step', Pattern, Pattern)

# 3. Core Axioms
axioms = [
    # Structural Subordination for (p1,p2)
    Implies(And(IsPartOf(p1, p2), p1 != p2), K(p1) < K(p2)),
    # Temporal Linearity for (p1,p2)
    Implies(Step(p1) == Step(p2), p1 == p2),
]

# -- Test A: Bare Consistency of Axioms
sA = Solver()
sA.add(*axioms)
print("Test A: Axioms alone are satisfiable? →", sA.check())  # Expect: sat
if sA.check().r == 1:
    print("  Example model (partial):", sA.model())
print()

# -- Test B: Attempt a 2‐cycle in IsPartOf → Should be UNSAT
sB = Solver()
# re‐add axioms
sB.add(*axioms)
# add symmetric cycle p1↔p2 and distinctness
sB.add(And(IsPartOf(p1, p2), IsPartOf(p2, p1), p1 != p2))
print("Test B: 2‐cycle in 'part‐of' →", sB.check())  # Expect: unsat
print()

# -- Test C: Attempt to merge time (Step(p1)==Step(p2) but p1!=p2) → UNSAT
sC = Solver()
sC.add(*axioms)
sC.add(p1 != p2, Step(p1) == Step(p2))
print("Test C: Temporal merging →", sC.check())  # Expect: unsat


