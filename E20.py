# E20_smt_full_n10.py

from z3 import (
    DeclareSort, Consts, Function,
    IntSort, BoolSort,
    Solver, Implies, And, Or, Not, sat
)

# --- Parameters ---
n = 30  # change this to 100 or 1000 for larger domains (may be slower)

# --- Domain Declaration ---
Pattern = DeclareSort('Pattern')
# Dynamically create P0, P1, ..., Pn-1
Patterns = Consts(' '.join(f'P{i}' for i in range(n)), Pattern)

# --- Uninterpreted Functions ---
Structure      = Function('Structure',      Pattern, IntSort())
Feeling        = Function('Feeling',        Pattern, IntSort())
Describe       = Function('Describe',       Pattern, Pattern)
FindSubPattern = Function('FindSubPattern', Pattern, Pattern)
IsSlice        = Function('IsSlice',        Pattern, BoolSort())
Interpret      = Function('Interpret',      Pattern, Pattern, IntSort())
IsObserver     = Function('IsObserver',     Pattern, BoolSort())
Perceive       = Function('Perceive',       Pattern, Pattern, Pattern, IntSort())
SelfModel      = Function('SelfModel',      Pattern, Pattern)
Step           = Function('Step',           Pattern, Pattern)

cons = []
patterns = list(Patterns)

# 1. Universal Principle
for p in patterns:
    for q in patterns:
        cons.append(Implies(Structure(p) == Structure(q),
                            Feeling(p) == Feeling(q)))

# 2. Absolute Combinatorics
for o in patterns:
    comb_cases = [And(o != o2, Structure(o2) == Structure(o)) for o2 in patterns]
    cons.append(Implies(IsObserver(o), Or(*comb_cases)))

# 3. Map–Territory Gap
for p in patterns:
    cons.append(Describe(p) != p)

# 4. Self-Similarity Proxy
for p in patterns:
    cons.append(FindSubPattern(p) != p)

# 5. Slice Functionality
slice_diff = []
for s1 in patterns:
    for s2 in patterns:
        if s1 == s2: continue
        for x in patterns:
            slice_diff.append(And(IsSlice(s1), IsSlice(s2),
                                  Interpret(s1, x) != Interpret(s2, x)))
cons.append(Or(*slice_diff))

# 6. Cognition
for o in patterns:
    for s in patterns:
        for x in patterns:
            cons.append(Implies(And(IsObserver(o), IsSlice(s)),
                                Perceive(o, s, x) == Interpret(s, x)))

# 7. Self-Modeling
for o in patterns:
    cons.append(Implies(IsObserver(o), SelfModel(o) != o))

# 8. Temporal Ordering (2-step injectivity)
for p in patterns:
    cons.append(Step(p) != p)
    cons.append(Step(Step(p)) != p)
    cons.append(Step(Step(p)) != Step(p))

# --- Solve ---
solver = Solver()
solver.add(*cons)
result = solver.check()

print("=== Full-System SMT Check for n =", n, " ===")
print("Solver result:", result)
if result == sat:
    print("✅ All axioms are jointly satisfiable over a", n, "-element domain.")
else:
    print("❌ Unexpected UNSAT or UNKNOWN; consider lowering n.")
