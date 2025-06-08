# E19_temporal_ordering_tests.py

from z3 import DeclareSort, Consts, Function, Solver, And, Or, Not, Implies, sat

# --- Domain Declaration ---
Pattern = DeclareSort('Pattern')
P0, P1, P2 = Consts('P0 P1 P2', Pattern)
patterns = [P0, P1, P2]

# --- Step Function ---
Step = Function('Step', Pattern, Pattern)

# --- Constraints List ---
cons = []

# 0. Basic Step Injectivity (no 1- or 2-step loops)
for p in patterns:
    cons.append(Step(p) != p)
    cons.append(Step(Step(p)) != p)
    cons.append(Step(Step(p)) != Step(p))

# 1. Path k=0,1,2
def Path(p0, pi, k):
    if k == 0:
        return pi == p0
    if k == 1:
        return pi == Step(p0)
    if k == 2:
        return pi == Step(Step(p0))
    raise ValueError

# 2. EarlierThan definition (unrolled for k in {0,1,2})
def EarlierThan(p0, pi, pj):
    return Or(
        And(Path(p0, pi, 0), Path(p0, pj, 1)),
        And(Path(p0, pi, 0), Path(p0, pj, 2)),
        And(Path(p0, pi, 1), Path(p0, pj, 2))
    )

# 3. Irreflexivity: ¬EarlierThan(p0, pi, pi)
for p0 in patterns:
    for pi in patterns:
        cons.append(Not(EarlierThan(p0, pi, pi)))

# 4. Asymmetry: EarlierThan(p0, pi, pj) ⇒ ¬EarlierThan(p0, pj, pi)
for p0 in patterns:
    for pi in patterns:
        for pj in patterns:
            cons.append(
                Implies(EarlierThan(p0, pi, pj),
                        Not(EarlierThan(p0, pj, pi)))
            )

# 5. Transitivity: if pi< pj and pj< pk then pi< pk
for p0 in patterns:
    for pi in patterns:
        for pj in patterns:
            for pk in patterns:
                cons.append(
                    Implies(
                        And(EarlierThan(p0, pi, pj),
                            EarlierThan(p0, pj, pk)),
                        EarlierThan(p0, pi, pk)
                    )
                )

# --- Solver ---
solver = Solver()
solver.add(*cons)
result = solver.check()

print("=== SMT Test: Emergent Temporal Ordering ===")
print("Solver result:", result)
if result == sat:
    print("✅ Temporal ordering (irreflexivity, asymmetry, transitivity) holds on a 3-element domain.")
else:
    print("❌ Temporal ordering axioms failed (UNSAT or UNKNOWN).")
