from z3 import (
    DeclareSort, Consts, Function,
    IntSort, BoolSort,
    Solver, Implies, And, Or, Not, sat
)

# --- Sorts and Constants ---
Pattern = DeclareSort('Pattern')
P0, P1, P2 = Consts('P0 P1 P2', Pattern)
patterns = [P0, P1, P2]

# --- Function Declarations ---
Structure      = Function('Structure',      Pattern, IntSort())
Feeling        = Function('Feeling',        Pattern, IntSort())
Describe       = Function('Describe',       Pattern, Pattern)
FindSubPattern = Function('FindSubPattern', Pattern, Pattern)
IsSlice        = Function('IsSlice',        Pattern, BoolSort())
Interpret      = Function('Interpret',      Pattern, Pattern, IntSort())
IsObserver     = Function('IsObserver',     Pattern, BoolSort())
Perceive       = Function('Perceive',       Pattern, Pattern, Pattern, IntSort())
SelfModel      = Function('SelfModel',      Pattern, Pattern)

cons = []

# 1. Universal Principle
for p in patterns:
    for q in patterns:
        cons.append(
            Implies(Structure(p) == Structure(q),
                    Feeling(p)   == Feeling(q))
        )

# 2. Absolute Combinatorics: ∀o: IsObserver(o) → ∃o' ≠ o: Structure(o') = Structure(o)
for o in patterns:
    # Build a disjunction over all o' of (o' != o AND Structure(o')==Structure(o))
    comb_cases = [And(o != o2, Structure(o2) == Structure(o)) for o2 in patterns]
    cons.append(
        Implies(IsObserver(o),
                Or(*comb_cases))
    )

# 3. Map–Territory Gap: ∀p: Describe(p) ≠ p
for p in patterns:
    cons.append(Describe(p) != p)

# 4. Self-Similarity Proxy: ∀p: FindSubPattern(p) ≠ p
for p in patterns:
    cons.append(FindSubPattern(p) != p)

# 5. Slice Functionality
slice_diff = []
for s1 in patterns:
    for s2 in patterns:
        if s1 == s2: 
            continue
        for x in patterns:
            slice_diff.append(
                And(IsSlice(s1), IsSlice(s2),
                    Interpret(s1, x) != Interpret(s2, x))
            )
cons.append(Or(*slice_diff))

# 6. Cognition
for o in patterns:
    for s in patterns:
        for x in patterns:
            cons.append(
                Implies(And(IsObserver(o), IsSlice(s)),
                        Perceive(o, s, x) == Interpret(s, x))
            )

# 7. Self-Modeling: ∀o: IsObserver(o) → SelfModel(o) ≠ o
for o in patterns:
    cons.append(
        Implies(IsObserver(o),
                SelfModel(o) != o)
    )

# --- Solve ---
solver = Solver()
solver.add(*cons)
result = solver.check()

print("=== Integrated Axioms SMT Check ===")
print("Solver result:", result)
if result == sat:
    print("✅ All axioms are jointly satisfiable over a 3-element domain.")
else:
    print("❌ Unexpected UNSAT or UNKNOWN.")
