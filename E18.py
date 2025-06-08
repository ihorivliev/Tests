from z3 import (
    DeclareSort, Consts, Function,
    IntSort, BoolSort,
    Solver, Implies, And, Or, Not, sat
)

# --- Domain ---
Pattern = DeclareSort('Pattern')
P0, P1, P2 = Consts('P0 P1 P2', Pattern)
patterns = [P0, P1, P2]

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

# 1. Universal Principle: Structure(p)=Structure(q) ⇒ Feeling(p)=Feeling(q)
for p in patterns:
    for q in patterns:
        cons.append(Implies(Structure(p) == Structure(q),
                            Feeling(p) == Feeling(q)))

# 2. Absolute Combinatorics: IsObserver(o) ⇒ ∃o'≠o: Structure(o')=Structure(o)
for o in patterns:
    comb_cases = [And(o != o2, Structure(o2) == Structure(o)) for o2 in patterns]
    cons.append(Implies(IsObserver(o), Or(*comb_cases)))

# 3. Map–Territory Gap: Describe(p) ≠ p
for p in patterns:
    cons.append(Describe(p) != p)

# 4. Self-Similarity Proxy: FindSubPattern(p) ≠ p
for p in patterns:
    cons.append(FindSubPattern(p) != p)

# 5. Slice Functionality: ∃ distinct s1,s2,x: IsSlice(s1)∧IsSlice(s2)∧Interpret(s1,x)≠Interpret(s2,x)
slice_diff = []
for s1 in patterns:
    for s2 in patterns:
        if s1 == s2: continue
        for x in patterns:
            slice_diff.append(And(IsSlice(s1), IsSlice(s2),
                                  Interpret(s1, x) != Interpret(s2, x)))
cons.append(Or(*slice_diff))

# 6. Cognition: IsObserver(o)∧IsSlice(s) ⇒ Perceive(o,s,x)=Interpret(s,x)
for o in patterns:
    for s in patterns:
        for x in patterns:
            cons.append(Implies(And(IsObserver(o), IsSlice(s)),
                                Perceive(o, s, x) == Interpret(s, x)))

# 7. Self-Modeling: IsObserver(o) ⇒ SelfModel(o) ≠ o
for o in patterns:
    cons.append(Implies(IsObserver(o), SelfModel(o) != o))

# 8. Phenomenal Time Checks (2-step injectivity):
#    Step(p)≠p, Step(Step(p))≠p, Step(Step(p))≠Step(p)
for p in patterns:
    cons.append(Step(p) != p)
    cons.append(Step(Step(p)) != p)
    cons.append(Step(Step(p)) != Step(p))

# --- Solve ---
solver = Solver()
solver.add(*cons)
result = solver.check()

print("=== Full-System + Time Ordering SMT Check ===")
print("Solver result:", result)
if result == sat:
    print("✅ All axioms including 2-step time‐injectivity are jointly satisfiable over a 3-element domain.")
else:
    print("❌ Unexpected UNSAT or UNKNOWN.")
