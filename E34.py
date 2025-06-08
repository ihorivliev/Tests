from z3 import (
    DeclareSort, Const, Consts, IntSort, BoolSort, Function,
    ForAll, Implies, Solver, Not, sat, unsat, And, Distinct
)
# Re-importing ALL axioms from the Final Validation Suite
Pattern = DeclareSort('Pattern')
p1, p2, p3, a, b, c = Consts('p1 p2 p3 a b c', Pattern)
Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())
K = Function('K', Pattern, IntSort())
IsPartOf = Function('IsPartOf', Pattern, Pattern, BoolSort())
FindSubPattern = Function('FindSubPattern', Pattern, Pattern)
IsSlice = Function('IsSlice', Pattern, BoolSort())
Interpret = Function('Interpret', Pattern, Pattern, IntSort())
IsObserver = Function('IsObserver', Pattern, BoolSort())
Perceive = Function('Perceive', Pattern, Pattern, Pattern, IntSort())
GetCopy = Function('GetCopy', Pattern, Pattern)
Step = Function('Step', Pattern, Pattern)
ALL_AXIOMS = [
    ForAll([p1, p2], (Structure(p1) == Structure(p2)) == (Feeling(p1) == Feeling(p2))),
    ForAll([p1], IsPartOf(FindSubPattern(p1), p1)),
    ForAll([p1], FindSubPattern(p1) != p1),
    ForAll([p1, p2, p3], Implies(And(IsObserver(p1), IsSlice(p2)), Perceive(p1, p2, p3) == Interpret(p2, p3))),
    ForAll([p1], Implies(IsObserver(p1), And(IsObserver(GetCopy(p1)), p1 != GetCopy(p1), Structure(p1) == Structure(GetCopy(p1))))),
    ForAll([a, b, c], Implies(And(IsPartOf(a, b), IsPartOf(b, c)), IsPartOf(a, c))),
    ForAll([p1, p2], Implies(And(IsPartOf(p1, p2), p1 != p2), K(p1) < K(p2))),
    ForAll([p1, p2], Implies(Structure(p1) == Structure(p2), K(p1) == K(p2)))
]

# --- Test 4b: Cyclic Time Consistency Check ---
print("\n--- Test 4b: Cyclic Time Consistency Check ---")

solver = Solver()
solver.add(ALL_AXIOMS)

# Define a small universe for the cycle
P0, P1, P2 = Consts('P0 P1 P2', Pattern)
solver.add(Distinct(P0, P1, P2))

# Assert the existence of a perfect 3-cycle
cycle_definition = And(
    Step(P0) == P1,
    Step(P1) == P2,
    Step(P2) == P0
)
solver.add(cycle_definition)

result = solver.check()
print("Solver result:", result)

if result == sat:
    print("✅ Success! The system is SATISFIABLE.")
    print("   This confirms the full axiomatic system is consistent with a stable, linear, cyclic model of time.")
elif result == unsat:
    print("❌ Failure: The axioms forbid the existence of a simple, stable timeline.")
else:
    print("⚠️ Unknown result.")