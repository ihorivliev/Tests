from z3 import (
    DeclareSort, Const, IntSort, BoolSort, Function,
    ForAll, Implies, Solver, Not, sat, unsat, And
)

# --- Sorts and Constants ---
Pattern = DeclareSort('Pattern')
p1, p2, p3 = Const('p1', Pattern), Const('p2', Pattern), Const('p3', Pattern)

# --- Functions representing core concepts ---
Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())
IsPartOf = Function('IsPartOf', Pattern, Pattern, BoolSort())
FindSubPattern = Function('FindSubPattern', Pattern, Pattern)
IsSlice = Function('IsSlice', Pattern, BoolSort())
Interpret = Function('Interpret', Pattern, Pattern, IntSort())
IsObserver = Function('IsObserver', Pattern, BoolSort())
Perceive = Function('Perceive', Pattern, Pattern, Pattern, IntSort())


# --- Axioms from the Treatise ---

# 1. Universal Principle
# CORRECTED: The 'if-then' structure must be built with Implies()
# to form a single boolean expression for the body of ForAll.
universal_principle = ForAll(
    [p1, p2],
    Implies(
        Structure(p1) == Structure(p2),
        Feeling(p1) == Feeling(p2)
    )
)

# 2. Axiom of Absolute Self-Similarity (in two parts)
axiom_ss_part1 = ForAll([p1], IsPartOf(FindSubPattern(p1), p1))
axiom_ss_part2 = ForAll([p1], Not(FindSubPattern(p1) == p1))

# 3. Axiom of Cognition
axiom_cognition = ForAll(
    [p1, p2, p3],
    Implies(
        And(IsObserver(p1), IsSlice(p2)),
        Perceive(p1, p2, p3) == Interpret(p2, p3)
    )
)


# --- Full System Consistency Check ---
system_solver = Solver()
system_solver.add(universal_principle)
system_solver.add(axiom_ss_part1)
system_solver.add(axiom_ss_part2)
system_solver.add(axiom_cognition)

result = system_solver.check()

print("--- Full System Consistency Check ---")
print("Solver result:", result)

if result == sat:
    print("✅ Success! The model is SATISFIABLE.")
    print("All axioms (Universal Principle, Self-Similarity, Cognition) are mutually consistent.")
elif result == unsat:
    print("❌ Unexpected: The axioms of the system are contradictory.")
else:
    print("⚠️ Unknown result.")