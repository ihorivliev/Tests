from z3 import (
    DeclareSort, Const, Consts, IntSort, BoolSort, Function,
    ForAll, Implies, Solver, Not, sat, unsat, And
)

# --- Sorts and Constants ---
Pattern = DeclareSort('Pattern')
p1, p2, p3 = Consts('p1 p2 p3', Pattern)
a, b, c = Consts('a b c', Pattern)

# --- Functions representing core concepts ---
Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())
IsPartOf = Function('IsPartOf', Pattern, Pattern, BoolSort())
FindSubPattern = Function('FindSubPattern', Pattern, Pattern)
IsSlice = Function('IsSlice', Pattern, BoolSort())
Interpret = Function('Interpret', Pattern, Pattern, IntSort())
IsObserver = Function('IsObserver', Pattern, BoolSort())
Perceive = Function('Perceive', Pattern, Pattern, Pattern, IntSort())
GetCopy = Function('GetCopy', Pattern, Pattern)

# --- Axioms from the Treatise ---
universal_principle = ForAll([p1, p2], Implies(Structure(p1) == Structure(p2), Feeling(p1) == Feeling(p2)))
axiom_ss_part1 = ForAll([p1], IsPartOf(FindSubPattern(p1), p1))
axiom_ss_part2 = ForAll([p1], Not(FindSubPattern(p1) == p1))
axiom_cognition = ForAll([p1, p2, p3], Implies(And(IsObserver(p1), IsSlice(p2)), Perceive(p1, p2, p3) == Interpret(p2, p3)))
axiom_combinatorics = ForAll([p1], Implies(IsObserver(p1), And(IsObserver(GetCopy(p1)), p1 != GetCopy(p1), Structure(p1) == Structure(GetCopy(p1)))))

# --- NEW, STRICTER AXIOM ---
# Axiom: The IsPartOf relation must be transitive.
axiom_transitivity = ForAll(
    [a, b, c],
    Implies(
        And(IsPartOf(a, b), IsPartOf(b, c)),
        IsPartOf(a, c)
    )
)

# --- Full System Rigor Check ---
system_solver = Solver()
system_solver.add(
    universal_principle,
    axiom_ss_part1,
    axiom_ss_part2,
    axiom_cognition,
    axiom_combinatorics,
    axiom_transitivity # Adding the new constraint
)

result = system_solver.check()

print("--- Test 1: Full System Check with Stricter Axioms ---")
print("Solver result:", result)

if result == sat:
    print("✅ Success! The model is SATISFIABLE.")
    print("The system remains consistent even with the strict requirement of transitivity.")
elif result == unsat:
    print("❌ Failure: The axioms become contradictory when transitivity is enforced.")
else:
    print("⚠️ Unknown result.")