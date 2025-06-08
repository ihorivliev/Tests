from z3 import (
    DeclareSort, Const, IntSort, BoolSort, Function, 
    ForAll, Implies, Solver, Not, sat, unsat
)

# --- Setup from previous step ---
# Declare an uninterpreted sort "Pattern"
Pattern = DeclareSort('Pattern')

# Declare function symbols from Universal Principle
Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())

# Declare pattern constants (variables for ForAll)
p1 = Const('p1', Pattern)
p2 = Const('p2', Pattern)

# --- New declarations for Self-Similarity ---
# Declare the new predicate and function
IsPartOf = Function('IsPartOf', Pattern, Pattern, BoolSort())
FindSubPattern = Function('FindSubPattern', Pattern, Pattern)

# --- Axioms ---

# 1. Universal Principle (from before)
#    ∀p1, p2: if Structure(p1) == Structure(p2) then Feeling(p1) == Feeling(p2)
universal_principle = ForAll(
    [p1, p2],
    Implies(
        Structure(p1) == Structure(p2),
        Feeling(p1) == Feeling(p2)
    )
)

# 2. Axiom of Absolute Self-Similarity (Part 1: Existence)
#    ∀p1: IsPartOf(FindSubPattern(p1), p1)
axiom_ss_part1 = ForAll(
    [p1],
    IsPartOf(FindSubPattern(p1), p1)
)

# 3. Axiom of Absolute Self-Similarity (Part 2: No Final Simplification)
#    ∀p1: ¬(FindSubPattern(p1) = p1)
axiom_ss_part2 = ForAll(
    [p1],
    Not(FindSubPattern(p1) == p1)
)


# --- Consistency Check ---
# We add all our core axioms to the solver to see if they can coexist.
solver = Solver()
solver.add(universal_principle)
solver.add(axiom_ss_part1)
solver.add(axiom_ss_part2)

# Check satisfiability of the combined axioms
result = solver.check()

print("--- Axiom Consistency Check ---")
print("Solver result:", result)

if result == sat:
    print("✅ Success! The axioms (Universal Principle + Self-Similarity) are mutually consistent.")
    print("The solver found a model where all axioms can be true simultaneously.")
elif result == unsat:
    print("❌ Unexpected: The axioms are contradictory.")
else:
    print("⚠️ Unknown result.")