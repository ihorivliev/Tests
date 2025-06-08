from z3 import (
    DeclareSort, Const, IntSort, BoolSort, Function,
    ForAll, Implies, Solver, Not, sat, unsat, And
)

# --- Sorts and Constants ---
Pattern = DeclareSort('Pattern')
p1 = Const('p1', Pattern)
p2 = Const('p2', Pattern)

# --- Functions representing core concepts ---
Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())
IsPartOf = Function('IsPartOf', Pattern, Pattern, BoolSort())
FindSubPattern = Function('FindSubPattern', Pattern, Pattern)

# --- NEW: Declarations for the "Slice" ---
IsSlice = Function('IsSlice', Pattern, BoolSort())
# Interpret(slice, pattern_to_interpret) -> perceived_value
Interpret = Function('Interpret', Pattern, Pattern, IntSort())

# --- Axioms from the Treatise ---

# 1. Universal Principle
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


# --- Targeted Check for Slice Functionality ---

# Let's create a new solver for this specific test
slice_solver = Solver()

# First, add all the established axioms of our reality
slice_solver.add(universal_principle)
slice_solver.add(axiom_ss_part1)
slice_solver.add(axiom_ss_part2)

# Now, set up the scenario for the test
s1 = Const('s1', Pattern)
s2 = Const('s2', Pattern)
p_to_interpret = Const('p_to_interpret', Pattern)

# We assert that s1 and s2 are distinct Slices
slice_solver.add(IsSlice(s1))
slice_solver.add(IsSlice(s2))
slice_solver.add(s1 != s2)

# The core of the test: Is it possible for these two different Slices
# to interpret the same pattern and get different results?
slice_solver.add(Interpret(s1, p_to_interpret) != Interpret(s2, p_to_interpret))

# Check satisfiability
result = slice_solver.check()

print("--- Slice Functionality Check ---")
print("Solver result:", result)

if result == sat:
    print("✅ Success! The model is SATISFIABLE.")
    print("This confirms that it's consistent for two different Slices to yield different interpretations of the same pattern.")
    print("This aligns with the role of a Slice as a 'projective lens'.")
elif result == unsat:
    print("❌ Unexpected: The axioms prevent different Slices from having different interpretations.")
else:
    print("⚠️ Unknown result.")