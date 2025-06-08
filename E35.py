from z3 import (
    DeclareSort, Const, Consts, IntSort, BoolSort, Function,
    ForAll, Implies, Solver, Not, sat, unsat, And, Distinct
)

# --- Environment Setup ---
Pattern = DeclareSort('Pattern')
p1, p2 = Consts('p1 p2', Pattern)
Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())
Step = Function('Step', Pattern, Pattern)

# --- Core Axioms for Temporal Tests ---
# We only need the most fundamental axiom for these tests.
AXIOM_UNIVERSAL = ForAll([p1, p2], (Structure(p1) == Structure(p2)) == (Feeling(p1) == Feeling(p2)))

# The NEW and FINAL axiom required for a coherent timeline.
AXIOM_TEMPORAL_LINEARITY = ForAll([p1, p2], Implies(Step(p1) == Step(p2), p1 == p2))


# --- Test A: Proof that Time-Merging is now Forbidden ---
print("--- Test A: Adversarial Proof of Temporal Linearity ---")

solver_a = Solver()
solver_a.add(AXIOM_TEMPORAL_LINEARITY) # Add our new rule for time

# Adversarial Claim: Two distinct pasts merge into a single future.
c1, c2, c3 = Consts('c1 c2 c3', Pattern)
solver_a.add(And(
    c1 != c2,
    Step(c1) == c3,
    Step(c2) == c3
))

result_a = solver_a.check()
print("Solver result:", result_a)

if result_a == unsat:
    print("✅ Proof successful! The system is UNSATISFIABLE.")
    print("   The Axiom of Temporal Linearity successfully forbids time-merging.")
elif result_a == sat:
    print("❌ FAILED: The system still permits time-merging.")
else:
    print("⚠️ Unknown result.")


# --- Test B: Proof that a Cyclic Timeline is Consistent ---
print("\n--- Test B: Cyclic Time Consistency Check ---")

solver_b = Solver()
# We check if a cycle is consistent with the core principles of Being and Time.
solver_b.add(AXIOM_UNIVERSAL, AXIOM_TEMPORAL_LINEARITY)

# Define a small universe for the cycle
P0, P1, P2 = Consts('P0 P1 P2', Pattern)
solver_b.add(Distinct(P0, P1, P2))

# Assert the existence of a perfect 3-cycle
cycle_definition = And(
    Step(P0) == P1,
    Step(P1) == P2,
    Step(P2) == P0
)
solver_b.add(cycle_definition)

result_b = solver_b.check()
print("Solver result:", result_b)

if result_b == sat:
    print("✅ Success! The system is SATISFIABLE.")
    print("   This confirms that a stable, cyclic timeline is consistent with the core axioms.")
elif result_b == unsat:
    print("❌ FAILED: The axioms forbid the existence of a simple timeline.")
else:
    print("⚠️ Unknown result.")