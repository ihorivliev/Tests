from z3 import (
    DeclareSort, Const, Consts, IntSort, BoolSort, Function,
    ForAll, Implies, Solver, Not, sat, unsat, And, Distinct
)

# Using a subset of axioms relevant to the core test
Pattern = DeclareSort('Pattern')
p1, p2, p3 = Consts('p1 p2 p3', Pattern)
Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())
Step = Function('Step', Pattern, Pattern)
AXIOM_UNIVERSAL = ForAll([p1, p2], (Structure(p1) == Structure(p2)) == (Feeling(p1) == Feeling(p2)))

# --- Test 4a: Bounded Adversarial Check ---
print("--- Test 4a: Bounded Adversarial Check (Time-Merging) ---")

solver = Solver()
solver.add(AXIOM_UNIVERSAL) # Add core axioms

# Define a small universe of 4 distinct patterns
P0, P1, P2, P3 = Consts('P0 P1 P2 P3', Pattern)
solver.add(Distinct(P0, P1, P2, P3))

# Adversarial Claim: Two distinct pasts merge into a single future.
# We assert that P0 and P1 are different, but their 'next step' is the same (P2).
adversarial_claim = And(
    P0 != P1,
    Step(P0) == P2,
    Step(P1) == P2
)
solver.add(adversarial_claim)

result = solver.check()
print("Solver result:", result)

if result == unsat:
    print("✅ Proof successful! The system is UNSATISFIABLE.")
    print("   This proves that even in a bounded model, two distinct moments cannot lead to the same future.")
elif result == sat:
    print("❌ DISCOVERY: The axioms permit time-merging.")
    print("   The solver found a valid model where the adversarial claim holds.")
else:
    print("⚠️ Unknown result.")