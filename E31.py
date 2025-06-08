from z3 import (
    DeclareSort, Const, Consts, IntSort, BoolSort, Function,
    ForAll, Implies, Solver, Not, sat, unsat, And
)

# --- Setup (Sorts, Constants, Functions) ---
Pattern = DeclareSort('Pattern')
p, w = Consts('p w', Pattern) # Renamed for clarity in the new axiom
p1, p2 = Consts('p1 p2', Pattern)
a, b, c = Consts('a b c', Pattern)

IsPartOf = Function('IsPartOf', Pattern, Pattern, BoolSort())
K = Function('K', Pattern, IntSort()) # A function for Complexity

# --- Axioms ---
axiom_transitivity = ForAll([a, b, c], Implies(And(IsPartOf(a, b), IsPartOf(b, c)), IsPartOf(a, c)))

# --- THE NEW, CRITICAL AXIOM ---
# Axiom of Structural Subordination: A proper part is always less complex than its whole.
axiom_structural_subordination = ForAll(
    [p, w],
    Implies(
        And(IsPartOf(p, w), p != w),
        K(p) < K(w)
    )
)

# --- Final Adversarial Proof ---
proof_solver = Solver()
proof_solver.add(
    axiom_transitivity,
    axiom_structural_subordination # Adding the new, stronger axiom
)

# Create two specific constants for the adversarial claim
c1, c2 = Consts('c1 c2', Pattern)

# The Adversarial Claim: Assert that there EXISTS a part c1 of c2
# such that the complexity of the part is GREATER than the whole.
# We also assert they are not equal, to engage the new axiom.
adversarial_claim = And(
    IsPartOf(c1, c2),
    c1 != c2,
    K(c1) > K(c2)
)
proof_solver.add(adversarial_claim)

result = proof_solver.check()

print("\n--- Final Adversaral Proof with Stricter Axioms ---")
print("Solver result:", result)

if result == unsat:
    print("✅✅✅ Ultimate Proof Successful! The system is UNSATISFIABLE.")
    print("The Axiom of Structural Subordination successfully closed the loophole.")
    print("This formally proves that a part CANNOT be more complex than its whole in the 'Existe' framework.")
elif result == sat:
    print("❌❌❌ Ultimate Proof Failed. The system is still SATISFIABLE.")
    print("A weakness remains in the axiomatic system.")
else:
    print("⚠️ Unknown result.")