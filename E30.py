from z3 import (
    DeclareSort, Const, Consts, IntSort, BoolSort, Function,
    ForAll, Implies, Solver, Not, sat, unsat, And
)

# --- Setup (Sorts, Constants, Functions) ---
Pattern = DeclareSort('Pattern')
p1, p2, p3 = Consts('p1 p2 p3', Pattern)
a, b, c = Consts('a b c', Pattern)

Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())
IsPartOf = Function('IsPartOf', Pattern, Pattern, BoolSort())
FindSubPattern = Function('FindSubPattern', Pattern, Pattern)
K = Function('K', Pattern, IntSort()) # A function for Complexity

# --- Axioms ---
# We only need the axioms relevant to parts and complexity for this proof.
axiom_ss_part1 = ForAll([p1], IsPartOf(FindSubPattern(p1), p1))
axiom_ss_part2 = ForAll([p1], Not(FindSubPattern(p1) == p1))
axiom_transitivity = ForAll([a, b, c], Implies(And(IsPartOf(a, b), IsPartOf(b, c)), IsPartOf(a, c)))

# A new axiom linking complexity to structure (a reasonable assumption)
axiom_k_structure = ForAll([p1, p2], Implies(Structure(p1) == Structure(p2), K(p1) == K(p2)))

# --- Adversarial Proof ---
proof_solver = Solver()
proof_solver.add(
    axiom_ss_part1,
    axiom_ss_part2,
    axiom_transitivity,
    axiom_k_structure
)

# Create two specific constants for the adversarial claim
c1, c2 = Consts('c1 c2', Pattern)

# The Adversarial Claim: Assert that there EXISTS a part c1 of c2
# such that the complexity of the part is GREATER than the whole.
adversarial_claim = And(
    IsPartOf(c1, c2),
    K(c1) > K(c2)
)
proof_solver.add(adversarial_claim)

result = proof_solver.check()

print("\n--- Test 2: Adversarial Proof of Complexity Ordering ---")
print("Solver result:", result)

if result == unsat:
    print("✅ Proof successful! The system is UNSATISFIABLE.")
    print("This proves that a part CANNOT be more complex than its whole in any valid model.")
elif result == sat:
    print("❌ Proof failed. A model was found where a part is more complex than its whole.")
    print("This indicates a weakness or incompleteness in our axioms.")
else:
    print("⚠️ Unknown result.")