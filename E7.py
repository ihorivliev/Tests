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

# --- NEW: Declaration for Combinatorics ---
GetCopy = Function('GetCopy', Pattern, Pattern)


# --- Axioms from the Treatise ---

# 1. Universal Principle
universal_principle = ForAll(
    [p1, p2],
    Implies(
        Structure(p1) == Structure(p2),
        Feeling(p1) == Feeling(p2)
    )
)

# 2. Axiom of Absolute Self-Similarity
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

# 4. NEW: Axiom of Absolute Combinatorics
#    For any observer o, its copy is also an observer, is distinct, and has the same structure.
axiom_combinatorics = ForAll(
    [p1],
    Implies(
        IsObserver(p1),
        And(
            IsObserver(GetCopy(p1)),
            p1 != GetCopy(p1),
            Structure(p1) == Structure(GetCopy(p1))
        )
    )
)


# --- Proof of Theorem: "The Dissolution of the Self" ---

# Theorem: An Observer and its copy are qualitatively identical.
# Proof strategy: Assert all axioms and the NEGATION of the theorem.
# If the result is UNSAT, the theorem is proven to be true.

proof_solver = Solver()
proof_solver.add(universal_principle)
proof_solver.add(axiom_ss_part1)
proof_solver.add(axiom_ss_part2)
proof_solver.add(axiom_cognition)
proof_solver.add(axiom_combinatorics)

# Let's consider a specific observer, O1
O1 = Const('O1', Pattern)
proof_solver.add(IsObserver(O1))

# Now, assert the NEGATION of the theorem we want to prove.
# The theorem is: Feeling(O1) == Feeling(GetCopy(O1))
# The negation is: Feeling(O1) != Feeling(GetCopy(O1))
proof_solver.add(Feeling(O1) != Feeling(GetCopy(O1)))


# Check satisfiability
result = proof_solver.check()

print("--- Theorem Proof: Dissolution of the Self ---")
print("Solver result:", result)

if result == unsat:
    print("✅ Proof successful! The system is UNSATISFIABLE.")
    print("This proves that an Observer and its structurally identical copy MUST have the same 'Feeling'.")
    print("The 'uniqueness of the self' is disproven within the axiomatic system.")
elif result == sat:
    print("❌ Proof failed. The system is SATISFIABLE.")
    print("This means it's possible for a copy to have a different 'Feeling', indicating a flaw in our axioms.")
else:
    print("⚠️ Unknown result.")