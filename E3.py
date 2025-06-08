from z3 import DeclareSort, Const, IntSort, Function, ForAll, Implies, Solver, Not, sat, unsat

# Declare an uninterpreted sort "Pattern"
Pattern = DeclareSort('Pattern')

# Declare function symbols: Structure: Pattern -> Int, Feeling: Pattern -> Int
Structure = Function('Structure', Pattern, IntSort())
Feeling = Function('Feeling', Pattern, IntSort())

# Declare two pattern constants p1, p2
p1 = Const('p1', Pattern)
p2 = Const('p2', Pattern)

# 1. Universal Principle: 
#    ∀p1, p2: if Structure(p1) == Structure(p2) then Feeling(p1) == Feeling(p2)
universal_principle = ForAll([p1, p2],
    Implies(
        Structure(p1) == Structure(p2),
        Feeling(p1) == Feeling(p2)
    )
)

# 2. Assumption: Structure(p1) == Structure(p2)
assumption1 = Structure(p1) == Structure(p2)

# 3. Claim (negation of the implication's conclusion): Feeling(p1) != Feeling(p2)
claim = Not(Feeling(p1) == Feeling(p2))

# Set up the solver and assert the formulas
solver = Solver()
solver.add(universal_principle)
solver.add(assumption1)
solver.add(claim)

# Check satisfiability
result = solver.check()
print("Solver result:", result)

# Interpret the result
if result == unsat:
    print("✅ Success! The claim contradicts the Universal Principle (as expected).")
elif result == sat:
    print("❌ Unexpected: the claim is satisfiable alongside the Universal Principle.")
else:
    print("⚠️ Unknown result.")
