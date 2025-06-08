# Import necessary components from pySMT
from pysmt.shortcuts import Symbol, Equals, And, ForAll, Implies, Not, Solver
from pysmt.typing import INT, Type, FunctionType

# 1. Define the custom sort "Pattern"
Pattern = Type("Pattern")

# 2. Declare the function symbols
Structure = Symbol("Structure", FunctionType(INT, (Pattern,)))
Feeling = Symbol("Feeling", FunctionType(INT, (Pattern,)))

# 3. Declare variables to represent Token-Patterns
p1 = Symbol("p1", Pattern)
p2 = Symbol("p2", Pattern)

# 4. State the axioms and principles
universal_principle = ForAll([p1, p2],
    Implies(
        Equals(Structure(p1), Structure(p2)),
        Equals(Feeling(p1), Feeling(p2))
    )
)

# 5. Formulate a test case
assumption1 = Equals(Structure(p1), Structure(p2))
claim = Not(Equals(Feeling(p1), Feeling(p2)))

# 6. Create a solver and run the check
with Solver(name="z3") as solver:
    solver.add_assertion(universal_principle)
    solver.add_assertion(assumption1)
    solver.add_assertion(claim)

    # --- CORRECTED LINE ---
    # To check the stack of assertions, use solve().
    # It returns True if the system is SAT (satisfiable) and False if UNSAT (unsatisfiable/contradictory).
    result_is_sat = solver.solve()

    print(f"Is the system satisfiable with the claim? {result_is_sat}")

    if not result_is_sat:
        print("✅ Success! The system is UNSATISFIABLE.")
        print("This means the claim creates a logical contradiction with the axioms, as expected.")