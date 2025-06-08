# Stage 1: Consistency Check of the Primitive Axiom R
# ----------------------------------------------------
# Axiom R: ∃ a, b : R(a, b)
# This script uses Z3 to verify that “there exists at least one directed relation”
# is a consistent axiom (i.e., the solver finds a model).

from z3 import Solver, DeclareSort, Consts, Function, BoolSort, Exists

# 1. Declare the sort "Node" and relation R: Node × Node → Bool
Node = DeclareSort('Node')
a, b = Consts('a b', Node)
R = Function('R', Node, Node, BoolSort())

# 2. Build the solver and assert the existential axiom ∃a,b. R(a,b)
solver = Solver()
solver.add(Exists([a, b], R(a, b)))

# 3. Check satisfiability and display a model
result = solver.check()
print("Stage 1: Axiom R satisfiable?", result)
if result.r == 1:  # sat
    print("Model (showing R as an unconstrained relation):", solver.model())
