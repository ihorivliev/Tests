# Stage 2: Adding Acyclicity to Axiom R
# --------------------------------------
# Axiom R: ∃a,b. R(a,b)
# Axiom A: No cycles of length 1, 2, or 3 in R
#   1. ∀x. ¬R(x,x)
#   2. ∀x,y. ¬(R(x,y) ∧ R(y,x))
#   3. ∀x,y,z. ¬(R(x,y) ∧ R(y,z) ∧ R(z,x))

from z3 import (
    Solver, DeclareSort, Consts, Function, BoolSort,
    Exists, ForAll, Not, And
)

# 1. Declare the sort and relation
Node = DeclareSort('Node')
a, b, x, y, z = Consts('a b x y z', Node)
R = Function('R', Node, Node, BoolSort())

# 2. Build solver with axioms
solver = Solver()

# Axiom R: at least one directed edge
solver.add(Exists([a, b], R(a, b)))

# Axiom A1: no self-edge
solver.add(ForAll([x], Not(R(x, x))))

# Axiom A2: no 2-cycle
solver.add(ForAll([x, y], Not(And(R(x, y), R(y, x)))))

# Axiom A3: no 3-cycle
solver.add(ForAll([x, y, z], Not(And(R(x, y), R(y, z), R(z, x)))))

# 3. Check satisfiability
result = solver.check()
print("Stage 2: Axioms (R + Acyclicity) satisfiable?", result)
