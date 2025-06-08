from z3 import (
    DeclareSort, Const, Function, ForAll, Solver, Not, sat
)

# --- Sort and Function Declarations ---
Pattern   = DeclareSort('Pattern')
Describe  = Function('Describe', Pattern, Pattern)

# --- Variable Declaration ---
p = Const('p', Pattern)

# --- Axiom: No description equals its original token ---
# ∀p: Describe(p) ≠ p
axiom_map_territory = ForAll([p], Not(Describe(p) == p))

# --- Solver Setup ---
solver = Solver()
solver.add(axiom_map_territory)

# --- Check Consistency ---
result = solver.check()
print("--- Map–Territory Gap Consistency Check ---")
print("Solver result:", result)
if result == sat:
    print("✅ Success: Axiom is consistent (SAT).")
else:
    print("❌ Unexpected: Axiom is inconsistent (UNSAT).")
