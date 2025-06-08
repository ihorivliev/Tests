from z3 import (
    DeclareSort, Consts, Function,
    Solver, ForAll, Implies, Not, Or, sat, And, BoolSort
)

# --- Domain: 3 Sentences ---
Sentence = DeclareSort('Sentence')
S0, S1, S2 = Consts('S0 S1 S2', Sentence)

# --- Predicates ---
Prov     = Function('Prov',     Sentence, BoolSort())
TrueStmt = Function('TrueStmt', Sentence, BoolSort())

# --- Axiom: Provable implies True ---
axiom_prov = ForAll([S0], Implies(Prov(S0), TrueStmt(S0)))

# --- Gödel Sentence G: assume it's S2 ---
G = S2
axiom_G = And(TrueStmt(G), Not(Prov(G)))

# --- Universal Decider (Turing) ---
Decide = Function('Decide', Sentence, BoolSort())
axiom_decider = ForAll([S0], Decide(S0) == TrueStmt(S0))

# --- Diagonal Sentence: True(G) == ¬Decide(G) ---
axiom_diag = TrueStmt(G) == Not(Decide(G))

# --- Solver ---
solver = Solver()
solver.add(axiom_prov, axiom_G)
# Incompleteness check:
inc_result = solver.check()
print("=== Incompleteness Test ===", inc_result)

solver.reset()
solver.add(axiom_decider, axiom_diag)
und_result = solver.check()
print("=== Undecidability Test ===", und_result)

if inc_result == sat:
    print("✅ Incompleteness: true but unprovable sentence is consistent.")
else:
    print("❌ Incompleteness failed.")

if und_result == sat:
    print("❌ Unexpected: universal decider found.")
else:
    print("✅ Undecidability: no universal decider.")
