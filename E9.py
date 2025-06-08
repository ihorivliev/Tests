import itertools

try:
    from z3 import (
        DeclareSort, Function, Const, ForAll,
        Solver, Not, BoolSort, sat
    )

    # --- Sort Declaration ---
    Sentence = DeclareSort('Sentence')

    # --- Functions ---
    TrueStmt = Function('TrueStmt', Sentence, BoolSort())
    Decide   = Function('Decide',   Sentence, BoolSort())

    # --- Constants ---
    s = Const('s', Sentence)
    G = Const('G', Sentence)

    # --- Axiom: Universal Decider ---
    axiom_decider = ForAll([s], Decide(s) == TrueStmt(s))

    # --- Diagonal Sentence ---
    diag_sentence = TrueStmt(G) == Not(Decide(G))

    # --- Solver Setup ---
    solver = Solver()
    solver.add(axiom_decider)
    solver.add(diag_sentence)

    # --- Check ---
    result = solver.check()

    print("--- Turing Undecidability (Solver) ---")
    print("Solver result:", result)
    if result == sat:
        print("❌ Unexpected: Found a model with a universal decider.")
    else:
        print("✅ As expected, UNSAT: no universal decider can exist.")

except ModuleNotFoundError:
    # Fallback simulation on a single sentence domain
    solutions = []
    domain = [False, True]
    for d_val, t_val in itertools.product(domain, repeat=2):
        # Constraints: (d_val == t_val) AND (t_val == not d_val)
        if (d_val == t_val) and (t_val == (not d_val)):
            solutions.append((d_val, t_val))
    print("--- Turing Undecidability (Simulated) ---")
    if solutions:
        print("❌ Unexpected: Found satisfying assignments", solutions)
    else:
        print("✅ As expected, no satisfying assignments: UNSAT (no universal decider).")
