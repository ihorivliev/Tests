# existe_validation_report.py

from z3 import (
    DeclareSort, Consts, Function,
    IntSort, BoolSort, Solver,
    Implies, And, Or, Not, ForAll, sat
)

def full_system_test(n):
    # Declare a fresh Pattern sort
    Pattern = DeclareSort(f'Pattern{n}')
    # Create constants P0...P{n-1}
    names = ' '.join(f'P{i}' for i in range(n))
    Patterns = Consts(names, Pattern)
    patterns = list(Patterns)
    # Declare functions
    Structure      = Function('Structure',      Pattern, IntSort())
    Feeling        = Function('Feeling',        Pattern, IntSort())
    Describe       = Function('Describe',       Pattern, Pattern)
    FindSubPattern = Function('FindSubPattern', Pattern, Pattern)
    IsSlice        = Function('IsSlice',        Pattern, BoolSort())
    Interpret      = Function('Interpret',      Pattern, Pattern, IntSort())
    IsObserver     = Function('IsObserver',     Pattern, BoolSort())
    Perceive       = Function('Perceive',       Pattern, Pattern, Pattern, IntSort())
    SelfModel      = Function('SelfModel',      Pattern, Pattern)
    Step           = Function('Step',           Pattern, Pattern)
    # Build constraints
    cons = []
    # 1. Universal Principle
    for p in patterns:
        for q in patterns:
            cons.append(Implies(Structure(p) == Structure(q),
                                Feeling(p) == Feeling(q)))
    # 2. Absolute Combinatorics
    for o in patterns:
        comb = [And(o != o2, Structure(o2) == Structure(o)) for o2 in patterns]
        cons.append(Implies(IsObserver(o), Or(*comb)))
    # 3. Map–Territory & Self-Similarity proxies
    for p in patterns:
        cons.append(Describe(p) != p)
        cons.append(FindSubPattern(p) != p)
        # 4. Slice Functionality (purely Z3; no Python 'if')
    slice_cases = []
    for s1 in patterns:
        for s2 in patterns:
            for x in patterns:
                slice_cases.append(And(
                    s1  != s2,                    # Z3 symbolic test
                    IsSlice(s1), IsSlice(s2),
                    Interpret(s1, x) != Interpret(s2, x)
                ))
    cons.append(Or(*slice_cases))

    # 5. Cognition & Self-Modeling
    for o in patterns:
        for s in patterns:
            for x in patterns:
                cons.append(Implies(And(IsObserver(o), IsSlice(s)),
                                    Perceive(o, s, x) == Interpret(s, x)))
        cons.append(Implies(IsObserver(o), SelfModel(o) != o))
    # 6. Temporal injectivity (2-step)
    for p in patterns:
        cons.append(Step(p) != p)
        cons.append(Step(Step(p)) != p)
        cons.append(Step(Step(p)) != Step(p))
    # Solve
    solver = Solver()
    solver.add(*cons)
    return solver.check()

def emergent_temporal_test():
    # Domain of size 3 for temporal ordering
    Pattern = DeclareSort('PatternT')
    P0, P1, P2 = Consts('P0 P1 P2', Pattern)
    patterns = [P0, P1, P2]
    Step = Function('Step', Pattern, Pattern)
    cons = []
    # Injectivity
    for p in patterns:
        cons += [Step(p) != p,
                 Step(Step(p)) != p,
                 Step(Step(p)) != Step(p)]
    # Path and EarlierThan unrolled
    def Path(p0, pi, k):
        if k == 0: return pi == p0
        if k == 1: return pi == Step(p0)
        return pi == Step(Step(p0))
    def Earlier(p0, pi, pj):
        return Or(
            And(Path(p0, pi, 0), Path(p0, pj, 1)),
            And(Path(p0, pi, 0), Path(p0, pj, 2)),
            And(Path(p0, pi, 1), Path(p0, pj, 2))
        )
    for p0 in patterns:
        for pi in patterns:
            cons.append(Not(Earlier(p0, pi, pi)))
            for pj in patterns:
                cons.append(Implies(Earlier(p0, pi, pj),
                                    Not(Earlier(p0, pj, pi))))
                for pk in patterns:
                    cons.append(Implies(And(Earlier(p0, pi, pj),
                                            Earlier(p0, pj, pk)),
                                        Earlier(p0, pi, pk)))
    solver = Solver()
    solver.add(*cons)
    return solver.check()

def meta_theory_test():
    # Domain of size 3 for sentences
    Sentence = DeclareSort('SentenceM')
    S0, S1, S2 = Consts('S0 S1 S2', Sentence)
    Prov = Function('Prov', Sentence, BoolSort())
    TrueStmt = Function('TrueStmt', Sentence, BoolSort())
    Decide = Function('Decide', Sentence, BoolSort())
    # Incompleteness
    solver1 = Solver()
    ax1 = ForAll([S0], Implies(Prov(S0), TrueStmt(S0)))
    axG = And(TrueStmt(S2), Not(Prov(S2)))
    solver1.add(ax1, axG)
    inc = solver1.check()
    # Undecidability
    solver2 = Solver()
    ax2 = ForAll([S0], Decide(S0) == TrueStmt(S0))
    diag = TrueStmt(S2) == Not(Decide(S2))
    solver2.add(ax2, diag)
    und = solver2.check()
    return inc, und

if __name__ == '__main__':
    print("=== Full-System + 2-step temporal injectivity (n=3) ===")
    res = full_system_test(3)
    print("Result:", res)
    print("✅ SAT" if res == sat else "❌ Unexpected UNSAT/UNKNOWN")
    print("\n=== Emergent Temporal Ordering ===")
    res = emergent_temporal_test()
    print("Result:", res)
    print("✅ Valid order" if res == sat else "❌ Failed")
    print("\n=== Meta-Theoretic Walls ===")
    inc, und = meta_theory_test()
    print("Incompleteness Test:", inc, " (sat expected)")
    print("Undecidability Test:", und, " (unsat expected)")
    if inc == sat and und != sat:
        print("✅ Meta-theoretic walls hold")
    else:
        print("❌ Meta-theory anomaly")
    print("\n=== Scaling Full-System ===")
    for n in (10, 30):
        print(f"n = {n:2d} ->", full_system_test(n))
