"""
Top-tier Stress-Testing Suite for the 'Existe' Metaphysical Framework
Requires: z3-solver (install via `pip install z3-solver`)

This script systematically encodes a rich subset of the framework’s claimed concepts:
  - Distinction (at least two distinct patterns)
  - Structural Subordination
  - Temporal Linearity
  - Self-Similarity (fractal copy requirement)
It then runs adversarial queries to Z3 to try and find:
  * A concrete model of the axioms
  * Counterexamples to fractality
  * Counterexamples to self-similarity
  * Counterexamples to map–territory (perfect self-model) claims

If any check returns `sat`, the corresponding property is under-constrained or fails.
"""

from z3 import (
    Solver, DeclareSort, Const, Function, IntSort, BoolSort,
    Implies, And, Or, Not, Distinct, Exists
)
from itertools import product

def build_model(N):
    Pattern = DeclareSort('Pattern')
    patterns = [Const(f'p{i}', Pattern) for i in range(N)]
    # Uninterpreted functions
    Structure   = Function('Structure', Pattern, IntSort())
    K           = Function('K', Pattern, IntSort())
    IsPartOf    = Function('IsPartOf', Pattern, Pattern, BoolSort())
    Step        = Function('Step', Pattern, Pattern)
    SelfSimilar = Function('SelfSimilar', Pattern, BoolSort())

    axioms = []
    # 1. Δ: at least two distinct patterns
    axioms.append(Distinct(patterns[0], patterns[1]))

    # 2. Structural Subordination: (IsPartOf(p,q) ∧ p≠q) → K(p) < K(q)
    for p, q in product(patterns, repeat=2):
        axioms.append(Implies(And(IsPartOf(p, q), p != q), K(p) < K(q)))

    # 3. Temporal Linearity: (Step(p)==Step(q)) → p == q
    for p, q in product(patterns, repeat=2):
        axioms.append(Implies(Step(p) == Step(q), p == q))

    # 4. Self-Similarity: SelfSimilar(p) ↔ ∃q. (q≠p ∧ Structure(p)==Structure(q))
    for p in patterns:
        copies = [And(q != p, Structure(p) == Structure(q)) for q in patterns]
        axioms.append(SelfSimilar(p) == Or(*copies))

    return patterns, Structure, K, IsPartOf, Step, SelfSimilar, axioms

def run_tests(N=3):
    ps, Structure, K, IsPartOf, Step, SelfSimilar, axioms = build_model(N)

    print("=== Base Axiom Consistency ===")
    s0 = Solver(); s0.add(*axioms)
    print("Axioms satisfiable? →", s0.check())

    print("\n=== Fractality Check ===")
    # Try to falsify fractality: ∃p. ¬SelfSimilar(p)
    s1 = Solver(); s1.add(*axioms)
    p = ps[0]
    s1.add(Not(SelfSimilar(p)))
    print(f"Can p0 lack a fractal copy? →", s1.check())

    print("\n=== Self-Similarity Existence ===")
    # Check ∃p. SelfSimilar(p); must be sat if fractality holds
    s2 = Solver(); s2.add(*axioms)
    s2.add(SelfSimilar(ps[1]))
    print(f"Can p1 have a copy? →", s2.check())

    print("\n=== Map–Territory (Perfect Self-Model) Check ===")
    # Test existence of a “perfect description”: ∃p≠desc. Structure(desc)==Structure(p)
    desc = Const('desc', ps[0].sort())
    s3 = Solver(); s3.add(*axioms)
    s3.add(Exists([desc], And(Distinct(desc, *ps), Structure(desc) == Structure(ps[0]))))
    print("Can one ‘describe’ p0 as a distinct pattern? →", s3.check())

    print("\n=== 2-Cycle Exclusion (Stress Test) ===")
    # Force a 2-cycle in IsPartOf( p0↔p1 )
    s4 = Solver(); s4.add(*axioms)
    s4.add(And(IsPartOf(ps[0], ps[1]), IsPartOf(ps[1], ps[0]), ps[0] != ps[1]))
    print("2-cycle allowed? →", s4.check())

    print("\n=== Time-Merging Exclusion (Stress Test) ===")
    # Force Step(p0)==Step(p1) but p0≠p1
    s5 = Solver(); s5.add(*axioms)
    s5.add(ps[0] != ps[1], Step(ps[0]) == Step(ps[1]))
    print("Time merging allowed? →", s5.check())

if __name__ == "__main__":
    run_tests(N=3)

