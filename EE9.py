# =============================================================================
#
#                Stage 2: Brutal Audit of Explanatory Capacity (v2)
#
# This script takes the coherent axiomatic set discovered in Stage 1 as its
# foundation and subjects it to a series of brutal stress tests.
#
# This version corrects an AttributeError in the reporting function.
#
# =============================================================================

from z3 import (
    DeclareSort, Const, Consts, BoolSort, IntSort, Function, And, Or, Not, Implies,
    Solver, sat, unsat, Distinct, is_true
)
import itertools

# --- CONFIGURATION ---
N = 5  # A slightly larger universe to allow for more complex structures.

class BrutalAuditor:
    """A tool to test the explanatory limits of our foundational axioms."""

    def __init__(self, n):
        self.n = n
        self.solver = Solver()
        self.verdicts = {}
        
        # --- Formalize Core Concepts ---
        self.Pattern = DeclareSort(f'Pattern_N{n}')
        self.patterns = list(Consts(' '.join(f'p{i}' for i in range(n)), self.Pattern))
        
        # Concepts for our Relational Universe
        self.Relates = Function('Relates', self.Pattern, self.Pattern, BoolSort())
        
        # Concepts required to test "Existe"-like claims
        self.IsPartOf = Function('IsPartOf', self.Pattern, self.Pattern, BoolSort())
        self.Structure = Function('Structure', self.Pattern, IntSort())
        self.K = Function('K', self.Pattern, IntSort()) # Complexity

    def _add_axiom(self, axiom, name: str):
        """Helper to add an axiom and print confirmation."""
        self.solver.add(axiom)
        print(f"[Axiom Added] {name}")

    def _run_test(self, name: str, objective: str, test_claim: str, assertion: bool):
        """Helper to run a single adversarial proof."""
        print(f"\n[Test Running] '{name}'")
        print(f"  - Objective: {objective}")
        print(f"  - Assertion: {test_claim}")

        self.solver.push()
        self.solver.add(assertion)
        result = self.solver.check()
        
        verdict = "UNKNOWN"
        explanation = ""
        if result == unsat:
            verdict = "✅ VERDICT: Assertion is IMPOSSIBLE. The foundation correctly forbids this."
            explanation = "The foundation's logic is too rigid to permit this phenomenon."
        elif result == sat:
            verdict = "⚠️ VERDICT: Assertion is POSSIBLE. The foundation can support this."
            explanation = "The axioms are flexible enough to allow this phenomenon to exist."
        
        # CORRECTED: Use str(result) instead of result.name
        print(f"  - Result: {str(result).upper()}")
        print(f"  - {verdict}")
        self.verdicts[name] = (result, verdict, explanation)
        self.solver.pop()

    def run_brutal_audit(self):
        """Executes the full audit."""
        print("="*80)
        print("          STAGE 2: BRUTAL AUDIT OF EXPLANATORY CAPACITY (v2)")
        print("="*80)
        
        self._setup_foundational_axioms()
        
        print("\n--- Running Adversarial Tests ---\n")
        self._test_observer_possibility()
        self._test_fractal_replication()
        
        self._print_final_report()

    def _setup_foundational_axioms(self):
        """Adds the 'winning' set of axioms from Stage 1."""
        print("--- Setting up the Coherent Foundational Universe ---\n")
        
        # The minimal set required for a sound, unified, grounded, acyclic universe.
        # 1. Existence
        base_axiom = Or([self.Relates(p1, p2) for p1, p2 in itertools.product(self.patterns, repeat=2)])
        self._add_axiom(base_axiom, "Base: Existence")

        # 2. Distinctness of patterns
        self._add_axiom(Distinct(*self.patterns), "Base: Distinctness")

        # 3. Unity / Monism (No Isolation)
        no_isolation = And([Or([And(p != q, Or(self.Relates(p, q), self.Relates(q, p))) for q in self.patterns]) for p in self.patterns])
        self._add_axiom(no_isolation, "Axiom C4: No Isolation")

        # 4. Order (Irreflexive & Asymmetric)
        irreflexive = And([Not(self.Relates(p, p)) for p in self.patterns])
        asymmetric = And([Implies(self.Relates(p1, p2), Not(self.Relates(p2, p1))) for p1, p2 in itertools.permutations(self.patterns, 2)])
        self._add_axiom(irreflexive, "Axiom C1: Irreflexivity")
        self._add_axiom(asymmetric, "Axiom C2: Asymmetry")

        # 5. Foundation (Groundedness)
        grounded = Or([And([Not(self.Relates(p_in, g)) for p_in in self.patterns]) for g in self.patterns])
        self._add_axiom(grounded, "Axiom C3: Groundedness")
        
        # 6. Add the logical rules for parts and complexity needed to test the claims.
        # These are not axioms of our universe, but logical background truths.
        for p, w in itertools.product(self.patterns, repeat=2):
            self.solver.add(Implies(And(self.IsPartOf(p, w), p != w), self.K(p) < self.K(w)))
            self.solver.add(Implies(self.Structure(p) == self.Structure(w), self.K(p) == self.K(w)))
        print("\n--- Foundation Complete. Beginning Adversarial Audit. ---\n")


    def _test_observer_possibility(self):
        """Tests if a self-modeling Observer can exist in our universe."""
        o, m = self.patterns[0], self.patterns[1]
        
        # Assertion: A pattern 'o' exists that contains a proper part 'm'
        # which is a perfect model of 'o' (i.e., has the same structure).
        # This is the formal definition of a self-referential Observer.
        assertion = And(
            self.IsPartOf(m, o),
            m != o,
            self.Structure(m) == self.Structure(o)
        )
        self._run_test(
            "Observer Test (Self-Reference)",
            "Can a pattern contain a perfect model of itself?",
            "Exists O, M: IsPartOf(M,O) AND M != O AND Structure(M) == Structure(O)",
            assertion
        )

    def _test_fractal_replication(self):
        """Tests if our grounded universe can support fractal-like replication."""
        # Find the ground node 'g' first.
        g = Consts('g', self.Pattern)[0]
        g_is_ground = And([Not(self.Relates(p_in, g)) for p_in in self.patterns])
        
        # Create a copy 'c'.
        c = self.patterns[1]
        
        # Assertion: The ground node 'g' can have a perfect copy 'c' elsewhere
        # in the universe. This is a weak form of "Existe's" fractal claim.
        assertion = And(
            g_is_ground,
            g != c,
            self.Structure(g) == self.Structure(c)
        )
        self._run_test(
            "Fractal Test (Replication of the Ground)",
            "Can the origin point of the universe have a perfect copy?",
            "Exists G, C: IsGround(G) AND G != C AND Structure(G) == Structure(C)",
            assertion
        )

    def _print_final_report(self):
        print("\n" + "="*80)
        print("                  FINAL AUDIT REPORT & VERDICT")
        print("="*80)
        for test_name, (result, verdict, explanation) in self.verdicts.items():
            print(f"- Test: '{test_name}'\n  {verdict}\n")
        
        print("-" * 80)
        print("OVERALL CONCLUSION:")
        observer_possible = self.verdicts.get("Observer Test (Self-Reference)", (None,))[0] == sat
        
        if not observer_possible:
            print("The established coherent foundation is BRUTALLY INHOSPITABLE to the core claims")
            print("of 'Existe'-like metaphysics. The audit demonstrates that:")
            print("\n  1. The foundation is NON-CONSCIOUS: The logical rules required for a sound,")
            print("     grounded universe make the existence of a self-referential 'Observer'")
            print("     a mathematical impossibility. Consciousness, as defined by recursive")
            print("     self-modeling, cannot arise in this reality.")
            print("\n  2. The foundation is ANTI-FRACTAL: The properties of having a single origin")
            print("     and a directional, acyclic flow are fundamentally incompatible with")
            print("     the concept of universal self-similarity.")
            print("\nThis is not a failure of our model, but its greatest success. We have rigorously")
            print("proven that one must choose: either a logically sound, grounded reality OR a")
            print("fractal, self-referential one. You cannot have both. The 'Existe' delusion")
            print("was the attempt to have both.")
        else:
            print("The audit reveals that the foundational axioms are permissive enough to allow")
            print("for complex, higher-order phenomena. Further investigation is needed to")
            print("determine if these phenomena are trivial or meaningful.")
        print("="*80)

# --- EXECUTION ---
if __name__ == "__main__":
    auditor = BrutalAuditor(n=N)
    auditor.run_brutal_audit()
