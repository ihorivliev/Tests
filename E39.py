# =============================================================================
#
#                 Existe: The Adversarial Audit & Falsification
#
# This script subjects the formalized "Existe" framework to a no-mercy stress
# test designed to reveal internal contradictions. Unlike a validation suite
# that confirms theorems, this audit actively searches for paradoxes that can
# be generated from the treatise's own axioms.
#
# The central test, the "Self-Similarity Contradiction," targets the direct
# conflict between the philosophical claim of Absolute Self-Similarity and the
# logical necessity of part-whole relationships. A "pass" on this test (a
# 'sat' result) signifies a critical failure of the framework's logical soundness.
#
# =============================================================================

from z3 import (
    DeclareSort, Consts, IntSort, BoolSort, Function,
    And, Or, Not, Implies, Solver, sat, unsat, Distinct
)
import itertools

# --- CONFIGURATION ---
# The size of our bounded universe. N=5 is sufficient to demonstrate the paradox.
N = 5

# =============================================================================
# 1. THE FORMAL MODEL: Faithfully Implementing the "Existe" Universe
# =============================================================================

class ExisteModel:
    """A class to encapsulate the formal definition of the Existe universe,
       including all axioms from the treatise and the previous validation report.
    """
    
    def __init__(self, n):
        """Initializes the universe with n patterns and defines all concepts."""
        self.n = n
        
        # --- Sorts and Constants ---
        self.Pattern = DeclareSort(f'Pattern_N{n}')
        self.patterns = Consts(' '.join(f'P{i}' for i in range(n)), self.Pattern)
        
        # --- Core Concepts as Uninterpreted Functions ---
        self.Structure = Function('Structure', self.Pattern, IntSort()) # An abstract ID for a pattern's structure
        self.K = Function('K', self.Pattern, IntSort()) # Kolmogorov Complexity
        self.IsPartOf = Function('IsPartOf', self.Pattern, self.Pattern, BoolSort())

        # Define axioms based on the treatise and the "successful" validation report
        self.axioms = self._define_axioms()

    def _define_axioms(self):
        """
        Defines all foundational axioms using pure Z3 constructs.
        These are taken directly from the treatise's logic and the previous
        "successful" validation, ensuring a fair test.
        """
        axioms = [Distinct(*self.patterns)]
        
        p_space2 = list(itertools.product(self.patterns, repeat=2))
        p_space3 = list(itertools.product(self.patterns, repeat=3))

        # --- AXIOM SET ---
        
        # 1. Structure implies Complexity: If two patterns have the same structure,
        #    they must have the same complexity. This is a core realist claim.
        for p1, p2 in p_space2:
            axioms.append(Implies(self.Structure(p1) == self.Structure(p2), self.K(p1) == self.K(p2)))

        # 2. Transitivity of "IsPartOf": If A is part of B, and B is part of C,
        #    then A is part of C. This makes the hierarchy logical.
        for a, b, c in p_space3:
            axioms.append(Implies(And(self.IsPartOf(a, b), self.IsPartOf(b, c)), self.IsPartOf(a, c)))

        # 3. Structural Subordination (Derived Theorem): A *proper* part (p != w)
        #    MUST be less complex than the whole. K(p) < K(w). This is a
        #    fundamental rule of information theory and logic.
        for p, w in p_space2:
             axioms.append(Implies(And(self.IsPartOf(p, w), p != w), self.K(p) < self.K(w)))
            
        return axioms

# =============================================================================
# 2. THE ADVERSARIAL AUDIT: The No-Mercy Stress Test
# =============================================================================

class AdversarialAuditor:
    """Executes a single, decisive test to find a contradiction."""
    
    def __init__(self, model):
        self.model = model

    def run_falsification_test(self):
        """The core test designed to break the system."""
        print("--- Starting Adversarial Audit & Falsification ---")
        self.test_self_similarity_contradiction()
        
    def _run_adversarial_check(self, name, adversarial_claim):
        """
        Helper function to run the adversarial check.
        Unlike validation, here 'sat' means the system is broken.
        """
        solver = Solver()
        solver.add(self.model.axioms)
        solver.add(adversarial_claim)
        
        result = solver.check()
        
        print("\n" + "="*70)
        print(f"  ADVERSARIAL TEST: '{name}'")
        print("="*70)
        print("  GOAL: Can the axioms permit a logically paradoxical state of affairs?")
        print(f"  PARADOXICAL CLAIM: '{adversarial_claim}'")
        print(f"  SOLVER RESULT: {result}")
        print("-" * 70)

        if result == sat:
            print("  🚨 VERDICT: TEST FAILED. The 'Existe' framework is INCONSISTENT.")
            print("  EXPLANATION: The solver found a concrete example (a 'model') where")
            print("               the paradoxical claim is TRUE under the system's own axioms.")
            print("               This proves the framework is logically unsound.")
            model = solver.model()
            print("\n  --- COUNTEREXAMPLE MODEL ---")
            print(f"  A world where the paradox holds:")
            print(f"  - Whole Pattern: {model.evaluate(adversarial_claim.children()[0].children()[1])}")
            print(f"  - Paradoxical Part: {model.evaluate(adversarial_claim.children()[0].children()[0])}")
            k_whole = model.evaluate(self.model.K(adversarial_claim.children()[0].children()[1]))
            k_part = model.evaluate(self.model.K(adversarial_claim.children()[0].children()[0]))
            print(f"  - Complexity of Whole (K_whole): {k_whole}")
            print(f"  - Complexity of Part (K_part): {k_part}")
            print("\n  FATAL CONTRADICTION:")
            print(f"  The model requires K_part ({k_part}) to be EQUAL to K_whole ({k_whole}) because their structures are identical.")
            print(f"  Simultaneously, it requires K_part ({k_part}) to be LESS THAN K_whole ({k_whole}) because it's a proper part.")
            print(f"  A number cannot be both equal to and less than another. The system is broken.")

        elif result == unsat:
            print("  ✅ VERDICT: TEST PASSED. The framework is consistent on this point.")
            print("  EXPLANATION: The axioms successfully prohibit this specific paradox from occurring.")
        else:
            print("  ⚠️ VERDICT: UNKNOWN. The solver could not determine the result.")
        print("="*70)


    def test_self_similarity_contradiction(self):
        """
        This test formalizes the core philosophical claim of self-similarity
        and shows it contradicts the logical axioms.
        """
        # Let's pick two distinct patterns from our universe.
        P_part = self.model.patterns[0]
        P_whole = self.model.patterns[1]
        
        # THE ADVERSARIAL CLAIM (The Paradoxical Scenario):
        # We ask the solver: "Can a world exist where P_part is a *proper part*
        # of P_whole, but it also has the *same structure* as P_whole?"
        # This is the most charitable formalization of the "self-similarity" claim.
        adversarial_claim = And(
            # Condition 1: P_part is a proper part of P_whole.
            self.model.IsPartOf(P_part, P_whole), 
            P_part != P_whole,
            
            # Condition 2: P_part has the same structure as P_whole.
            self.model.Structure(P_part) == self.model.Structure(P_whole)
        )
        
        self._run_adversarial_check("Self-Similarity Contradiction", adversarial_claim)

# =============================================================================
# 3. EXECUTION
# =============================================================================
if __name__ == "__main__":
    # We instantiate the model with its own rules.
    model = ExisteModel(N)
    
    # We create the auditor to stress-test those rules.
    auditor = AdversarialAuditor(model)
    
    # Run the single, decisive test.
    auditor.run_falsification_test()
