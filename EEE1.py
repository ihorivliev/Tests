# =============================================================================
#
#                  Deep Sanity Check: Rigidity & Existence Audit (v2)
#
# This script is not an exploration. It is a targeted, deep sanity check to
# answer one question: Can the proposed "sterile and novel" object, defined
# by a set of rigid constraints, actually exist?
#
# This version corrects a NameError for the missing 'is_true' import.
#
# =============================================================================

from z3 import (
    DeclareSort, Consts, BoolSort, Function, And, Or, Not, Implies,
    Solver, sat, unsat, Distinct, Sum, If, is_true
) # <-- CORRECTED: Added 'is_true' to the import list.
import itertools

# --- CONFIGURATION ---
N = 4  # A small universe to keep the problem tractable.

class RigidityExistenceAuditor:
    """A tool to search for a single instance of a maximally constrained object."""

    def __init__(self, n):
        self.n = n
        self.solver = Solver()
        
        # --- Formalize the Universe ---
        self.Pattern = DeclareSort(f'Pattern_N{n}')
        self.patterns = list(Consts(' '.join(f'p{i}' for i in range(n)), self.Pattern))
        self.Relates = Function('Relates', self.Pattern, self.Pattern, BoolSort())

    def run_sanity_check(self):
        """Executes the single, decisive search for a valid model."""
        print("="*80)
        print("          DEEP SANITY CHECK: RIGIDITY & EXISTENCE AUDIT")
        print("="*80)
        print(f"Searching for a single, unique, rigid object with N={self.n} nodes...\n")

        self._add_axioms()
        self._check_for_existence()

    def _add_axioms(self):
        """Asserts all constraints that define the sterile object."""
        
        # --- Axiom of Unique & Finite Existence ---
        self.solver.add(Distinct(*self.patterns))
        print("[Axiom Asserted] Finite Structure: N patterns are distinct.")

        # --- Axiom of Arbitrary Constraint (The "Key") ---
        out_degrees_constraint = [1, 2, 0, 1]
        print(f"[Axiom Asserted] Arbitrary Constraint: Required out-degrees are {out_degrees_constraint}")
        for i, p_i in enumerate(self.patterns):
            degree = Sum([If(self.Relates(p_i, p_j), 1, 0) for p_j in self.patterns])
            self.solver.add(degree == out_degrees_constraint[i])
            
        # --- Axiom of Total Rigidity ---
        print("[Axiom Asserted] Total Rigidity: Forbidding all non-trivial symmetries.")
        
        all_perms = list(itertools.permutations(range(self.n)))
        identity_perm = tuple(range(self.n))
        
        rigidity_constraints = []
        for perm in all_perms:
            if perm == identity_perm:
                continue
            
            perm_map = {self.patterns[i]: self.patterns[perm[i]] for i in range(self.n)}
            
            is_automorphism = And([self.Relates(p1, p2) == self.Relates(perm_map[p1], perm_map[p2])
                                  for p1, p2 in itertools.product(self.patterns, repeat=2)])
            
            rigidity_constraints.append(Not(is_automorphism))
            
        self.solver.add(And(rigidity_constraints))


    def _check_for_existence(self):
        """Runs the solver and reports the result."""
        print("\n--- Initiating Search ---")
        result = self.solver.check()
        
        print(f"\nRESULT: {str(result).upper()}")
        
        if result == sat:
            print("\n✅ VERDICT: PROOF OF CONCEPT SUCCESSFUL. A non-delusional object exists.")
            print("The axioms are coherent and admit at least one solution. The following is a")
            print("concrete example of a finite, rigid graph satisfying all constraints:")
            
            model = self.solver.model()
            relations = [f"{p1} → {p2}" 
                         for p1, p2 in itertools.product(self.patterns, repeat=2) 
                         if is_true(model.evaluate(self.Relates(p1, p2)))]
            print("\n--- CONCRETE MODEL ---")
            print(f"  - Relations: {', '.join(relations) or 'None'}")
            print("----------------------")

        elif result == unsat:
            print("\n❌ VERDICT: PROOF OF INCOHERENCE. The proposed system is a contradiction.")
            print("The combination of axioms—specifically the arbitrary degree constraint and")
            print("the demand for total rigidity—are mutually exclusive. No such object can exist.")

        else:
            print("\n⚠️ VERDICT: UNKNOWN. The solver timed out or the problem is too complex.")
            print("This does not prove or disprove existence, but suggests the problem is")
            print("computationally very difficult.")

# --- EXECUTION ---
if __name__ == "__main__":
    auditor = RigidityExistenceAuditor(n=N)
    auditor.run_sanity_check()
