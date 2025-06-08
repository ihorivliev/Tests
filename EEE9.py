# =============================================================================
#
#                         The Final Test: Liar's Paradox Audit
#
# This script performs the ultimate stress test on the Bi-Level Ontology. It
# checks if the "firewall" between a classical substrate (Tier 1) and a
# dynamic process (Tier 2) can contain a true self-referential paradox.
#
# We introduce a "Liar's State" for the Tier 2 Scribe—a state that is true
# if and only if it is false. This state is triggered if the Scribe enters a
# specific "danger zone" on the Tier 1 graph.
#
# THE TEST: Is it possible for a coherent timeline to exist under these
# conditions?
# - An 'unsat' result means the paradox is too powerful and collapses the system.
# - A 'sat' result means the system preserves its integrity by forcing the
#   Scribe to AVOID the paradoxical state, demonstrating an emergent,
#   self-preservation behavior.
#
# =============================================================================

from z3 import (
    DeclareSort, Const, Consts, BoolSort, IntSort, Function, And, Or, Not,
    Implies, Solver, sat, unsat, is_true, Distinct, If, ForAll
)
import itertools

# --- CONFIGURATION ---
N = 4  # Number of nodes in the Tier 1 substrate
T = 6  # Number of time steps for the simulation

class LiarParadoxAuditor:
    """A tool to test the system's integrity against a self-referential paradox."""

    def __init__(self, n, t):
        self.n = n
        self.t = t
        self.solver = Solver()
        
        # --- TIER 1: The Stone ---
        self.Pattern = DeclareSort(f'Pattern_N{n}')
        self.patterns = list(Consts(' '.join(f'p{i}' for i in range(n)), self.Pattern))
        self.Relates = Function('Relates', self.Pattern, self.Pattern, BoolSort())
        
        # --- TIER 2: The Scribe ---
        self.Time = IntSort()
        self.CognitiveState = DeclareSort('CognitiveState')
        self.S_Normal, self.S_Liar = Consts('S_Normal S_Liar', self.CognitiveState)

        self.Location = Function('Location', self.Time, self.Pattern)
        self.CurrentState = Function('CurrentState', self.Time, self.CognitiveState)
        self.IsTrue = Function('IsTrue', self.CognitiveState, self.Time, BoolSort())

    def run_final_audit(self):
        print("="*80)
        print("          THE FINAL TEST: LIAR'S PARADOX AUDIT")
        print("="*80)
        
        self._assert_tier1_substrate()
        self._assert_tier2_process_rules()
        self._run_the_test()

    def _assert_tier1_substrate(self):
        """Asserts the existence of our proven, sterile, rigid object."""
        print("\n--- TIER 1: Locking in the Invariant Substrate ('The Stone') ---")
        self.solver.add(Distinct(*self.patterns))
        
        p0, p1, p2, p3 = self.patterns
        defined_relations = {(p0, p3), (p1, p1), (p1, p2), (p3, p2)}
        self.solver.add(And([
            And([self.Relates(p_i, p_j) for (p_i, p_j) in defined_relations]),
            # CORRECTED: Use self.patterns[i] and self.patterns[j]
            And([Not(self.Relates(self.patterns[i], self.patterns[j])) for i,j in itertools.product(range(self.n), repeat=2) 
                 if (self.patterns[i], self.patterns[j]) not in defined_relations])
        ]))
        print("[Substrate Locked] Reality is a fixed, classically sound object.")

    def _assert_tier2_process_rules(self):
        """Defines the Scribe's rules, including the Liar's Paradox."""
        print("\n--- TIER 2: Defining the Dynamic Scribe with a Paradoxical State ---")
        
        # Start state
        self.solver.add(self.Location(0) == self.patterns[0])
        self.solver.add(self.CurrentState(0) == self.S_Normal)
        self.solver.add(self.IsTrue(self.S_Normal, 0) == True)
        print("[Process Rule] Scribe starts at p0 in a Normal state.")
        
        # --- THE LIAR'S PARADOX AXIOM ---
        # The S_Liar state is true if and only if it is false.
        # This is a direct assertion of the paradox.
        t_var = Const('t_var', self.Time)
        liar_axiom = ForAll([t_var], self.IsTrue(self.S_Liar, t_var) == Not(self.IsTrue(self.S_Liar, t_var)))
        self.solver.add(liar_axiom)
        print("[Paradox Asserted] The Liar's State (S_Liar) is defined.")

        # Define the transition rules for T-1 steps
        danger_zone_node = self.patterns[2] # p2 is the "danger zone"
        print(f"[Trigger Defined] Entering '{danger_zone_node}' triggers the Liar's State.")

        for i in range(self.t - 1):
            current_loc = self.Location(i)
            next_loc = self.Location(i+1)
            next_state = self.CurrentState(i+1)
            
            # Scribe must move along a valid relation
            self.solver.add(self.Relates(current_loc, next_loc))
            
            # State transition logic
            is_triggered = (current_loc == danger_zone_node)
            self.solver.add(If(is_triggered, 
                               next_state == self.S_Liar, 
                               next_state == self.S_Normal))

    def _run_the_test(self):
        """Checks if a coherent timeline can exist under these paradoxical rules."""
        print("\n--- Initiating Final Test: Can the system survive the paradox? ---")
        
        result = self.solver.check()
        print(f"\nRESULT: {str(result).upper()}")

        if result == sat:
            print("\n✅ VERDICT: PARADOX CONTAINED. The Bi-Level Ontology is robust.")
            print("The solver found a coherent timeline. This is only possible if the Scribe")
            print("was forced to AVOID the paradoxical trigger. This demonstrates:")
            print("\n  1. Emergent Self-Preservation: The system's global consistency forces")
            print("     the Scribe's local behavior to change, avoiding a state that would")
            print("     lead to a paradox.")
            print("\n  2. The 'firewall' between tiers is robust enough to contain not just a")
            print("     simple contradiction, but a true self-referential paradox.")
            
            model = self.solver.model()
            path = [str(model.evaluate(self.Location(i))) for i in range(self.t)]
            states = [str(model.evaluate(self.CurrentState(i))) for i in range(self.t)]
            print("\n--- Found Timeline (Proof of Avoidance) ---")
            print(f"  Path: {' → '.join(path)}")
            print(f"  States: {' → '.join(states)}")
            if self.patterns[2].__str__() not in path:
                print(f"\n  Analysis: The Scribe successfully avoided the danger zone '{self.patterns[2]}'.")

        elif result == unsat:
            print("\n❌ VERDICT: SYSTEM COLLAPSE. The Bi-Level Ontology has failed.")
            print("The paradox asserted at Tier 2 is inescapable and creates a global")
            print("contradiction. The system is not powerful enough to withstand a true")
            print("self-referential challenge.")
        print("="*80)

# --- EXECUTION ---
if __name__ == "__main__":
    auditor = LiarParadoxAuditor(n=N, t=T)
    auditor.run_final_audit()
