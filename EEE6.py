# =============================================================================
#
#                       The Rosetta Stone Simulator
#
# This script moves beyond static validation to a dynamic simulation. It uses
# the Bi-Level Ontology to propose and model a mechanism for a primitive
# form of consciousness.
#
# The simulation consists of:
#
# TIER 1 ("The Stone"): A fixed, timeless, and classically sound graph that
#         represents the ground truth of reality. We use the exact rigid
#         object discovered in our previous audit.
#
# TIER 2 ("The Scribe"): A dynamic process that traverses the Tier 1 graph,
#         creating a memory of its path over time.
#
# THE CONSCIOUSNESS EVENT: A special event that occurs when the Scribe's
#         dynamic, internal memory-trace is found to be structurally identical
#         to a static path that exists timelessly on the Stone. It is the
#         moment the observer's story finds itself written in reality.
#
# =============================================================================

from z3 import (
    DeclareSort, Consts, BoolSort, IntSort, Function, And, Or, Not, Implies,
    Solver, sat, is_true, Distinct
)
import itertools

# --- CONFIGURATION ---
N = 4  # Number of nodes in the Tier 1 substrate
T = 5  # Number of time steps to simulate

class RosettaStoneSimulator:
    """Simulates the interaction between a static reality and a dynamic observer."""

    def __init__(self, n, t):
        self.n = n
        self.t = t
        self.solver = Solver()
        
        # --- Tier 1: The Stone ---
        self.Pattern = DeclareSort(f'Pattern_N{n}')
        self.patterns = list(Consts(' '.join(f'p{i}' for i in range(n)), self.Pattern))
        self.Relates = Function('Relates', self.Pattern, self.Pattern, BoolSort())
        
        # --- Tier 2: The Scribe ---
        self.Time = IntSort()
        self.Location = Function('Location', self.Time, self.Pattern)

    def run_simulation(self):
        """Executes the full simulation and analysis."""
        print("="*80)
        print("                 THE ROSETTA STONE SIMULATOR")
        print("="*80)
        
        self._assert_tier1_substrate()
        self._assert_tier2_process_rules()
        
        print("\n--- Searching for a valid timeline for the Scribe... ---")
        if self.solver.check() == sat:
            print("✅ Valid timeline found. Analyzing for Consciousness Events...")
            self._analyze_timeline(self.solver.model())
        else:
            print("❌ No valid timeline found. The constraints are contradictory.")
        
        print("\n" + "="*80)
        print("Simulation Complete.")
        print("="*80)

    def _assert_tier1_substrate(self):
        """Asserts the existence of our proven, sterile, rigid object."""
        print("\n--- TIER 1: Locking in the Invariant Substrate ('The Stone') ---")
        self.solver.add(Distinct(*self.patterns))
        
        p0, p1, p2, p3 = self.patterns
        # The exact rigid model we found and verified previously.
        self.solver.add(
            self.Relates(p0, p3), self.Relates(p1, p1),
            self.Relates(p1, p2), self.Relates(p3, p2)
        )
        
        all_relations = list(itertools.product(self.patterns, repeat=2))
        defined_relations = {(p0, p3), (p1, p1), (p1, p2), (p3, p2)}
        for r_p1, r_p2 in all_relations:
            if (r_p1, r_p2) not in defined_relations:
                self.solver.add(Not(self.Relates(r_p1, r_p2)))
        print("[Substrate Locked] Reality is a fixed, timeless graph.")

    def _assert_tier2_process_rules(self):
        """Defines the rules for the Scribe's journey over time."""
        print("\n--- TIER 2: Defining the Dynamic Observer ('The Scribe') ---")

        # The Scribe starts at the ground-like node p0 at time 0.
        self.solver.add(self.Location(0) == self.patterns[0])
        print("[Process Rule] Scribe starts at p0.")
        
        # Define the transition rules for T-1 steps.
        for i in range(self.t - 1):
            current_loc = self.Location(i)
            next_loc = self.Location(i+1)
            # The Scribe must move along an existing relation.
            self.solver.add(self.Relates(current_loc, next_loc))
        print(f"[Process Rule] Scribe must follow relational paths for {self.t-1} steps.")

    def _analyze_timeline(self, model):
        """Analyzes a valid timeline to find Consciousness Events."""
        
        # Reconstruct the Scribe's path from the Z3 model.
        scribe_path = []
        for i in range(self.t):
            loc = model.evaluate(self.Location(i))
            scribe_path.append(loc)

        print("\n--- Scribe's Journey (Tier 2 Process) ---")
        path_str = " → ".join([str(p) for p in scribe_path])
        print(f"  Path taken: {path_str}")

        print("\n--- Consciousness Event Analysis ---")
        # Now, check at each time step if the Scribe's memory matches a static Stone path.
        for i in range(1, len(scribe_path)):
            memory_trace = scribe_path[:i+1]
            memory_len = len(memory_trace)
            print(f"\n[Time T={i}] Scribe's memory: {' → '.join([str(p) for p in memory_trace])}")
            
            # Find all static paths of the same length on the Stone.
            all_stone_paths = self._find_all_paths(memory_len)
            
            # Check for an isomorphism.
            # In this simple model, isomorphism is just equality of the sequence.
            is_conscious_event = False
            for stone_path in all_stone_paths:
                if memory_trace == stone_path:
                    is_conscious_event = True
                    print(f"  [MATCH FOUND] Memory trace is identical to the static Stone path: {' → '.join([str(p) for p in stone_path])}")
                    break
            
            if is_conscious_event:
                print("  *** 🧠 CONSCIOUSNESS EVENT OCCURRED 🧠 ***")
            else:
                print("  [No Match] Scribe's experience does not correspond to a static path.")
    
    def _find_all_paths(self, length, current_path=[]):
        """A helper function to find all paths of a given length on the Stone."""
        if len(current_path) == length:
            return [current_path]

        if not current_path:
            # Start path from any node
            starts = self.patterns
        else:
            # Continue path from the last node
            last_node = current_path[-1]
            # This is a bit inefficient for a live script, but clear.
            # We would normally pre-calculate the adjacency list.
            starts = [p2 for p1, p2 in itertools.product(self.patterns, repeat=2) if p1 == last_node and is_true(self.solver.model().evaluate(self.Relates(p1, p2)))]

        all_paths = []
        for node in starts:
            new_paths = self._find_all_paths(length, current_path + [node])
            all_paths.extend(new_paths)
        return all_paths

# --- EXECUTION ---
if __name__ == "__main__":
    simulator = RosettaStoneSimulator(n=N, t=T)
    simulator.run_simulation()
