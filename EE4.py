# =============================================================================
#
#                 Stage 1: Combinatorial Universe Explorer (v5)
#
# This script embodies the principle of finding a maximally minimal set of axioms.
# It corrects a bug related to a missing import for the 'Distinct' function.
#
# =============================================================================

from z3 import (
    DeclareSort, Consts, BoolSort, Function, And, Or, Not, Implies,
    Solver, sat, is_true, Distinct
) # <-- CORRECTED: Added 'Distinct' to the import list.
import itertools

# --- CONFIGURATION ---
N = 4  # The size of our bounded universe.

class CombinatorialUniverseExplorer:
    """A tool to explore universes by combining minimal constraints."""

    def __init__(self, n):
        self.n = n
        self.Pattern = DeclareSort(f'Pattern_N{n}')
        self.patterns = list(Consts(' '.join(f'p{i}' for i in range(n)), self.Pattern))
        self.Relates = Function('Relates', self.Pattern, self.Pattern, BoolSort())
        
        # --- The Library of Minimal Constraints ---
        self.constraints = {
            "C1_IRREFLEXIVE": And([Not(self.Relates(p, p)) for p in self.patterns]),
            "C2_ASYMMETRIC": And([Implies(self.Relates(p1, p2), Not(self.Relates(p2, p1))) 
                                for p1, p2 in itertools.permutations(self.patterns, 2)]),
            "C3_GROUNDED": Or([And([Not(self.Relates(p_in, g)) for p_in in self.patterns]) 
                               for g in self.patterns]),
            "C4_NO_ISOLATION": And([Or([And(p != q, Or(self.Relates(p, q), self.Relates(q, p)))
                                     for q in self.patterns])
                                    for p in self.patterns])
        }

    def run_explorations(self):
        """Executes a series of explorations on different combinations of constraints."""
        print("="*80)
        print("        STAGE 1: COMBINATORIAL UNIVERSE EXPLORER (v5)")
        print("="*80)
        print(f"Exploring universes with N={self.n} patterns.\n")

        self.explore("Minimal Universe", [])
        self.explore("Irreflexive Universe", ["C1_IRREFLEXIVE"])
        self.explore("Acyclic (2-Cycle Free) Universe", ["C2_ASYMMETRIC"])
        self.explore("Irreflexive & Acyclic Universe", ["C1_IRREFLEXIVE", "C2_ASYMMETRIC"])
        self.explore("Grounded & Acyclic Universe", ["C3_GROUNDED", "C2_ASYMMETRIC"])
        self.explore("Enforced Monism (No Isolation)", ["C4_NO_ISOLATION"])
        self.explore("Grounded, Acyclic, Monistic Universe", ["C3_GROUNDED", "C2_ASYMMETRIC", "C4_NO_ISOLATION"])

    def _report_findings(self, name, model):
        """Analyzes and prints a human-readable report of a given model."""
        print(f"\n--- EXPLORATION REPORT: '{name}' ---")
        
        relations = [f"{p1} → {p2}" 
                     for p1, p2 in itertools.product(self.patterns, repeat=2) 
                     if is_true(model.evaluate(self.Relates(p1, p2)))]
        
        print("  - Model Found:")
        print(f"    - Relations: {', '.join(relations) or 'None'}")

        incoming_map = {p: [p_in for p_in in self.patterns if is_true(model.evaluate(self.Relates(p_in, p)))] for p in self.patterns}
        outgoing_map = {p: [p_out for p_out in self.patterns if is_true(model.evaluate(self.Relates(p, p_out)))] for p in self.patterns}

        sources = sorted([str(p) for p, incoming in incoming_map.items() if not incoming])
        terminals = sorted([str(p) for p, outgoing in outgoing_map.items() if not outgoing])
        isolated = sorted([str(p) for p in sources if p in terminals])

        print("  - Emergent Properties:")
        print(f"    - Source nodes (no parents): {sources or 'None'}")
        print(f"    - Terminal nodes (no children): {terminals or 'None'}")
        print(f"    - Isolated nodes (no relations): {isolated or 'None'}")
        print("-" * 50)

    def explore(self, name, constraint_keys):
        """A generic exploration function that combines constraints."""
        solver = Solver()
        
        # Base Axiom: Forces at least one relation to exist between our named patterns.
        base_axiom = Or([self.Relates(p1, p2) for p1, p2 in itertools.product(self.patterns, repeat=2)])
        solver.add(base_axiom)

        # Add distinctness axiom for all patterns
        if len(self.patterns) > 1:
            solver.add(Distinct(*self.patterns))

        print(f"Running Exploration: '{name}'")
        print(f"  - Constraints: {constraint_keys or 'None'}")

        for key in constraint_keys:
            solver.add(self.constraints[key])

        if solver.check() == sat:
            self._report_findings(name, solver.model())
        else:
            print(f"\n--- EXPLORATION REPORT: '{name}' ---")
            print("  - No model found. This combination of constraints is contradictory.")
            print("-" * 50)

# --- EXECUTION ---
if __name__ == "__main__":
    explorer = CombinatorialUniverseExplorer(n=N)
    explorer.run_explorations()
