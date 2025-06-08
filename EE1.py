# =============================================================================
#
#                    Stage 1: Generative Universe Explorer
#
# This script implements the "Bottom-Up (Investigative Emergence)" methodology.
# Its purpose is not to validate or falsify a pre-existing theory, but to
# generate and analyze the simplest possible coherent universes that can be
# built from a maximally minimal set of axioms.
#
# This version corrects a bug related to evaluating Z3 models.
#
# =============================================================================

from z3 import (
    DeclareSort, Const, Consts, BoolSort, Function, And, Or, Not, Implies,
    Exists, ForAll, Solver, sat, unsat, Distinct, is_true
) # <-- CORRECTED: Added 'is_true' to handle model evaluation.
import itertools

# --- CONFIGURATION ---
# The size of our bounded universe. A small N is ideal for exploration.
N = 4

class GenerativeUniverseExplorer:
    """A tool to generate and analyze minimal, relation-based universes."""

    def __init__(self, n):
        self.n = n
        self.Pattern = DeclareSort(f'Pattern_N{n}')
        self.patterns = Consts(' '.join(f'p{i}' for i in range(n)), self.Pattern)
        self.Relates = Function('Relates', self.Pattern, self.Pattern, BoolSort())

    def run_explorations(self):
        """Executes a series of explorations on different minimal universes."""
        print("="*80)
        print("          STAGE 1: GENERATIVE UNIVERSE EXPLORER")
        print("="*80)
        print(f"Exploring possible universes with N={self.n} patterns.\n")

        self.explore_minimal_universe()
        self.explore_irreflexive_universe()
        self.explore_acyclic_universe()
        self.explore_grounded_universe()
        
    def _report_findings(self, name, axioms, model):
        """Analyzes and prints a human-readable report of a given model."""
        print(f"\n--- EXPLORATION REPORT: '{name}' ---")
        
        relations = []
        # CORRECTED: Use is_true() to evaluate the model's boolean results.
        for p1, p2 in itertools.product(self.patterns, repeat=2):
            if is_true(model.evaluate(self.Relates(p1, p2))):
                relations.append(f"{p1} → {p2}")
        
        print("  - Model Found:")
        if relations:
            print(f"    - Relations: {', '.join(relations)}")
        else:
            print("    - No relations found in this model.")

        # Analyze emergent properties
        incoming_map = {p: [] for p in self.patterns}
        outgoing_map = {p: [] for p in self.patterns}
        
        for p1, p2 in itertools.product(self.patterns, repeat=2):
            if is_true(model.evaluate(self.Relates(p1, p2))):
                outgoing_map[p1].append(p2)
                incoming_map[p2].append(p1)

        sources = {p for p, incoming in incoming_map.items() if not incoming}
        terminals = {p for p, outgoing in outgoing_map.items() if not outgoing}
        isolated = sources.intersection(terminals)

        print("  - Emergent Properties:")
        print(f"    - Source nodes (no parents): {sorted([str(p) for p in sources]) if sources else 'None'}")
        print(f"    - Terminal nodes (no children): {sorted([str(p) for p in terminals]) if terminals else 'None'}")
        print(f"    - Isolated nodes (no relations): {sorted([str(p) for p in isolated]) if isolated else 'None'}")
        print("-" * 50)


    def _explore(self, name, constraints):
        """A generic exploration function."""
        solver = Solver()
        
        # Base Axiom: At least one relation must exist.
        p1, p2 = Consts('p1_exists p2_exists', self.Pattern)
        base_axiom = Exists([p1, p2], self.Relates(p1, p2))
        solver.add(base_axiom)

        # Add the specific constraints for this exploration
        if constraints:
            solver.add(constraints)

        # Check for a model
        if solver.check() == sat:
            self._report_findings(name, [base_axiom] + constraints, solver.model())
        else:
            print(f"\n--- EXPLORATION REPORT: '{name}' ---")
            print("  - No model found. The constraints are contradictory.")
            print("-" * 50)


    def explore_minimal_universe(self):
        """SCENARIO 1: The most basic universe possible."""
        print("1. Exploring the simplest possible universe with just one relation.")
        self._explore("Minimal Universe (Axiom of Relation only)", [])

    def explore_irreflexive_universe(self):
        """SCENARIO 2: A universe where nothing relates to itself."""
        print("\n2. Constraining the universe to be IRREFLEXIVE (no self-relations).")
        p = Const('p_forall', self.Pattern)
        constraint = ForAll(p, Not(self.Relates(p, p)))
        self._explore("Irreflexive Universe", [constraint])

    def explore_acyclic_universe(self):
        """SCENARIO 3: A universe with no 2-cycles, a prerequisite for time."""
        print("\n3. Constraining the universe to be ASYMMETRIC (no A->B and B->A pairs).")
        p1, p2 = Consts('p1_forall p2_forall', self.Pattern)
        constraint = ForAll([p1, p2], Implies(self.Relates(p1, p2), Not(self.Relates(p2, p1))))
        self._explore("Acyclic (2-Cycle Free) Universe", [constraint])

    def explore_grounded_universe(self):
        """SCENARIO 4: A universe that must have a 'foundational ground'."""
        print("\n4. Constraining the universe to be GROUNDED (at least one 'un-caused' node).")
        g = Const('g_exists', self.Pattern)
        p = Const('p_forall', self.Pattern)
        constraint = Exists(g, ForAll(p, Not(self.Relates(p, g))))
        self._explore("Grounded Universe", [constraint])

# --- EXECUTION ---
if __name__ == "__main__":
    explorer = GenerativeUniverseExplorer(n=N)
    explorer.run_explorations()
