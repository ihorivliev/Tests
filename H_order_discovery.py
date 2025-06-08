from pysmt.shortcuts import (Symbol, And, Or, Implies, Solver, Equals, Not, Int, 
                             TRUE, FALSE) 
from pysmt.typing import BOOL as SMT_BOOL_TYPE, INT as SMT_INT_TYPE
from pysmt.fnode import FNode 
from typing import List, Dict, Tuple

# AVCA standard tables for Omega=3 (U=0, DFI1=1, DFI2=2)
avca_add_table_omega3_py = { 
    (0,0):0, (0,1):1, (0,2):2,
    (1,0):1, (1,1):2, (1,2):0,
    (2,0):2, (2,1):0, (2,2):0
}
avca_mul_table_omega3_py = {
    (0,0):0, (0,1):0, (0,2):0,
    (1,0):0, (1,1):1, (1,2):2,
    (2,0):0, (2,1):2, (2,2):0
}

def run_order_discovery(omega_val: int = 3, check_add_mono: bool = True, check_mul_mono: bool = False): # Parameter is check_mul_mono
    print(f"--- order_discovery.py: SMT Search for Monotonic Partial Order (Omega={omega_val}) ---")
    if omega_val != 3:
        print("Warning: This script's AVCA tables are hardcoded for Omega=3.")

    S_py = list(range(omega_val)) 
    
    # Leq is an uninterpreted predicate Leq(x,y) -> Bool
    Leq_predicate_name = "Leq_UserDefined" 
    Leq = Symbol(Leq_predicate_name, FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])) # Needs FunctionType
                                                                                                # from pysmt.typing

    # --- User Defined Partial Order Assertions ---
    # This part needs to be filled by the user based on their candidate order
    # For now, we proceed as if Leq is unconstrained beyond PO axioms and monotonicity.
    # To test a *specific* order, user_order_facts = get_user_defined_order_assertions() would be used.
    # For *discovery*, we let Leq be free variables constrained by PO and Mono axioms.

    le_vars: Dict[Tuple[int,int], FNode] = {} # Store direct SMT variables for le(i,j)
    for i_py in S_py:
        for j_py in S_py:
            # Instead of using the uninterpreted function directly for all assertions,
            # we can create Boolean SMT variables for each le(i,j)
            # and then constrain the uninterpreted function Leq to equal these.
            # This makes the "minimization" heuristic slightly easier to formulate.
            # However, using the uninterpreted function directly is cleaner for axioms.
            # Let's stick to the auditor's skeleton of using le[(i,j)] as direct symbols
            le_vars[(i_py,j_py)] = Symbol(f"le_{i_py}_{j_py}", SMT_BOOL_TYPE)


    po_axioms_list = []
    # Reflexivity: le[i,i] is TRUE
    for i_py in S_py:
        po_axioms_list.append(le_vars[(i_py,i_py)])
    
    # Antisymmetry: (le[i,j] AND le[j,i]) IMPLIES (i == j)
    for i_py in S_py:
        for j_py in S_py:
            if i_py != j_py: 
                po_axioms_list.append(Implies(And(le_vars[(i_py,j_py)], le_vars[(j_py,i_py)]), FALSE()))
    
    # Transitivity: (le[i,j] AND le[j,k]) IMPLIES le[i,k]
    for i_py in S_py:
        for j_py in S_py:
            for k_py in S_py:
                po_axioms_list.append(Implies(And(le_vars[(i_py,j_py)], le_vars[(j_py,k_py)]), le_vars[(i_py,k_py)]))
    
    smt_po_axioms = And(po_axioms_list)
    print(f"Asserted {len(po_axioms_list)} partial order axioms.")

    all_monotonicity_assertions = []

    if check_add_mono:
        print("  Including ⊕-monotonicity constraints...")
        mono_plus_axioms_list = []
        for a_py in S_py:
            for b_py in S_py:
                premise_leq_ab = le_vars[(a_py,b_py)] 
                for x_py in S_py:
                    res_xa = avca_add_table_omega3_py[(x_py,a_py)]
                    res_xb = avca_add_table_omega3_py[(x_py,b_py)]
                    mono_plus_axioms_list.append(Implies(premise_leq_ab, le_vars[(res_xa, res_xb)]))
                    
                    res_ax = avca_add_table_omega3_py[(a_py,x_py)]
                    res_bx = avca_add_table_omega3_py[(b_py,x_py)]
                    mono_plus_axioms_list.append(Implies(premise_leq_ab, le_vars[(res_ax, res_bx)]))
        all_monotonicity_assertions.append(And(mono_plus_axioms_list))
        print(f"    Added {len(mono_plus_axioms_list)} ⊕-monotonicity implication clauses.")

    if check_mul_mono: # CORRECTED: check_mul_mono, not check_mul_monotonicity
        print("  Including ⊗-monotonicity constraints...")
        mono_mul_axioms_list = []
        for a_py in S_py:
            for b_py in S_py:
                premise_leq_ab = le_vars[(a_py,b_py)]
                for x_py in S_py:
                    res_xa_mul = avca_mul_table_omega3_py[(x_py,a_py)]
                    res_xb_mul = avca_mul_table_omega3_py[(x_py,b_py)]
                    mono_mul_axioms_list.append(Implies(premise_leq_ab, le_vars[(res_xa_mul, res_xb_mul)]))
                    res_ax_mul = avca_mul_table_omega3_py[(a_py,x_py)]
                    res_bx_mul = avca_mul_table_omega3_py[(b_py,x_py)]
                    mono_mul_axioms_list.append(Implies(premise_leq_ab, le_vars[(res_ax_mul, res_bx_mul)]))
        all_monotonicity_assertions.append(And(mono_mul_axioms_list))
        print(f"    Added {len(mono_mul_axioms_list)} ⊗-monotonicity implication clauses.")

    with Solver(name="z3") as s: 
        s.add_assertion(smt_po_axioms)
        if all_monotonicity_assertions:
            s.add_assertion(And(all_monotonicity_assertions))

        print("  Searching for a partial order satisfying all constraints...")
        
        if s.solve():
            print("  SAT: Found a partial order satisfying the monotonicity constraints!")
            model = s.get_model()
            true_non_reflexive_relations = 0
            print("    Discovered Partial Order le(x,y) [x <= y]:")
            for i_py_model in S_py:
                related_to_i_list = []
                for j_py_model in S_py:
                    le_var = le_vars.get((i_py_model,j_py_model))
                    if le_var and model.get_value(le_var).is_true(): 
                        related_to_i_list.append(j_py_model)
                        if i_py_model != j_py_model:
                            true_non_reflexive_relations +=1
                # Sort for consistent output, useful if many relations
                related_to_i_list.sort() 
                print(f"      {i_py_model} <= {related_to_i_list}")
            print(f"    Number of true non-reflexive le(i,j) relations in this model: {true_non_reflexive_relations}")
        else:
             print("  UNSAT: No such partial order found that makes the operation(s) monotone with these constraints.")

# --- Main Execution Block ---
if __name__ == "__main__":
    # Ensure function definition is above this block
    # The FunctionType import was also missing previously for Leq symbol declaration
    from pysmt.typing import FunctionType 

    run_order_discovery(omega_val=3, check_add_mono=True, check_mul_mono=False)
