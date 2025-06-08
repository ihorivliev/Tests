from pysmt.shortcuts import (Symbol, And, Or, Implies, Solver, Equals, Not, Int, Plus, # ToInt removed
                             TRUE, FALSE, GE, LE, Ite) # Added Ite
from pysmt.typing import BOOL as SMT_BOOL_TYPE, INT as SMT_INT_TYPE, FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple

# AVCA standard tables for Omega=3 (U=0, DFI1=1, DFI2=2)
avca_add_table_omega3_py = { 
    (0,0):0, (0,1):1, (0,2):2,
    (1,0):1, (1,1):2, (1,2):0,
    (2,0):2, (2,1):0, (2,2):0
}
avca_mul_table_omega3_py = { # Included if we want to test mul_mono later
    (0,0):0, (0,1):0, (0,2):0,
    (1,0):0, (1,1):1, (1,2):2,
    (2,0):0, (2,1):2, (2,2):0
}

def run_nontrivial_order_discovery(omega_val: int = 3, 
                                   check_add_mono: bool = True, 
                                   check_mul_mono: bool = False,
                                   min_nontrivial_relations: int = 1):
    print(f"--- order_discovery_nontrivial.py: SMT Search for NON-TRIVIAL Monotonic PO (Omega={omega_val}) ---")
    print(f"    Attempting to find an order with at least {min_nontrivial_relations} non-reflexive true relation(s).")
    if omega_val != 3:
        print("Warning: This script's AVCA tables are hardcoded for Omega=3.")

    S_py = list(range(omega_val)) 
    
    le_vars: Dict[Tuple[int,int], FNode] = {}
    for i_py in S_py:
        for j_py in S_py:
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

    if check_mul_mono:
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

    # --- Constraint for Non-Triviality ---
    non_reflexive_le_int_vars = []
    for i_py in S_py:
        for j_py in S_py:
            if i_py != j_py:
                # Convert boolean le_vars[(i_py, j_py)] to Int(1) if True, Int(0) if False
                non_reflexive_le_int_vars.append(Ite(le_vars[(i_py, j_py)], Int(1), Int(0))) # CORRECTED
    
    sum_of_true_non_reflexive_relations = Plus(non_reflexive_le_int_vars) if non_reflexive_le_int_vars else Int(0)
    nontriviality_constraint = GE(sum_of_true_non_reflexive_relations, Int(min_nontrivial_relations))
    print(f"  Adding constraint for at least {min_nontrivial_relations} non-reflexive true relation(s).")

    with Solver(name="z3") as s: 
        s.add_assertion(smt_po_axioms)
        if all_monotonicity_assertions:
            s.add_assertion(And(all_monotonicity_assertions))
        s.add_assertion(nontriviality_constraint)

        print("  Searching for a NON-TRIVIAL partial order satisfying all constraints...")
        
        if s.solve():
            print("  SAT: Found a NON-TRIVIAL partial order satisfying the monotonicity constraints!")
            model = s.get_model()
            true_non_reflexive_relations_count = 0
            print("    Discovered Partial Order le(x,y) [x <= y]:")
            for i_py_model in S_py:
                related_to_i_list = []
                for j_py_model in S_py:
                    le_var = le_vars.get((i_py_model,j_py_model))
                    if le_var and model.get_value(le_var).is_true(): 
                        related_to_i_list.append(j_py_model)
                        if i_py_model != j_py_model:
                            true_non_reflexive_relations_count +=1
                related_to_i_list.sort() 
                print(f"      {i_py_model} <= {related_to_i_list}")
            print(f"    Number of true non-reflexive le(i,j) relations in this model: {true_non_reflexive_relations_count}")
            if true_non_reflexive_relations_count < min_nontrivial_relations:
                 print(f"    WARNING: Model found, but true non-reflexive relations ({true_non_reflexive_relations_count}) is less than specified minimum ({min_nontrivial_relations}). Check logic.")

        else:
             print(f"  UNSAT: No NON-TRIVIAL partial order (with at least {min_nontrivial_relations} non-reflexive relations) found that makes the operation(s) monotone.")

# --- Main Execution Block ---
if __name__ == "__main__":
    # Ensure FunctionType is available for Leq symbol declaration if using uninterpreted function style
    # from pysmt.typing import FunctionType # Not needed for le_vars as Symbols
    
    # The script's internal 'le_vars' dictionary uses Boolean Symbols for le(i,j)

    run_nontrivial_order_discovery(omega_val=3, check_add_mono=True, check_mul_mono=False, min_nontrivial_relations=1)
    
    # Example: Search for an order with at least 2 non-reflexive relations that makes both ⊕ and ⊗ monotone
    # print("\n--- Now testing for both ⊕ and ⊗ monotonicity with at least 2 non-trivial relations ---")
    # run_nontrivial_order_discovery(omega_val=3, check_add_mono=True, check_mul_mono=True, min_nontrivial_relations=2)

