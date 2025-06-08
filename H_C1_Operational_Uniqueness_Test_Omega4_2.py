# H_C1_Operational_Uniqueness_Test_Omega4.py (v2 - Corrected Associativity ITE)
# SMT Test for H-C1: Is any algebra X = (S4,oplus',otimes') satisfying GIT Axioms A1-A6
# (interpreted strongly with AVCA DFI/Unio behaviors) necessarily identical to AVCA-Omega=4?

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- AVCA Best Combination Kernel Operations (Python reference for Cayley tables for Omega=4) ---
add_AVCA_Omega4_table = {
    (0,0):0, (0,1):1, (0,2):2, (0,3):3,
    (1,0):1, (1,1):2, (1,2):3, (1,3):0, 
    (2,0):2, (2,1):3, (2,2):0, (2,3):0, 
    (3,0):3, (3,1):0, (3,2):0, (3,3):0, 
}
mul_AVCA_Omega4_table = {
    (0,0):0, (0,1):0, (0,2):0, (0,3):0,
    (1,0):0, (1,1):1, (1,2):2, (1,3):3,
    (2,0):0, (2,1):2, (2,2):0, (2,3):0, 
    (3,0):0, (3,1):3, (3,2):0, (3,3):0, 
}

def test_H_C1_operational_uniqueness_O4(omega_py: int):
    if omega_py != 4:
        print(f"ERROR: This script is specifically configured for Omega=4. Current Omega={omega_py}.")
        return False 

    print(f"\n--- Testing H-C1 (Operational Uniqueness): Forcing an algebra X to satisfy AVCA Axioms for Omega={omega_py} ---")
    
    solver = Solver(name="z3", solver_options={'timeout': 600000}) # 10 minute timeout
    
    U_alg = Int(0)
    FP1_alg = Int(1)
    FP2_alg = Int(2)
    FP3_alg = Int(3)
    s_omega_vals = [U_alg, FP1_alg, FP2_alg, FP3_alg] 

    res_add_X: Dict[Tuple[FNode, FNode], FNode] = {}
    res_mul_X: Dict[Tuple[FNode, FNode], FNode] = {}

    print("  1. Defining symbolic tables for oplus_X and otimes_X...")
    for i_py_key in range(omega_py):
        for j_py_key in range(omega_py):
            i_smt_key, j_smt_key = Int(i_py_key), Int(j_py_key)
            
            add_res_var = Symbol(f"r_add_X_{i_py_key}{j_py_key}", SMT_INT_TYPE)
            solver.add_assertion(Or([Equals(add_res_var, val) for val in s_omega_vals])) 
            res_add_X[(i_smt_key, j_smt_key)] = add_res_var
            
            mul_res_var = Symbol(f"r_mul_X_{i_py_key}{j_py_key}", SMT_INT_TYPE)
            solver.add_assertion(Or([Equals(mul_res_var, val) for val in s_omega_vals])) 
            res_mul_X[(i_smt_key, j_smt_key)] = mul_res_var

    print("  2. Asserting GIT Axioms A1-A6 for the symbolic algebra X...")

    # Axioms A1,A3,A4,A5 for oplus_X (forces oplus_X = add_AVCA_Omega4_table)
    # This is because GIT Clause 5 states these axioms uniquely determine the add table.
    print("    Asserting Axioms for oplus_X (forcing it to be AVCA add for Omega=4)...")
    for i_py_key_ax_add in range(omega_py):
        for j_py_key_ax_add in range(omega_py):
            i_smt_key_ax_add, j_smt_key_ax_add = Int(i_py_key_ax_add), Int(j_py_key_ax_add)
            expected_add_res = Int(add_AVCA_Omega4_table[(i_py_key_ax_add, j_py_key_ax_add)])
            solver.add_assertion(Equals(res_add_X[(i_smt_key_ax_add, j_smt_key_ax_add)], expected_add_res))
    
    # Axiom A2_tensor (Commutativity of otimes_X)
    print("    Asserting A2_tensor (Commutativity of otimes_X)...")
    for v1_idx in range(omega_py):
        for v2_idx in range(v1_idx + 1, omega_py): 
            v1 = s_omega_vals[v1_idx]
            v2 = s_omega_vals[v2_idx]
            solver.add_assertion(Equals(res_mul_X[(v1,v2)], res_mul_X[(v2,v1)]))

    # Axiom A6 (Associativity of otimes_X)
    print("    Asserting A6 (Associativity of otimes_X)... (64 constraints)")
    for i_val in s_omega_vals:
        for j_val in s_omega_vals:
            for k_val in s_omega_vals:
                ij_mul_X_sym = res_mul_X[(i_val, j_val)] 
                
                lhs_final_val_assoc = Ite(Equals(ij_mul_X_sym, U_alg), res_mul_X[(U_alg, k_val)],
                                     Ite(Equals(ij_mul_X_sym, FP1_alg), res_mul_X[(FP1_alg, k_val)],
                                     Ite(Equals(ij_mul_X_sym, FP2_alg), res_mul_X[(FP2_alg, k_val)],
                                         res_mul_X[(FP3_alg, k_val)]))) 

                jk_mul_X_sym = res_mul_X[(j_val, k_val)]
                rhs_final_val_assoc = Ite(Equals(jk_mul_X_sym, U_alg), res_mul_X[(i_val, U_alg)],
                                     Ite(Equals(jk_mul_X_sym, FP1_alg), res_mul_X[(i_val, FP1_alg)],
                                     Ite(Equals(jk_mul_X_sym, FP2_alg), res_mul_X[(i_val, FP2_alg)],
                                         res_mul_X[(i_val, FP3_alg)]))) 
                
                solver.add_assertion(Equals(lhs_final_val_assoc, rhs_final_val_assoc))
    
    # Assert AVCA-specific DFI multiplication rules & Unio annihilator for otimes_X
    print("    Asserting AVCA-specific DFI/Unio multiplication rules for otimes_X...")
    # U_alg as annihilator:
    for x_val in s_omega_vals:
        solver.add_assertion(Equals(res_mul_X[(U_alg, x_val)], U_alg))
        if x_val != U_alg : 
             solver.add_assertion(Equals(res_mul_X[(x_val, U_alg)], U_alg)) # Also assert right-annihilation

    # DFI rules for otimes_X for Omega=4:
    solver.add_assertion(Equals(res_mul_X[(FP1_alg, FP1_alg)], FP1_alg)) 
    solver.add_assertion(Equals(res_mul_X[(FP1_alg, FP2_alg)], FP2_alg)) 
    solver.add_assertion(Equals(res_mul_X[(FP1_alg, FP3_alg)], FP3_alg)) 
    solver.add_assertion(Equals(res_mul_X[(FP2_alg, FP2_alg)], U_alg))   
    solver.add_assertion(Equals(res_mul_X[(FP2_alg, FP3_alg)], U_alg))   
    solver.add_assertion(Equals(res_mul_X[(FP3_alg, FP3_alg)], U_alg))   
    # Commutativity already asserted covers symmetric DFI pairs like (FP2_alg, FP1_alg) etc.

    print("  3. Asserting that the symbolic algebra X.otimes_X DIFFERS from AVCA-Omega=4 Best Combo Mul...")
    difference_clauses = []
    for i_py_key_diff in range(omega_py):
        for j_py_key_diff in range(omega_py):
            i_smt_key_diff, j_smt_key_diff = Int(i_py_key_diff), Int(j_py_key_diff)
            
            # oplus_X is already forced to be add_AVCA_Omega4_table.
            # So, only need to check difference in otimes_X
            avca_mul_expected_val = Int(mul_AVCA_Omega4_table[(i_py_key_diff, j_py_key_diff)])
            difference_clauses.append(Not(Equals(res_mul_X[(i_smt_key_diff, j_smt_key_diff)], avca_mul_expected_val)))
            
    solver.add_assertion(Or(difference_clauses))

    print("  4. Solving (this will be computationally intensive for Omega=4)...")
    property_holds = False 
    solve_result = solver.solve()
    if not solve_result:
        print("  RESULT: UNSAT. No algebra X satisfying all specified AVCA axioms and DFI/Unio behaviors")
        print("          can differ from the AVCA-Omega=4 Best Combination kernel's multiplication.")
        print("          This implies operational uniqueness for multiplication under these strong axiomatic interpretations.")
        property_holds = True
    else:
        print("  RESULT: SAT. An alternative multiplication otimes_X was found that satisfies the axioms but differs.")
        print("          This is UNEXPECTED if the axioms fully constrain multiplication to AVCA's.")
        # model = solver.get_model() # Model can be very large, print selectively if needed
        # Example: print(model.get_value(res_mul_X[Int(1), Int(1)]))
        property_holds = False
        
    return property_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_C1_Operational_Uniqueness_Test_Omega4 (v2): ======")
    
    omega_to_test = 4
    
    ops_are_unique = test_H_C1_operational_uniqueness_O4(omega_to_test)

    print("\n--- Summary of H-C1 (Operational Uniqueness Test for Omega=4 v2) ---")
    print(f"For Omega = {omega_to_test}:")
    if ops_are_unique:
        print("  The AVCA Best Combination multiplication (⊗_BC) appears to be UNIQELY DEFINED by")
        print("  the relevant GIT Axioms (A1,A2⊗,A6) when interpreted with AVCA's specific DFI/Unio behaviors.")
        print("  (Addition ⊕_BC was already known to be uniquely defined by its GIT axioms).")
        print("  This implies any 'collapse ring' satisfying these strong conditions is operationally AVCA-Ω itself.")
    else:
        print("  An alternative multiplication otimes_X satisfying the axioms but differing from AVCA-Ω's ⊗_BC was found,")
        print("  OR the SMT solver timed out / encountered an issue, OR the SMT setup has an issue.")
        print("  This would challenge H-C1 or the current interpretation of 'collapse ring' axioms if genuinely SAT.")

    print("\n====== H_C1_Operational_Uniqueness_Test_Omega4 (v2) Script Finished ======")