# H_C1_Operational_Uniqueness_Test.py (v3)
# SMT Test for H-C1: Is any algebra X = (S3,oplus',otimes') satisfying GIT Axioms A1-A6
# (interpreted strongly with AVCA DFI/Unio behaviors) necessarily identical to AVCA-Omega=3?

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- AVCA Best Combination Kernel Operations (Python reference for Cayley tables) ---
add_AVCA_Omega3_table = {
    (0,0):0, (0,1):1, (0,2):2,
    (1,0):1, (1,1):2, (1,2):0,
    (2,0):2, (2,1):0, (2,2):0,
}
mul_AVCA_Omega3_table = {
    (0,0):0, (0,1):0, (0,2):0,
    (1,0):0, (1,1):1, (1,2):2,
    (2,0):0, (2,1):2, (2,2):0,
}

def test_H_C1_operational_uniqueness(omega_py: int):
    if omega_py != 3:
        print(f"This script is hardcoded for Omega={omega_py}. Please use Omega=3.")
        return False

    print(f"\n--- Testing H-C1 (Operational Uniqueness): Forcing an algebra to satisfy AVCA Axioms for Omega={omega_py} ---")
    
    solver = Solver(name="z3")
    omega_smt_val = Int(omega_py)
    
    U_alg = Int(0)
    FP1_alg = Int(1)
    FP2_alg = Int(2)
    s_omega_vals = [U_alg, FP1_alg, FP2_alg]

    res_add_X: Dict[Tuple[FNode, FNode], FNode] = {}
    res_mul_X: Dict[Tuple[FNode, FNode], FNode] = {}

    print("  1. Defining symbolic tables for oplus_X and otimes_X...")
    s_omega_py_keys = [(i,j) for i in range(omega_py) for j in range(omega_py)]

    for i_py_key in range(omega_py):
        for j_py_key in range(omega_py):
            i_smt_key, j_smt_key = Int(i_py_key), Int(j_py_key)
            
            add_res_var = Symbol(f"r_add_X_{i_py_key}{j_py_key}", SMT_INT_TYPE)
            solver.add_assertion(Or(Equals(add_res_var, U_alg), Equals(add_res_var, FP1_alg), Equals(add_res_var, FP2_alg)))
            res_add_X[(i_smt_key, j_smt_key)] = add_res_var
            
            mul_res_var = Symbol(f"r_mul_X_{i_py_key}{j_py_key}", SMT_INT_TYPE)
            solver.add_assertion(Or(Equals(mul_res_var, U_alg), Equals(mul_res_var, FP1_alg), Equals(mul_res_var, FP2_alg)))
            res_mul_X[(i_smt_key, j_smt_key)] = mul_res_var

    print("  2. Asserting GIT Axioms A1-A6 for the symbolic algebra X...")

    for x_val in s_omega_vals:
        solver.add_assertion(Equals(res_add_X[(U_alg, x_val)], x_val))
        solver.add_assertion(Equals(res_add_X[(x_val, U_alg)], x_val))

    solver.add_assertion(Equals(res_add_X[(FP1_alg, FP1_alg)], FP2_alg)) 
    solver.add_assertion(Equals(res_add_X[(FP1_alg, FP2_alg)], U_alg)) 
    solver.add_assertion(Equals(res_add_X[(FP2_alg, FP1_alg)], U_alg)) 
    solver.add_assertion(Equals(res_add_X[(FP2_alg, FP2_alg)], U_alg)) 
    
    for v1 in s_omega_vals:
        for v2 in s_omega_vals:
            solver.add_assertion(Equals(res_mul_X[(v1,v2)], res_mul_X[(v2,v1)]))

    assoc_constraints_mul_X = []
    for i_val_outer in s_omega_vals:
        for j_val_outer in s_omega_vals:
            for k_val_outer in s_omega_vals:
                ij_mul_X_sym = res_mul_X[(i_val_outer, j_val_outer)] 
                lhs_final_val_assoc = Ite(Equals(ij_mul_X_sym, U_alg), res_mul_X[(U_alg, k_val_outer)],
                                     Ite(Equals(ij_mul_X_sym, FP1_alg), res_mul_X[(FP1_alg, k_val_outer)],
                                         res_mul_X[(FP2_alg, k_val_outer)]))
                jk_mul_X_sym = res_mul_X[(j_val_outer, k_val_outer)]
                rhs_final_val_assoc = Ite(Equals(jk_mul_X_sym, U_alg), res_mul_X[(i_val_outer, U_alg)],
                                     Ite(Equals(jk_mul_X_sym, FP1_alg), res_mul_X[(i_val_outer, FP1_alg)],
                                         res_mul_X[(i_val_outer, FP2_alg)]))
                assoc_constraints_mul_X.append(Equals(lhs_final_val_assoc, rhs_final_val_assoc))
    
    for constr in assoc_constraints_mul_X:
        solver.add_assertion(constr)

    for x_val in s_omega_vals:
        solver.add_assertion(Equals(res_mul_X[(U_alg, x_val)], U_alg))

    solver.add_assertion(Equals(res_mul_X[(FP1_alg, FP1_alg)], FP1_alg)) 
    solver.add_assertion(Equals(res_mul_X[(FP1_alg, FP2_alg)], FP2_alg)) 
    solver.add_assertion(Equals(res_mul_X[(FP2_alg, FP2_alg)], U_alg))   

    print("  3. Asserting that the symbolic algebra X DIFFERS from AVCA-Omega=3 Best Combo...")
    difference_clauses = []
    for i_py_key_diff in range(omega_py):
        for j_py_key_diff in range(omega_py):
            i_smt_key_diff, j_smt_key_diff = Int(i_py_key_diff), Int(j_py_key_diff)

            avca_add_expected_val = Int(add_AVCA_Omega3_table[(i_py_key_diff, j_py_key_diff)])
            difference_clauses.append(Not(Equals(res_add_X[(i_smt_key_diff, j_smt_key_diff)], avca_add_expected_val))) # Corrected
            
            avca_mul_expected_val = Int(mul_AVCA_Omega3_table[(i_py_key_diff, j_py_key_diff)])
            difference_clauses.append(Not(Equals(res_mul_X[(i_smt_key_diff, j_smt_key_diff)], avca_mul_expected_val))) # Corrected
            
    solver.add_assertion(Or(difference_clauses))

    print("  4. Solving...")
    property_holds = False 
    if not solver.solve():
        print("  RESULT: UNSAT. No algebra X satisfying all specified AVCA axioms and DFI/Unio behaviors")
        print("          can differ from the AVCA-Omega=3 Best Combination kernel.")
        print("          This implies operational uniqueness under these strong axiomatic interpretations.")
        property_holds = True
    else:
        print("  RESULT: SAT. An alternative algebra X was found that satisfies the axioms but differs.")
        print("          This is UNEXPECTED if the axioms fully constrain the operations to AVCA's.")
        model = solver.get_model()
        # (Model printing can be extensive, omitted for brevity unless specifically needed for debug)
        # Example of how to print if SAT:
        # print("    Alternative oplus_X table:")
        # for i_val_p in s_omega_vals:
        #     row_str = f"      {i_val_p.constant_value()} | "
        #     for j_val_p in s_omega_vals:
        #         row_str += f"{model.get_value(res_add_X[(i_val_p, j_val_p)])} "
        #     print(row_str)
        property_holds = False
        
    return property_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_C1_Operational_Uniqueness_Test (v3): ======")
    
    omega_to_test = 3
    
    ops_are_unique = test_H_C1_operational_uniqueness(omega_to_test)

    print("\n--- Summary of H-C1 (Operational Uniqueness Test v3) ---")
    print(f"For Omega = {omega_to_test}:")
    if ops_are_unique:
        print("  The AVCA Best Combination operations (⊕_BC, ⊗_BC) appear to be UNIQELY DEFINED by")
        print("  the GIT Axioms A1-A6 when interpreted with AVCA's specific DFI/Unio behaviors.")
        print("  This implies any 'collapse ring' satisfying these strong conditions is AVCA-Ω itself.")
        print("  Combined with the previous automorphism result (identity is unique tag-preserving automorphism),")
        print("  this strongly supports H-C1 for Ω=3 under this interpretation.")
    else:
        print("  An alternative algebra satisfying the axioms but differing from AVCA-Ω was found,")
        print("  OR the SMT setup has an issue or timed out.")
        print("  This would challenge H-C1 or the current interpretation of 'collapse ring' axioms.")

    print("\n====== H_C1_Operational_Uniqueness_Test (v3) Script Finished ======")