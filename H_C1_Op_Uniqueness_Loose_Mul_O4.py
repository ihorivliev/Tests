# H_C1_Op_Uniqueness_Loose_Mul_O4.py
# SMT Test for H-C1 (Omega=4):
# Is any algebra X = (S4,oplus_X,otimes_X) satisfying GIT Axioms A1,A3,A4,A5 for oplus_X
# AND A1,A2_tensor,A6 for otimes_X (with U_X as annihilator for otimes_X, but LOOSER DFI rules for otimes_X)
# necessarily identical to AVCA-Omega=4's otimes_X?

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- AVCA Best Combination Kernel Operations (Python reference for Cayley tables for Omega=4) ---
add_AVCA_Omega4_table_fixed_loose = {
    (0,0):0, (0,1):1, (0,2):2, (0,3):3,
    (1,0):1, (1,1):2, (1,2):3, (1,3):0, 
    (2,0):2, (2,1):3, (2,2):0, (2,3):0, 
    (3,0):3, (3,1):0, (3,2):0, (3,3):0, 
}
mul_AVCA_Omega4_table_fixed_loose = {
    (0,0):0, (0,1):0, (0,2):0, (0,3):0,
    (1,0):0, (1,1):1, (1,2):2, (1,3):3,
    (2,0):0, (2,1):2, (2,2):0, (2,3):0, 
    (3,0):0, (3,1):3, (3,2):0, (3,3):0, 
}

def test_H_C1_op_uniqueness_loose_mul_O4(omega_py: int):
    if omega_py != 4:
        print(f"ERROR: This script is specifically configured for Omega=4. Current Omega={omega_py}.")
        return False

    print(f"\n--- Testing H-C1 (Op. Uniqueness with LOOSER Mul DFI rules) for Omega={omega_py} ---")

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
            
            add_res_var = Symbol(f"r_add_X_lmO4_{i_py_key}{j_py_key}", SMT_INT_TYPE)
            solver.add_assertion(Or([Equals(add_res_var, val) for val in s_omega_vals]))
            res_add_X[(i_smt_key, j_smt_key)] = add_res_var
            
            mul_res_var = Symbol(f"r_mul_X_lmO4_{i_py_key}{j_py_key}", SMT_INT_TYPE)
            solver.add_assertion(Or([Equals(mul_res_var, val) for val in s_omega_vals]))
            res_mul_X[(i_smt_key, j_smt_key)] = mul_res_var

    print("  2. Asserting Axioms for the symbolic algebra X...")
    print("    Asserting Axioms for oplus_X (forcing it to be AVCA add for Omega=4)...")
    for i_py_key_ax_add in range(omega_py):
        for j_py_key_ax_add in range(omega_py):
            i_smt_key_ax_add, j_smt_key_ax_add = Int(i_py_key_ax_add), Int(j_py_key_ax_add)
            expected_add_res = Int(add_AVCA_Omega4_table_fixed_loose[(i_py_key_ax_add, j_py_key_ax_add)])
            solver.add_assertion(Equals(res_add_X[(i_smt_key_ax_add, j_smt_key_ax_add)], expected_add_res))
    
    print("    Asserting A2_tensor (Commutativity of otimes_X)...")
    for v1_idx in range(omega_py):
        for v2_idx in range(v1_idx + 1, omega_py):
            v1 = s_omega_vals[v1_idx]
            v2 = s_omega_vals[v2_idx]
            solver.add_assertion(Equals(res_mul_X[(v1,v2)], res_mul_X[(v2,v1)]))

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
    
    print("    Asserting Unio annihilator for otimes_X...")
    for x_val in s_omega_vals:
        solver.add_assertion(Equals(res_mul_X[(U_alg, x_val)], U_alg))
        if x_val != U_alg :
             solver.add_assertion(Equals(res_mul_X[(x_val, U_alg)], U_alg))

    print("    Skipping AVCA-specific DFI multiplication outcome rules for otimes_X (LOOSENED AXIOMS).")
    # Explicit DFI outcome rules like 1*1=1, 2*2=U_alg etc. are NOT asserted here.

    print("  3. Asserting that symbolic otimes_X DIFFERS from AVCA-Omega=4 Best Combo Mul...")
    difference_clauses_mul = []
    for i_py_key_diff in range(omega_py):
        for j_py_key_diff in range(omega_py):
            i_smt_key_diff, j_smt_key_diff = Int(i_py_key_diff), Int(j_py_key_diff)
            avca_mul_expected_val = Int(mul_AVCA_Omega4_table_fixed_loose[(i_py_key_diff, j_py_key_diff)])
            difference_clauses_mul.append(Not(Equals(res_mul_X[(i_smt_key_diff, j_smt_key_diff)], avca_mul_expected_val)))
            
    solver.add_assertion(Or(difference_clauses_mul))

    print("  4. Solving (this will be EXTREMELY computationally intensive for Omega=4 with loose mul axioms)...")
    property_holds_uniqueness = False 
    solve_result = solver.solve()
    if not solve_result:
        print("  RESULT: UNSAT. No otimes_X satisfying Totality, Commutativity, Associativity,")
        print("          and U_alg as annihilator (with oplus_X fixed to AVCA add) can differ")
        print("          from the AVCA-Omega=4 Best Combination kernel's multiplication.")
        print("          This implies these abstract axioms are very constraining for Omega=4 (UNEXPECTED for loose DFI rules).")
        property_holds_uniqueness = True
    else:
        print("  RESULT: SAT. An alternative otimes_X was found that satisfies Totality, Comm, Assoc,")
        print("          U_alg annihilator, but differs from AVCA mul_BC (and likely violates AVCA DFI rules).")
        print("          This is EXPECTED and shows AVCA's DFI mul rules are essential constraints.")
        model = solver.get_model()
        print("    Alternative otimes_X table (example - showing only DFIxDIFI part):")
        print("      x\\y |  1  |  2  |  3  ")
        print("      ----|-----|-----|-----")
        for i_val_p in s_omega_vals:
            if i_val_p == U_alg: continue # Skip Unio row for this snippet
            row_str = f"       {i_val_p.constant_value()} | "
            for j_val_p in s_omega_vals:
                 if j_val_p == U_alg: continue # Skip Unio col for this snippet
                 row_str += f"{model.get_value(res_mul_X[(i_val_p, j_val_p)])}   "
            print(row_str)
        property_holds_uniqueness = False
        
    return property_holds_uniqueness

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_C1_Op_Uniqueness_Loose_Mul_O4: ======")
    
    omega_to_test = 4
    
    ops_are_still_unique = test_H_C1_op_uniqueness_loose_mul_O4(omega_to_test)

    print("\n--- Summary of H-C1 (Operational Uniqueness with Looser Mul DFI Rules Test for Omega=4) ---")
    print(f"For Omega = {omega_to_test}:")
    if ops_are_still_unique:
        print("  AVCA multiplication appears UNIQELY DEFINED even with looser DFI outcome constraints,")
        print("  relying mainly on Totality, Commutativity, Associativity, and U_alg as annihilator.")
        print("  This would be a very strong rigidity result for AVCA's multiplicative structure at Omega=4.")
    else:
        print("  An alternative otimes_X (differing from AVCA's) WAS found that satisfies")
        print("  Totality, Commutativity, Associativity, and U_alg as annihilator.")
        print("  This implies AVCA's specific DFI multiplication rules (like 1*1=1, 2*2=U) are ESSENTIAL")
        print("  additional constraints to uniquely define AVCA's multiplication, beyond these abstract axioms.")

    print("\n====== H_C1_Op_Uniqueness_Loose_Mul_O4 Script Finished ======")