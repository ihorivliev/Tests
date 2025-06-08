# H_C1_Operational_Uniqueness_Test_Omega4.py
# SMT Test for H-C1: Is any algebra X = (S4,oplus',otimes') satisfying GIT Axioms A1-A6
# (interpreted strongly with AVCA DFI/Unio behaviors) necessarily identical to AVCA-Omega=4?

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- AVCA Best Combination Kernel Operations (Python reference for Cayley tables for Omega=4) ---
# Unio_alg = 0, Fp1 = 1, Fp2 = 2, Fp3 = 3

# Best Combo Add (v1.1) Table for Omega=4
add_AVCA_Omega4_table = {
    (0,0):0, (0,1):1, (0,2):2, (0,3):3,
    (1,0):1, (1,1):2, (1,2):3, (1,3):0, # 1+3=4 -> U
    (2,0):2, (2,1):3, (2,2):0, (2,3):0, # 2+2=4 -> U; 2+3=5 -> U
    (3,0):3, (3,1):0, (3,2):0, (3,3):0, # 3+1=4 -> U; 3+2=5 -> U; 3+3=6 -> U
}

# Best Combo Mul (v1.2 - Areo Dominates, alg U is annihilator) Table for Omega=4
mul_AVCA_Omega4_table = {
    (0,0):0, (0,1):0, (0,2):0, (0,3):0,
    (1,0):0, (1,1):1, (1,2):2, (1,3):3,
    (2,0):0, (2,1):2, (2,2):0, (2,3):0, # 2*2=4 -> U; 2*3=6 -> U
    (3,0):0, (3,1):3, (3,2):0, (3,3):0, # 3*2=6 -> U; 3*3=9 -> U
}

def test_H_C1_operational_uniqueness_O4(omega_py: int):
    if omega_py != 4:
        print(f"ERROR: This script is specifically configured for Omega=4. Current Omega={omega_py}.")
        return False 

    print(f"\n--- Testing H-C1 (Operational Uniqueness): Forcing an algebra X to satisfy AVCA Axioms for Omega={omega_py} ---")
    
    solver = Solver(name="z3", solver_options={'timeout': 600000}) # 10 minute timeout
    # omega_smt_val = Int(omega_py) # Not directly used but good for clarity if generalizing
    
    U_alg = Int(0)
    FP1_alg = Int(1)
    FP2_alg = Int(2)
    FP3_alg = Int(3)
    s_omega_vals = [U_alg, FP1_alg, FP2_alg, FP3_alg] # SMT Integer constants

    res_add_X: Dict[Tuple[FNode, FNode], FNode] = {}
    res_mul_X: Dict[Tuple[FNode, FNode], FNode] = {}

    print("  1. Defining symbolic tables for oplus_X and otimes_X...")
    for i_py_key in range(omega_py):
        for j_py_key in range(omega_py):
            i_smt_key, j_smt_key = Int(i_py_key), Int(j_py_key)
            
            add_res_var = Symbol(f"r_add_X_{i_py_key}{j_py_key}", SMT_INT_TYPE)
            solver.add_assertion(Or([Equals(add_res_var, val) for val in s_omega_vals])) # A1 Totality
            res_add_X[(i_smt_key, j_smt_key)] = add_res_var
            
            mul_res_var = Symbol(f"r_mul_X_{i_py_key}{j_py_key}", SMT_INT_TYPE)
            solver.add_assertion(Or([Equals(mul_res_var, val) for val in s_omega_vals])) # A1 Totality
            res_mul_X[(i_smt_key, j_smt_key)] = mul_res_var

    print("  2. Asserting GIT Axioms A1-A6 for the symbolic algebra X...")

    # A3 (Two-sided Identity U_alg for oplus_X)
    for x_val in s_omega_vals:
        solver.add_assertion(Equals(res_add_X[(U_alg, x_val)], x_val))
        solver.add_assertion(Equals(res_add_X[(x_val, U_alg)], x_val))

    # A4 (Classical Regime for oplus_X) for Omega=4: DFI={1,2,3}
    # 1 +_X 1 = 2
    solver.add_assertion(Equals(res_add_X[(FP1_alg, FP1_alg)], FP2_alg))
    # 1 +_X 2 = 3
    solver.add_assertion(Equals(res_add_X[(FP1_alg, FP2_alg)], FP3_alg))
    # 2 +_X 1 = 3
    solver.add_assertion(Equals(res_add_X[(FP2_alg, FP1_alg)], FP3_alg))

    # A5 (Overflow Collapse for oplus_X) for Omega=4
    solver.add_assertion(Equals(res_add_X[(FP1_alg, FP3_alg)], U_alg)) # 1+3=4
    solver.add_assertion(Equals(res_add_X[(FP2_alg, FP2_alg)], U_alg)) # 2+2=4
    solver.add_assertion(Equals(res_add_X[(FP2_alg, FP3_alg)], U_alg)) # 2+3=5
    solver.add_assertion(Equals(res_add_X[(FP3_alg, FP1_alg)], U_alg)) # 3+1=4
    solver.add_assertion(Equals(res_add_X[(FP3_alg, FP2_alg)], U_alg)) # 3+2=5
    solver.add_assertion(Equals(res_add_X[(FP3_alg, FP3_alg)], U_alg)) # 3+3=6
    
    # A2_tensor (Commutativity of otimes_X)
    for v1 in s_omega_vals:
        for v2 in s_omega_vals:
            if v1.constant_value() < v2.constant_value(): # Avoid redundant assertions
                 solver.add_assertion(Equals(res_mul_X[(v1,v2)], res_mul_X[(v2,v1)]))

    # A6 (Associativity of otimes_X)
    print("    Asserting A6 (Associativity of otimes_X)... (64 constraints)")
    assoc_constraints_mul_X = []
    for i_val_outer in s_omega_vals:
        for j_val_outer in s_omega_vals:
            for k_val_outer in s_omega_vals:
                ij_mul_X_sym = res_mul_X[(i_val_outer, j_val_outer)] 
                lhs_final_val_assoc = U_alg # Default
                ite_chain_lhs = res_mul_X[(s_omega_vals[-1], k_val_outer)] # Fallback to last DFI case
                for idx in range(len(s_omega_vals) -1, -1, -1): # Build ITE from inside out
                    val_check = s_omega_vals[idx]
                    branch_if_eq = res_mul_X[(val_check, k_val_outer)]
                    if idx == 0: # Last case in reversed list (U_alg)
                        ite_chain_lhs = Ite(Equals(ij_mul_X_sym, val_check), branch_if_eq, ite_chain_lhs) if idx != len(s_omega_vals)-1 else branch_if_eq
                    else: # Ensure ite_chain_lhs is defined for the first fallback
                         prev_fallback = res_mul_X[(s_omega_vals[0], k_val_outer)] if idx == 1 and len(s_omega_vals) > 1 else ite_chain_lhs
                         ite_chain_lhs = Ite(Equals(ij_mul_X_sym, val_check), branch_if_eq, ite_chain_lhs if idx != len(s_omega_vals)-1 else prev_fallback )


                lhs_final_val_assoc = ite_chain_lhs


                jk_mul_X_sym = res_mul_X[(j_val_outer, k_val_outer)]
                rhs_final_val_assoc = U_alg # Default
                ite_chain_rhs = res_mul_X[(i_val_outer, s_omega_vals[-1])] # Fallback
                for idx in range(len(s_omega_vals) -1, -1, -1):
                    val_check = s_omega_vals[idx]
                    branch_if_eq = res_mul_X[(i_val_outer, val_check)]
                    if idx == 0:
                        ite_chain_rhs = Ite(Equals(jk_mul_X_sym, val_check), branch_if_eq, ite_chain_rhs) if idx != len(s_omega_vals)-1 else branch_if_eq
                    else:
                        prev_fallback = res_mul_X[(i_val_outer, s_omega_vals[0])] if idx == 1 and len(s_omega_vals) > 1 else ite_chain_rhs
                        ite_chain_rhs = Ite(Equals(jk_mul_X_sym, val_check), branch_if_eq, ite_chain_rhs if idx != len(s_omega_vals)-1 else prev_fallback )

                rhs_final_val_assoc = ite_chain_rhs
                assoc_constraints_mul_X.append(Equals(lhs_final_val_assoc, rhs_final_val_assoc))
    
    for constr in assoc_constraints_mul_X:
        solver.add_assertion(constr)

    # Assert AVCA-specific DFI multiplication rules & Unio annihilator for otimes_X
    # U_alg as annihilator:
    for x_val in s_omega_vals:
        solver.add_assertion(Equals(res_mul_X[(U_alg, x_val)], U_alg))
        # solver.add_assertion(Equals(res_mul_X[(x_val, U_alg)], U_alg)) # Covered by commutativity

    # DFI rules for otimes_X for Omega=4:
    solver.add_assertion(Equals(res_mul_X[(FP1_alg, FP1_alg)], FP1_alg)) # 1*1=1 (<4)
    solver.add_assertion(Equals(res_mul_X[(FP1_alg, FP2_alg)], FP2_alg)) # 1*2=2 (<4)
    solver.add_assertion(Equals(res_mul_X[(FP1_alg, FP3_alg)], FP3_alg)) # 1*3=3 (<4)
    # Commutativity covers FP2_alg * FP1_alg, etc.
    solver.add_assertion(Equals(res_mul_X[(FP2_alg, FP2_alg)], U_alg))   # 2*2=4 (>=4), overflow to U_alg
    solver.add_assertion(Equals(res_mul_X[(FP2_alg, FP3_alg)], U_alg))   # 2*3=6 (>=4), overflow to U_alg
    solver.add_assertion(Equals(res_mul_X[(FP3_alg, FP3_alg)], U_alg))   # 3*3=9 (>=4), overflow to U_alg


    # --- Assert Difference from AVCA Best Combo fixed tables ---
    print("  3. Asserting that the symbolic algebra X DIFFERS from AVCA-Omega=4 Best Combo...")
    difference_clauses = []
    for i_py_key_diff in range(omega_py):
        for j_py_key_diff in range(omega_py):
            i_smt_key_diff, j_smt_key_diff = Int(i_py_key_diff), Int(j_py_key_diff)

            avca_add_expected_val = Int(add_AVCA_Omega4_table[(i_py_key_diff, j_py_key_diff)])
            difference_clauses.append(Not(Equals(res_add_X[(i_smt_key_diff, j_smt_key_diff)], avca_add_expected_val)))
            
            avca_mul_expected_val = Int(mul_AVCA_Omega4_table[(i_py_key_diff, j_py_key_diff)])
            difference_clauses.append(Not(Equals(res_mul_X[(i_smt_key_diff, j_smt_key_diff)], avca_mul_expected_val)))
            
    solver.add_assertion(Or(difference_clauses))

    # --- Solve ---
    print("  4. Solving (this will be computationally intensive for Omega=4)...")
    property_holds = False 
    solve_result = solver.solve()
    if not solve_result:
        print("  RESULT: UNSAT. No algebra X satisfying all specified AVCA axioms and DFI/Unio behaviors")
        print("          can differ from the AVCA-Omega=4 Best Combination kernel.")
        print("          This implies operational uniqueness under these strong axiomatic interpretations.")
        property_holds = True
    else:
        print("  RESULT: SAT. An alternative algebra X was found that satisfies the axioms but differs.")
        print("          This is UNEXPECTED if the axioms fully constrain the operations to AVCA's.")
        # Model printing omitted for brevity for Omega=4 due to size (16+16 entries)
        property_holds = False
        
    return property_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_C1_Operational_Uniqueness_Test_Omega4 (v1): ======")
    
    omega_to_test = 4
    
    ops_are_unique = test_H_C1_operational_uniqueness_O4(omega_to_test)

    print("\n--- Summary of H-C1 (Operational Uniqueness Test for Omega=4) ---")
    print(f"For Omega = {omega_to_test}:")
    if ops_are_unique:
        print("  The AVCA Best Combination operations (⊕_BC, ⊗_BC) appear to be UNIQELY DEFINED by")
        print("  the GIT Axioms A1-A6 when interpreted with AVCA's specific DFI/Unio behaviors.")
        print("  This implies any 'collapse ring' satisfying these strong conditions is AVCA-Ω itself.")
        print("  If true, and combined with results on uniqueness of tag-preserving automorphisms,")
        print("  this would strongly support H-C1 for Ω=4 under this interpretation.")
    else:
        print("  An alternative algebra satisfying the axioms but differing from AVCA-Ω was found,")
        print("  OR the SMT solver timed out / encountered an issue, OR the SMT setup has an issue.")
        print("  This would challenge H-C1 or the current interpretation of 'collapse ring' axioms if genuinely SAT.")

    print("\n====== H_C1_Operational_Uniqueness_Test_Omega4 (v1) Script Finished ======")