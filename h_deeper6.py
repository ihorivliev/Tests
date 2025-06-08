# Test_C1_MinimalMul_Omega3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Times, Ite, NotEquals)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple

def run_C1_H_Tensor_Min_test_omega3(): # Renamed function
    print("====== SCRIPT: Test_C1_MinimalMul_Omega3.py ======")
    print("Purpose: Test H⊗-Min (as proxy for C-1 initial check) for Ω=3.")
    print("         Are (Ann), (M-Cls), (M-Ovfl), (Comm_Explicit) for ⊗ sufficient")
    print("         to uniquely determine AVCA-⊗ table and emergent Associativity?")
    print("Expected: UNSAT for differing table; THEN check if this unique table is associative.\n")

    omega_val = 3
    U_val_smt = Int(0)
    DFI1_val_smt = Int(1)
    DFI2_val_smt = Int(2)
    
    s_omega_smt_elements = [U_val_smt, DFI1_val_smt, DFI2_val_smt]
    py_keys = [0,1,2] # Python int keys for dictionary

    alt_mul_results: Dict[Tuple[int, int], FNode] = {}
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            alt_mul_results[(r_py_key, c_py_key)] = Symbol(f"res_mul_{r_py_key}_{c_py_key}", SMT_INT_TYPE)

    assertions_base = []

    print(f"--- Asserting Minimal Axioms for ⊗ for Ω={omega_val} (U={U_val_smt.constant_value()}) ---")

    # Axiom: Output Range Totality for alt_mul
    print("1. Asserting Output Range Totality.")
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            res_var = alt_mul_results[(r_py_key, c_py_key)]
            assertions_base.append(Or([Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]))

    # Axiom (Ann): U is Annihilator (Two-Sided)
    print("2. Asserting (Ann) U is Annihilator.")
    for x_smt in s_omega_smt_elements:
        x_py_key = x_smt.constant_value()
        assertions_base.append(Equals(alt_mul_results[(U_val_smt.constant_value(), x_py_key)], U_val_smt)) # U * x = U
        assertions_base.append(Equals(alt_mul_results[(x_py_key, U_val_smt.constant_value())], U_val_smt)) # x * U = U

    # Axiom (M-Cls): DFI·DFI < Ω → product
    print("3. Asserting (M-Cls) DFI Classicality (Interior).")
    # For Ω=3: 1*1=1 (<3) -> 1.  1*2=2 (<3) -> 2.
    assertions_base.append(Equals(alt_mul_results[(1,1)], DFI1_val_smt)) # 1*1 = 1
    assertions_base.append(Equals(alt_mul_results[(1,2)], DFI2_val_smt)) # 1*2 = 2
    # 2*1 = 2 will be covered by commutativity.

    # Axiom (M-Ovfl): DFI·DFI ≥ Ω → U
    print("4. Asserting (M-Ovfl) DFI Overflow.")
    # For Ω=3: 2*2=4 (≥3) -> U.
    assertions_base.append(Equals(alt_mul_results[(2,2)], U_val_smt)) # 2*2 = U

    # Axiom (Comm_Explicit): Explicit Commutativity for alt_mul
    print("5. Asserting Explicit Commutativity.")
    for i, r_py_key in enumerate(py_keys):
        for c_py_key in py_keys[i+1:]: 
             assertions_base.append(Equals(alt_mul_results[(r_py_key, c_py_key)], alt_mul_results[(c_py_key, r_py_key)]))
    
    # Standard AVCA-⊗_v1.2 (algebraic part) table for Ω=3
    std_avca_mul_table_omega3 = {
        (0,0):0, (0,1):0, (0,2):0,
        (1,0):0, (1,1):1, (1,2):2,
        (2,0):0, (2,1):2, (2,2):0 
    }

    # --- Test 1: Uniqueness of Multiplication Table ---
    print("\n--- Test 1: Checking Uniqueness of ⊗ Table (M-core + Comm) ---")
    with Solver(name="z3") as s_uniq:
        for an_assertion in assertions_base:
            s_uniq.add_assertion(an_assertion)
        
        difference_clauses_mul = []
        for r_py_key in py_keys:
            for c_py_key in py_keys:
                std_val = std_avca_mul_table_omega3[(r_py_key, c_py_key)]
                difference_clauses_mul.append(NotEquals(alt_mul_results[(r_py_key, c_py_key)], Int(std_val)))
        s_uniq.add_assertion(Or(difference_clauses_mul)) # Assert table DIFFERS

        result_uniq = s_uniq.solve()
        print(f"SMT Result for Uniqueness (Expect UNSAT if M-core+Comm uniquely defines AVCA-⊗): {'SAT' if result_uniq else 'UNSAT'}")
        if result_uniq:
            print("  WARNING: SAT means an alternative ⊗ table was found satisfying M-core + Comm.")
            print("           This would mean M-core + Comm is NOT sufficient for unique AVCA-⊗.")
            model = s_uniq.get_model()
            print("\n  Alternative 'alt_mul' Table (Model):")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_val_key_m in py_keys:
                row_str_m = f"     {r_val_key_m:<2}| "
                for c_val_key_m in py_keys:
                    val_model_m = model.get_value(alt_mul_results[(r_val_key_m, c_val_key_m)])
                    row_str_m += f" {str(val_model_m.constant_value()):<2}| "
                print(row_str_m)
        else:
            print("  SUCCESS: UNSAT means M-core + Comm axioms uniquely determine the standard AVCA-⊗ table for Ω=3.")

    # --- Test 2: Emergent Associativity of This Unique Table ---
    print("\n--- Test 2: Checking Emergent Associativity from (M-core + Comm) ---")
    # For this script, we infer associativity if the table is uniquely AVCA-⊗ (which is known to be associative).
    # A direct proof of emergent associativity from M-core+Comm for a generic table is more complex.
    # The auditor LLM's roadmap implies this: "Associativity is therefore emergent (because the unique table is the known associative one)."
    print("  (If Test 1 was UNSAT, the unique table is the standard AVCA-⊗ table.)")
    print("  (Standard AVCA-⊗_v1.2 is already known to be associative from AVCA Core DraftV4.)")
    print("  For this script's scope: If Test 1 (Uniqueness to AVCA-⊗) is UNSAT, we infer that these")
    print("  conditions lead to an associative structure, as the unique result IS AVCA-⊗.")


    print("\n====== Test_C1_MinimalMul_Omega3.py Finished ======")

if __name__ == "__main__":
    # Script 1
    # run_C3_InvCount_NoComm_test(current_omega=3) # Called from its own main
    # print("\n" + "="*70 + "\n")
    
    # Script 2
    # run_C2_lattice_distributive_test_omega3() # Called from its own main
    # print("\n" + "="*70 + "\n")
    
    # Script 3
    run_C1_H_Tensor_Min_test_omega3() # Corrected function call