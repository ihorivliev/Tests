# Test_C3_InverseCount_Omega3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals) # Removed Sum, ExactlyN was not used but is valid
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple

def run_C3_test_omega3():
    print("====== SCRIPT: Test_C3_InverseCount_Omega3.py ======")
    print("Purpose: Test if (Id), (Cls), (Comm_Explicit), (InvCnt_Law) uniquely determine")
    print("         AVCA-⊕ table for Ω=3, forcing (Ovfl) as emergent.")
    print("Expected: UNSAT if these axioms uniquely force the standard AVCA-⊕ table.\n")

    omega_val = 3
    U_val_smt = Int(0)
    DFI1_val_smt = Int(1)
    DFI2_val_smt = Int(2)
    
    s_omega_smt_elements = [U_val_smt, DFI1_val_smt, DFI2_val_smt]
    # dfi_py_elements = [1, 2] # Not directly used in SMT logic below, keys are hardcoded

    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    py_keys = [0, 1, 2] # Using python int keys for the dictionary
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            alt_add_results[(r_py_key, c_py_key)] = Symbol(f"res_add_{r_py_key}_{c_py_key}", SMT_INT_TYPE)

    assertions = []

    print(f"--- Asserting Axioms for Ω={omega_val} (U={U_val_smt.constant_value()}) ---")

    # Axiom: Output Range Totality (all results must be in S_omega)
    print("1. Asserting Output Range Totality for alt_add results.")
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            res_var = alt_add_results[(r_py_key, c_py_key)]
            is_in_s_omega_clauses = [Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]
            assertions.append(Or(is_in_s_omega_clauses))

    # Axiom (Id): Two-Sided U-Identity
    print("2. Asserting (Id) Two-Sided U-Identity for alt_add.")
    for x_smt in s_omega_smt_elements:
        x_py_key = x_smt.constant_value()
        assertions.append(Equals(alt_add_results[(U_val_smt.constant_value(), x_py_key)], x_smt)) # U + x = x
        assertions.append(Equals(alt_add_results[(x_py_key, U_val_smt.constant_value())], x_smt)) # x + U = x
    
    # Axiom (Cls): DFI Classicality (Interior: sum < Ω)
    # For Ω=3, only 1+1=2 < 3.
    print("3. Asserting (Cls) DFI Classicality (1+1=2) for alt_add.")
    assertions.append(Equals(alt_add_results[(1,1)], DFI2_val_smt)) # 1 + 1 = 2

    # Axiom (Comm_Explicit): Explicit Commutativity for alt_add
    print("4. Asserting Explicit Commutativity for alt_add.")
    for i, r_py_key in enumerate(py_keys):
        for c_py_key in py_keys[i+1:]: # Only for j > i to avoid redundant/conflicting a=b asserts
             assertions.append(Equals(alt_add_results[(r_py_key, c_py_key)], alt_add_results[(c_py_key, r_py_key)]))

    # Axiom (InvCnt): DFI Additive Inverse-Count Law
    # |{x∈DFI | a⊕x=U}| = a_val
    print("5. Asserting (InvCnt) DFI Additive Inverse-Count Law.")
    # For a=1 (DFI1), count of DFI x in {DFI1, DFI2} such that 1⊕x=U must be 1.
    is_1_plus_1_U = Equals(alt_add_results[(1,1)], U_val_smt)
    is_1_plus_2_U = Equals(alt_add_results[(1,2)], U_val_smt)
    # ExactlyOne takes a list of Booleans.
    assertions.append(ExactlyOne([is_1_plus_1_U, is_1_plus_2_U]))


    # For a=2 (DFI2), count of DFI x in {DFI1, DFI2} such that 2⊕x=U must be 2.
    is_2_plus_1_U = Equals(alt_add_results[(2,1)], U_val_smt)
    is_2_plus_2_U = Equals(alt_add_results[(2,2)], U_val_smt)
    assertions.append(And(is_2_plus_1_U, is_2_plus_2_U)) # Both must be true

    # Standard AVCA-⊕ table for Ω=3 (U=0, DFI1=1, DFI2=2)
    std_avca_add_table_omega3 = {
        (0,0):0, (0,1):1, (0,2):2,
        (1,0):1, (1,1):2, (1,2):0, 
        (2,0):2, (2,1):0, (2,2):0  
    }

    print("\n6. Asserting that alt_add_results table DIFFERS from standard AVCA-⊕ table.")
    difference_clauses = []
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            std_val = std_avca_add_table_omega3[(r_py_key, c_py_key)]
            difference_clauses.append(NotEquals(alt_add_results[(r_py_key, c_py_key)], Int(std_val)))
    assertions.append(Or(difference_clauses))
    
    print("\n--- Solving with SMT (Z3) ---")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Test C-3 (Ω=3): {'SAT' if result else 'UNSAT'}")

        if result:
            print("  INTERPRETATION: SAT means an alternative table was found that satisfies")
            print("                  (Id), (Cls for 1+1=2), (Comm_Explicit), (InvCnt_Law), and (Range Totality)")
            print("                  AND differs from the standard AVCA-⊕ table.")
            print("                  This would mean C-3 (that these axioms uniquely force std AVCA-⊕) is FALSE for Ω=3.")
            model = s.get_model()
            print("\n  Alternative 'alt_add' Table (Model):")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_val_key in py_keys:
                row_str = f"     {r_val_key:<2}| "
                for c_val_key in py_keys:
                    val_model = model.get_value(alt_add_results[(r_val_key, c_val_key)])
                    row_str += f" {str(val_model.constant_value()):<2}| "
                print(row_str)
        else: # UNSAT
            print("  INTERPRETATION: UNSAT means NO alternative table exists that satisfies")
            print("                  (Id), (Cls for 1+1=2), (Comm_Explicit), (InvCnt_Law), and (Range Totality)")
            print("                  AND also differs from the standard AVCA-⊕ table.")
            print("                  This strongly supports C-3: these axioms (including InvCnt_Law)")
            print("                  uniquely determine the standard AVCA-⊕ table for Ω=3,")
            print("                  making the (Ovfl) DFI Overflow rules emergent properties.")
    print("\n====== Test_C3_InverseCount_Omega3.py Finished ======")

if __name__ == "__main__":
    run_C3_test_omega3()