# Script F.1 (Variant 2): SMT Search for Alternative Commutative Addition Table
# Red-Team Audit: Attack on Claim 5 "Uniqueness of ⊕ table"
# Falsification Strategy: SMT: drop commutativity OR remove rule “a+b<Ω→a+b”;
#                        search for an alternative total identity operation.
# This variant REMOVES the "a+b<Ω→a+b" rule AND ADDS a commutativity constraint.

from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Literal

# --- AVCA Primitives (Simplified for this SMT context) ---
# U_sF1v2 = Int(0)
# D1_sF1v2 = Int(1)
# D2_sF1v2 = Int(2) for Omega=3

# Standard AVCA Add (⊕_v1.1) for comparison table for Ω=3
# U=0, D1=1, D2=2
# AREO_UNIO is algebraically U (0)
std_avc_add_table_omega3_v2: Dict[Tuple[int, int], int] = {
    (0, 0): 0, (0, 1): 1, (0, 2): 2,
    (1, 0): 1, (1, 1): 2, (1, 2): 0, 
    (2, 0): 2, (2, 1): 0, 
              (2, 2): 0  
}


def run_smt_alternative_commutative_add_table_search_f1_v2():
    print("====== Script F.1 (Variant 2): SMT Search for Alternative *Commutative* Addition Table ======")
    print("                (Ω=3, Relaxed DFI-Haven, Commutativity Asserted for alt_add)                ")
    
    omega_val = 3
    U_val = 0
    D1_val = 1
    D2_val = 2
    
    s_omega_py_elements = [U_val, D1_val, D2_val]

    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    for r_py_val in s_omega_py_elements:
        for c_py_val in s_omega_py_elements:
            alt_add_results[(r_py_val, c_py_val)] = Symbol(f"res_v2_{r_py_val}_{c_py_val}", SMT_INT_TYPE)

    assertions = []

    # 1. Assert Totality
    # print("\n1. Asserting Totality for alt_add results:")
    for r_py_val in s_omega_py_elements:
        for c_py_val in s_omega_py_elements:
            res_var = alt_add_results[(r_py_val, c_py_val)]
            assertions.append(Or(Equals(res_var, Int(U_val)),
                                 Equals(res_var, Int(D1_val)),
                                 Equals(res_var, Int(D2_val))))

    # 2. Assert U (Int(0)) is Left and Right Identity
    # print("\n2. Asserting U (0) is Left and Right Identity for alt_add:")
    assertions.append(Equals(alt_add_results[(U_val, U_val)], Int(U_val)))
    assertions.append(Equals(alt_add_results[(U_val, D1_val)], Int(D1_val)))
    assertions.append(Equals(alt_add_results[(U_val, D2_val)], Int(D2_val)))
    assertions.append(Equals(alt_add_results[(D1_val, U_val)], Int(D1_val)))
    assertions.append(Equals(alt_add_results[(D2_val, U_val)], Int(D2_val)))

    # 3. Assert DFI+DFI Overflow Rule (conceptual sum s = val(a)+val(b) >= Ω -> U)
    # print("\n3. Asserting DFI+DFI Overflow Rule (sum >= Ω -> U) for alt_add:")
    # D1+D1 (1+1=2). Rule for sum < Ω is relaxed. Not asserted to be D2.
    assertions.append(Equals(alt_add_results[(D1_val, D2_val)], Int(U_val))) # 1+2=3 -> U
    assertions.append(Equals(alt_add_results[(D2_val, D1_val)], Int(U_val))) # 2+1=3 -> U
    assertions.append(Equals(alt_add_results[(D2_val, D2_val)], Int(U_val))) # 2+2=4 -> U

    # 4. Assert Difference from standard avc_add_v1_1 table for Ω=3
    # print("\n4. Asserting alt_add differs from standard avc_add_v1_1 for at least one pair:")
    difference_clauses = []
    for r_py_val in s_omega_py_elements:
        for c_py_val in s_omega_py_elements:
            std_result = std_avc_add_table_omega3_v2[(r_py_val, c_py_val)]
            difference_clauses.append(NotEquals(alt_add_results[(r_py_val, c_py_val)], Int(std_result)))
    assertions.append(Or(difference_clauses))

    # 5. Assert Commutativity for alt_add
    print("\n5. Asserting Commutativity for alt_add:")
    # Only need to assert for pairs where r_py_val < c_py_val to cover all unique pairs
    commutative_assertions = [
        Equals(alt_add_results[(D1_val, D2_val)], alt_add_results[(D2_val, D1_val)]), # (1,2) vs (2,1)
        Equals(alt_add_results[(U_val, D1_val)], alt_add_results[(D1_val, U_val)]),   # (0,1) vs (1,0)
        Equals(alt_add_results[(U_val, D2_val)], alt_add_results[(D2_val, U_val)])    # (0,2) vs (2,0)
    ]
    # Diagonal elements (U,U), (D1,D1), (D2,D2) are inherently symmetric.
    assertions.extend(commutative_assertions)
    for ca in commutative_assertions:
        print(f"  {ca.serialize()}")


    print("\nAll assertions prepared. Solving with Z3...")
    with Solver(name="z3", logic="LIA") as s: 
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()

        print("\n--- Variant 2: Commutativity Asserted for alt_add (Still Relaxed DFI-Haven) ---")
        if result:
            print("Status: SAT")
            print("  This is a POTENTIAL FALSIFICATION of Claim 5's strongest interpretation (even with commutativity).")
            print("  An alternative *commutative* addition table for Ω=3 was found that:")
            print("    - Is total on S3.")
            print("    - Has U (0) as a two-sided identity.")
            print("    - Maps DFI+DFI sums >= Ω to U.")
            print("    - Differs from standard avc_add_v1_1.")
            print("    - Does NOT necessarily respect DFI+DFI sums < Ω being their integer sum.")
            
            model = s.get_model()
            print("\n  Alternative Commutative 'alt_add' Table for Ω=3 (U=0, D1=1, D2=2):")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_py_val in s_omega_py_elements:
                row_str = f"     {r_py_val}  | "
                for c_py_val in s_omega_py_elements:
                    val = model.get_value(alt_add_results[(r_py_val, c_py_val)])
                    row_str += f" {val}  | "
                print(row_str)
            
            print("\n  Standard avc_add_v1_1 Table for Ω=3 for comparison:")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_py_val_std in s_omega_py_elements:
                row_str_std = f"     {r_py_val_std}  | "
                for c_py_val_std in s_omega_py_elements:
                    val_std = std_avc_add_table_omega3_v2[(r_py_val_std, c_py_val_std)]
                    row_str_std += f" {val_std}  | "
                print(row_str_std)
        else:
            print("Status: UNSAT")
            print("  This means NO alternative *commutative* addition table exists for Ω=3 under these relaxed conditions")
            print("  that still has U as identity, maps overflows (>=Ω) to U, is total, and differs from std avc_add_v1_1.")
            print("  This would strongly support the uniqueness of AVCA's ⊕_v1.1 table if 'classical until overflow'")
            print("  is interpreted as allowing DFI+DFI sums < Ω to be arbitrary (within S_Omega and commutativity) but sums >= Ω must be U.")

    print("\n====== F.1 Script (Variant 2) Finished ======")

if __name__ == "__main__":
    run_smt_alternative_commutative_add_table_search_f1_v2()