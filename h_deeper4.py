# Test_C3_InvCount_NoComm_OmegaN.py (Corrected Imports & ExactlyN logic)
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, Plus, Ite, NotEquals)
# Removed AtLeastOne, AtMostOne, and the problematic Exactly/ExactlyN from direct import
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple

def get_avca_add_std_table(current_omega: int, U_val: int) -> Dict[Tuple[int, int], int]:
    """Generates the standard AVCA-⊕_v1.1 table (algebraic U)."""
    table = {}
    s_elements_py = [U_val] + list(range(1, current_omega))
    if current_omega == 1:
        s_elements_py = [U_val]

    for a_py_key_map in s_elements_py:
        for b_py_key_map in s_elements_py:
            a_op = U_val if a_py_key_map == U_val else a_py_key_map
            b_op = U_val if b_py_key_map == U_val else b_py_key_map

            if a_op == U_val: result_val = b_op
            elif b_op == U_val: result_val = a_op
            else: # Both DFI
                sum_val = a_op + b_op
                result_val = sum_val if sum_val < current_omega else U_val
            table[(a_py_key_map, b_py_key_map)] = result_val
    return table

def run_C3_InvCount_NoComm_test(current_omega: int):
    print(f"====== SCRIPT: Test_C3_InvCount_NoComm_OmegaN.py (Ω={current_omega}) ======")
    print("Purpose: Test if (Id), (Cls), (InvCnt_Law) uniquely determine AVCA-⊕ table")
    print("         AND force emergent commutativity.")
    print("Expected: UNSAT if these axioms uniquely force the standard (commutative) AVCA-⊕ table.\n")

    if current_omega < 1:
        print("Omega must be >= 1. Test skipped.")
        return

    U_val_smt = Int(0)
    s_omega_smt_elements = [U_val_smt] + [Int(i) for i in range(1, current_omega)]
    if current_omega == 1:
        s_omega_smt_elements = [U_val_smt]
    
    dfi_smt_elements = [Int(i) for i in range(1, current_omega)]
    # Python int keys for the dictionary, matching SMT Int constants
    py_keys = [U_val_smt.constant_value()] + [i.constant_value() for i in dfi_smt_elements]
    if current_omega == 1:
        py_keys = [U_val_smt.constant_value()]


    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            alt_add_results[(r_py_key, c_py_key)] = Symbol(f"res_add_{r_py_key}_{c_py_key}_O{current_omega}", SMT_INT_TYPE)

    assertions = []
    print(f"--- Asserting Axioms for Ω={current_omega} (U={U_val_smt.constant_value()}) ---")

    # 1. Output Range Totality
    print("1. Asserting Output Range Totality.")
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            res_var = alt_add_results[(r_py_key, c_py_key)]
            assertions.append(Or([Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]))

    # 2. (Id) Two-Sided U-Identity
    print("2. Asserting (Id) Two-Sided U-Identity.")
    for x_smt in s_omega_smt_elements:
        x_py_key = x_smt.constant_value() 
        assertions.append(Equals(alt_add_results[(U_val_smt.constant_value(), x_py_key)], x_smt))
        assertions.append(Equals(alt_add_results[(x_py_key, U_val_smt.constant_value())], x_smt))
    
    # 3. (Cls) DFI Classicality (Interior: sum < Ω)
    print("3. Asserting (Cls) DFI Classicality (Interior).")
    if current_omega > 1:
        for a_dfi_smt in dfi_smt_elements:
            a_py_key = a_dfi_smt.constant_value()
            for b_dfi_smt in dfi_smt_elements:
                b_py_key = b_dfi_smt.constant_value()
                if a_py_key + b_py_key < current_omega:
                    classical_sum_smt = Int(a_py_key + b_py_key)
                    assertions.append(Equals(alt_add_results[(a_py_key, b_py_key)], classical_sum_smt))

    # 4. (InvCnt) DFI Additive Inverse-Count Law
    print("4. Asserting (InvCnt) DFI Additive Inverse-Count Law.")
    if current_omega >= 2: 
        for a_dfi_smt_inv in dfi_smt_elements:
            a_py_val_inv = a_dfi_smt_inv.constant_value() 
            is_inverse_conditions = []
            for x_dfi_smt_inv in dfi_smt_elements:
                x_py_key_inv = x_dfi_smt_inv.constant_value()
                is_inverse_conditions.append(Equals(alt_add_results[(a_py_val_inv, x_py_key_inv)], U_val_smt))
            
            if is_inverse_conditions: 
                # Implementing "exactly a_py_val_inv are true"
                # Sum of (Ite(condition, 1, 0)) for all conditions must equal a_py_val_inv
                terms_to_sum = [Ite(cond, Int(1), Int(0)) for cond in is_inverse_conditions]
                if not terms_to_sum: # Should not happen if current_omega >= 2 and dfi_smt_elements is populated
                     if a_py_val_inv == 0 : # e.g. if DFI was empty and count should be 0
                        pass # Correctly no conditions to sum, sum is 0.
                     else: # Should not happen if DFI is populated, but as a guard
                        print(f"Warning: No inverse conditions for DFI a={a_py_val_inv} in Omega={current_omega} InvCnt.")
                        assertions.append(FALSE()) # Should make it UNSAT if this path is wrong
                elif len(terms_to_sum) == 1: # Plus([]) is not valid, Plus([x]) is x
                    assertions.append(Equals(terms_to_sum[0], Int(a_py_val_inv)))
                else:
                    sum_of_true_conditions = Plus(terms_to_sum)
                    assertions.append(Equals(sum_of_true_conditions, Int(a_py_val_inv)))

    std_avca_add_table = get_avca_add_std_table(current_omega, U_val_smt.constant_value())

    print(f"\n5. Asserting that alt_add_results table DIFFERS from standard AVCA-⊕_v1.1 table for Ω={current_omega}.")
    difference_clauses = []
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            std_val = std_avca_add_table.get((r_py_key, c_py_key)) # Use .get for safety
            if std_val is not None:
                 difference_clauses.append(NotEquals(alt_add_results[(r_py_key, c_py_key)], Int(std_val)))
            else: # Should not happen if get_avca_add_std_table is correct
                print(f"Warning: Missing standard table value for ({r_py_key}, {c_py_key})")
    
    if difference_clauses: 
        assertions.append(Or(difference_clauses))
    elif current_omega == 1 and not difference_clauses : 
        print("   (For Omega=1, only one possible table U+U=U, so 'differs' assertion is skipped.)")
        pass
    elif not difference_clauses and current_omega > 0 :
        print(f"   WARNING: No difference clauses generated for Omega={current_omega}. This is unexpected if Omega >= 1.")


    print("\n--- Solving with SMT (Z3) ---")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Test C-3 (Ω={current_omega}, no explicit Comm for alt_add): {'SAT' if result else 'UNSAT'}")

        if result:
            print("  INTERPRETATION: SAT means an alternative table was found that satisfies")
            print("                  (Id), (Cls), (InvCnt_Law), (Range Totality) but differs from std AVCA-⊕.")
            print("                  This would mean these axioms DO NOT uniquely force std AVCA-⊕ (and its emergent Comm & Ovfl).")
            model = s.get_model()
            print(f"\n  Alternative 'alt_add' Table (Model for Ω={current_omega}):")
            header_parts = ["    a\\b |"]
            for k in py_keys: header_parts.append(f" {str(k).center(len(str(k)))} |")
            print("".join(header_parts))
            
            separator_parts = ["    ----|-"]
            for k in py_keys: separator_parts.append("-" * (len(str(k))+2) + "|") #+2 for spaces
            print("".join(separator_parts))

            for r_val_key in py_keys:
                row_str_parts = [f"     {str(r_val_key).ljust(2)}|"]
                for c_val_key in py_keys:
                    val_model = model.get_value(alt_add_results[(r_val_key, c_val_key)])
                    row_str_parts.append(f" {str(val_model.constant_value()).center(len(str(c_val_key)))} |")
                print("".join(row_str_parts))
        else: # UNSAT
            print("  INTERPRETATION: UNSAT means NO alternative table exists that satisfies")
            print("                  (Id), (Cls), (InvCnt_Law), (Range Totality)")
            print("                  AND also differs from the standard AVCA-⊕ table.")
            print("                  This strongly supports C-3: these axioms (including InvCnt_Law)")
            print(f"                  uniquely determine the standard (and commutative) AVCA-⊕ table for Ω={current_omega},")
            print("                  making (Ovfl) DFI Overflow and Commutativity for ⊕ emergent properties.")
    print(f"\n====== Test_C3_InvCount_NoComm_OmegaN.py (Ω={current_omega}) Finished ======")

if __name__ == "__main__":
    run_C3_InvCount_NoComm_test(current_omega=3)
    # print("\n" + "="*70 + "\n")
    # run_C3_InvCount_NoComm_test(current_omega=4) 
    # print("\n" + "="*70 + "\n")
    # run_C3_InvCount_NoComm_test(current_omega=5)