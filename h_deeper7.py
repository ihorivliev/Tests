# Test_C3_InvCount_NoComm_OmegaN_v3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, Plus, Ite, NotEquals)
# Removed 'Exactly' and other potentially problematic imports like AtLeastOne, AtMostOne
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple

def get_avca_add_std_table(current_omega: int, U_val_int: int) -> Dict[Tuple[int, int], int]:
    """Generates the standard AVCA-⊕_v1.1 table using integer representations."""
    table: Dict[Tuple[int, int], int] = {}
    
    s_elements_py = [U_val_int]
    if current_omega > 1:
        s_elements_py.extend(list(range(1, current_omega)))
    
    for a_py_key in s_elements_py:
        for b_py_key in s_elements_py:
            a_op = U_val_int if a_py_key == U_val_int else a_py_key
            b_op = U_val_int if b_py_key == U_val_int else b_py_key

            result_val: int
            if a_op == U_val_int: result_val = b_op
            elif b_op == U_val_int: result_val = a_op
            else: 
                sum_val = a_op + b_op
                result_val = sum_val if sum_val < current_omega else U_val_int
            table[(a_py_key, b_py_key)] = result_val
    return table

def run_C3_InvCount_NoComm_test_v3(current_omega: int):
    print(f"====== SCRIPT: Test_C3_InvCount_NoComm_OmegaN_v3.py (Ω={current_omega}) ======")
    print("Purpose: Test if (Id), (Cls_interior), (InvCnt_Law) + RangeTotality")
    print("         uniquely determine the standard (and commutative) AVCA-⊕ table,")
    print("         making (Ovfl) and Commutativity emergent.")
    print("Expected: UNSAT for 'differs from standard table' assertion.\n")

    if current_omega < 1:
        print("Omega must be >= 1. Test skipped.")
        return

    U_val_smt = Int(0) 
    
    s_omega_smt_elements: List[FNode] = [U_val_smt]
    if current_omega > 1:
        s_omega_smt_elements.extend([Int(i) for i in range(1, current_omega)])
    
    dfi_smt_elements: List[FNode] = []
    if current_omega > 1:
        dfi_smt_elements = [Int(i) for i in range(1, current_omega)]

    py_keys: List[int] = [val.constant_value() for val in s_omega_smt_elements]

    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            alt_add_results[(r_py_key, c_py_key)] = Symbol(f"res_add_{r_py_key}_{c_py_key}_O{current_omega}", SMT_INT_TYPE)

    assertions: List[FNode] = []
    print(f"--- Asserting Axioms for Ω={current_omega} (U represented as {U_val_smt.constant_value()}) ---")

    print("1. Asserting Output Range Totality for alt_add_results.")
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            res_var = alt_add_results[(r_py_key, c_py_key)]
            assertions.append(Or([Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]))

    print("2. Asserting (Id) Two-Sided U-Identity for alt_add_results.")
    for x_smt in s_omega_smt_elements:
        x_py_key = x_smt.constant_value() 
        assertions.append(Equals(alt_add_results[(U_val_smt.constant_value(), x_py_key)], x_smt))
        assertions.append(Equals(alt_add_results[(x_py_key, U_val_smt.constant_value())], x_smt))
    
    print("3. Asserting (Cls) DFI Classicality (Interior DFI sums) for alt_add_results.")
    if current_omega > 1: 
        for a_dfi_smt in dfi_smt_elements:
            a_py_key = a_dfi_smt.constant_value()
            for b_dfi_smt in dfi_smt_elements:
                b_py_key = b_dfi_smt.constant_value()
                if a_py_key + b_py_key < current_omega:
                    classical_sum_smt = Int(a_py_key + b_py_key)
                    if classical_sum_smt.constant_value() != U_val_smt.constant_value() and \
                       classical_sum_smt.constant_value() < current_omega :
                        assertions.append(Equals(alt_add_results[(a_py_key, b_py_key)], classical_sum_smt))

    print("4. Asserting (InvCnt) DFI Additive Inverse-Count Law.")
    if current_omega >= 2: 
        for a_dfi_smt_inv_count in dfi_smt_elements: 
            a_py_val_for_count = a_dfi_smt_inv_count.constant_value() 
            
            is_inverse_conditions_for_a: List[FNode] = []
            for x_dfi_smt_potential_inverse in dfi_smt_elements: 
                x_py_key_for_inverse = x_dfi_smt_potential_inverse.constant_value()
                is_inverse_conditions_for_a.append(
                    Equals(alt_add_results[(a_py_val_for_count, x_py_key_for_inverse)], U_val_smt)
                )
            
            if not is_inverse_conditions_for_a: # Should only happen if DFI is empty (omega=1)
                if a_py_val_for_count == 0: # This count is for DFI 'a', so a_py_val_for_count is >= 1
                    pass 
                else: # DFI is empty, but a_py_val_for_count (from an empty dfi_smt_elements loop) is not 0.
                      # This branch should not be hit if current_omega >= 2 as dfi_smt_elements is not empty.
                    print(f"Warning: In InvCnt, is_inverse_conditions_for_a is empty for DFI a={a_py_val_for_count} in Omega={current_omega}. Should not happen for Omega>=2.")
                    assertions.append(FALSE()) 
            else:
                # Implement "exactly N are true" using sum of ITEs
                terms_to_sum = [Ite(cond, Int(1), Int(0)) for cond in is_inverse_conditions_for_a]
                
                current_sum_of_true: FNode
                if not terms_to_sum: # Should not happen if is_inverse_conditions_for_a was not empty
                    current_sum_of_true = Int(0)
                elif len(terms_to_sum) == 1:
                    current_sum_of_true = terms_to_sum[0]
                else:
                    current_sum_of_true = Plus(terms_to_sum) # Plus can take a list of FNodes
                
                assertions.append(Equals(current_sum_of_true, Int(a_py_val_for_count)))
    
    std_avca_add_table = get_avca_add_std_table(current_omega, U_val_smt.constant_value())

    print(f"\n5. Asserting that alt_add_results table DIFFERS from standard AVCA-⊕_v1.1 table for Ω={current_omega}.")
    difference_clauses: List[FNode] = []
    for r_py_key_diff in py_keys:
        for c_py_key_diff in py_keys:
            std_val = std_avca_add_table.get((r_py_key_diff, c_py_key_diff))
            if std_val is not None: 
                 difference_clauses.append(NotEquals(alt_add_results[(r_py_key_diff, c_py_key_diff)], Int(std_val)))
            else:
                print(f"CRITICAL WARNING: Missing standard table value for ({r_py_key_diff}, {c_py_key_diff}) in Omega={current_omega}")
                assertions.append(FALSE()) 
    
    if current_omega == 1:
        print("   (For Omega=1, 'differs' assertion is effectively FALSE, forcing UNSAT if axioms are consistent and lead to the unique table)")
        # The unique table U+U=U cannot differ from itself. So, if axioms force U+U=U,
        # asserting it "differs" (which would be Or() -> False) should lead to UNSAT.
        # To be safe, if difference_clauses is empty, we can assert False().
        if not difference_clauses:
            assertions.append(FALSE()) # This means "it must differ, but there are no cells to differ on" -> contradiction
    elif difference_clauses:
        assertions.append(Or(difference_clauses))
    else: # Omega > 1 but no difference clauses, highly unlikely if py_keys is populated
        print(f"   WARNING: No difference clauses generated for Omega={current_omega} > 1. This is unexpected.")
        assertions.append(FALSE())


    print("\n--- Solving with SMT (Z3) ---")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Test C-3 (Ω={current_omega}, no explicit Comm for alt_add): {'SAT' if result else 'UNSAT'}")

        if result:
            print("  INTERPRETATION: SAT means an alternative table was found that satisfies")
            print("                  (Id), (Cls_interior), (InvCnt_Law), (Range Totality) but differs from std AVCA-⊕.")
            print("                  This would mean these axioms DO NOT uniquely force std AVCA-⊕ (and its emergent Comm & Ovfl).")
            model = s.get_model()
            print(f"\n  Alternative 'alt_add' Table (Model for Ω={current_omega}):")
            header_parts = ["    a\\b |"]
            for k_print in py_keys: header_parts.append(f" {str(k_print).center(max(1,len(str(k_print))))} |")
            print("".join(header_parts))
            
            separator_parts = ["    ----|-"]
            for k_print in py_keys: separator_parts.append("-" * (max(1,len(str(k_print)))+2) + "|")
            print("".join(separator_parts))

            for r_val_key_print in py_keys:
                row_str_parts = [f"     {str(r_val_key_print).ljust(2)}|"]
                for c_val_key_print in py_keys:
                    val_model = model.get_value(alt_add_results[(r_val_key_print, c_val_key_print)])
                    row_str_parts.append(f" {str(val_model.constant_value()).center(max(1,len(str(c_val_key_print))))} |")
                print("".join(row_str_parts))
        else: # UNSAT
            print("  INTERPRETATION: UNSAT means NO alternative table exists that satisfies")
            print("                  (Id), (Cls_interior), (InvCnt_Law), (Range Totality)")
            print("                  AND also differs from the standard AVCA-⊕ table.")
            print("                  This strongly supports C-3: these axioms (including InvCnt_Law)")
            print(f"                  uniquely determine the standard (and commutative) AVCA-⊕ table for Ω={current_omega},")
            print("                  making (Ovfl) DFI Overflow and Commutativity for ⊕ emergent properties.")
    print(f"\n====== Test_C3_InvCount_NoComm_OmegaN_v3.py (Ω={current_omega}) Finished ======")

if __name__ == "__main__":
    run_C3_InvCount_NoComm_test_v3(current_omega=3) 
    print("\n" + "="*70 + "\n")
    run_C3_InvCount_NoComm_test_v3(current_omega=4) 
    print("\n" + "="*70 + "\n")
    run_C3_InvCount_NoComm_test_v3(current_omega=5)
    print("\n" + "="*70 + "\n")
    run_C3_InvCount_NoComm_test_v3(current_omega=2)
    print("\n" + "="*70 + "\n")
    run_C3_InvCount_NoComm_test_v3(current_omega=1)