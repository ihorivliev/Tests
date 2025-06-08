# Test_A2_MinimalMul_NoComm_OmegaN.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, NotEquals)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple

def get_avca_mul_std_table(current_omega: int, U_val_int: int) -> Dict[Tuple[int, int], int]:
    """
    Generates the standard AVCA-⊗_v1.2 table (algebraic U, no specific aspect object).
    Assumes U is annihilator, DFI products < Ω are classical, DFI products >= Ω are U.
    This table IS commutative and associative.
    """
    table: Dict[Tuple[int, int], int] = {}
    s_elements_py = [U_val_int]
    if current_omega > 1:
        s_elements_py.extend(list(range(1, current_omega)))
    
    for a_py_key in s_elements_py:
        for b_py_key in s_elements_py:
            a_op = U_val_int if a_py_key == U_val_int else a_py_key
            b_op = U_val_int if b_py_key == U_val_int else b_py_key

            result_val: int
            if a_op == U_val_int or b_op == U_val_int: # U is annihilator
                result_val = U_val_int
            else: # Both DFI
                prod_val = a_op * b_op
                if 1 <= prod_val < current_omega: # M-Cls
                    result_val = prod_val
                else: # M-Ovfl (prod_val >= current_omega, or < 1 which is not for DFI*DFI)
                    result_val = U_val_int
            table[(a_py_key, b_py_key)] = result_val
    return table

def run_A2_MinimalMul_NoComm_test(current_omega: int):
    print(f"====== SCRIPT: Test_A2_MinimalMul_NoComm_OmegaN.py (Ω={current_omega}) ======")
    print("Purpose: Test if M-core {Ann, M-Cls, M-Ovfl} + RangeTotality for ⊗")
    print("         uniquely determines the standard AVCA-⊗ table, making Commutativity")
    print("         (and Associativity) emergent.")
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

    alt_mul_results: Dict[Tuple[int, int], FNode] = {}
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            alt_mul_results[(r_py_key, c_py_key)] = Symbol(f"res_mul_{r_py_key}_{c_py_key}_O{current_omega}", SMT_INT_TYPE)

    assertions: List[FNode] = []
    print(f"--- Asserting M-core Axioms for ⊗ for Ω={current_omega} (U={U_val_smt.constant_value()}) ---")

    # 1. Output Range Totality
    print("1. Asserting Output Range Totality.")
    for r_py_key in py_keys:
        for c_py_key in py_keys:
            res_var = alt_mul_results[(r_py_key, c_py_key)]
            assertions.append(Or([Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]))

    # 2. (Ann) U is Annihilator (Two-Sided)
    print("2. Asserting (Ann) U is Annihilator.")
    for x_smt in s_omega_smt_elements:
        x_py_key = x_smt.constant_value()
        # U * x = U
        assertions.append(Equals(alt_mul_results[(U_val_smt.constant_value(), x_py_key)], U_val_smt))
        # x * U = U
        assertions.append(Equals(alt_mul_results[(x_py_key, U_val_smt.constant_value())], U_val_smt))
    
    # 3. (M-Cls) DFI·DFI < Ω → product
    print("3. Asserting (M-Cls) DFI Classicality (Interior).")
    if current_omega > 1:
        for a_dfi_smt in dfi_smt_elements:
            a_py_key = a_dfi_smt.constant_value()
            for b_dfi_smt in dfi_smt_elements:
                b_py_key = b_dfi_smt.constant_value()
                # Ensure product is DFI: 1 <= product < current_omega
                # DFI elements are >= 1, so product a_py_key * b_py_key is always >= 1
                if 1 <= (a_py_key * b_py_key) < current_omega:
                    classical_prod_smt = Int(a_py_key * b_py_key)
                    assertions.append(Equals(alt_mul_results[(a_py_key, b_py_key)], classical_prod_smt))

    # 4. (M-Ovfl) DFI·DFI ≥ Ω → U
    print("4. Asserting (M-Ovfl) DFI Overflow.")
    if current_omega > 1:
        for a_dfi_smt_ovfl in dfi_smt_elements:
            a_py_key_ovfl = a_dfi_smt_ovfl.constant_value()
            for b_dfi_smt_ovfl in dfi_smt_elements:
                b_py_key_ovfl = b_dfi_smt_ovfl.constant_value()
                if (a_py_key_ovfl * b_py_key_ovfl) >= current_omega:
                    assertions.append(Equals(alt_mul_results[(a_py_key_ovfl, b_py_key_ovfl)], U_val_smt))
    
    # NO EXPLICIT COMMUTATIVITY FOR alt_mul_results IS ASSERTED HERE.

    std_avca_mul_table = get_avca_mul_std_table(current_omega, U_val_smt.constant_value())

    print(f"\n5. Asserting that alt_mul_results table DIFFERS from standard AVCA-⊗ table for Ω={current_omega}.")
    difference_clauses_mul: List[FNode] = []
    for r_py_key_diff in py_keys:
        for c_py_key_diff in py_keys:
            std_val = std_avca_mul_table.get((r_py_key_diff, c_py_key_diff))
            if std_val is not None:
                 difference_clauses_mul.append(NotEquals(alt_mul_results[(r_py_key_diff, c_py_key_diff)], Int(std_val)))
            else:
                print(f"CRITICAL WARNING: Missing standard mul table value for ({r_py_key_diff}, {c_py_key_diff}) in Omega={current_omega}")
                assertions.append(FALSE())
    
    if current_omega == 1: # Only U*U=U, cannot differ if axioms above hold
        if not difference_clauses_mul: # Should contain one NotEquals(res_00, 0)
            assertions.append(FALSE()) 
        else:
            assertions.append(Or(difference_clauses_mul))
    elif difference_clauses_mul:
        assertions.append(Or(difference_clauses_mul))
    else: # Should not happen for Omega > 1 if py_keys is populated
        print(f"   WARNING: No difference clauses for mul generated for Omega={current_omega} > 1.")
        assertions.append(FALSE())

    print("\n--- Solving with SMT (Z3) ---")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Test A2 (Ω={current_omega}, M-core for ⊗, no explicit Comm): {'SAT' if result else 'UNSAT'}")

        if result:
            print("  INTERPRETATION: SAT means an alternative ⊗ table was found satisfying M-core")
            print("                  (Ann, M-Cls, M-Ovfl) + RangeTotality that differs from std AVCA-⊗.")
            print("                  This would mean M-core is NOT sufficient to uniquely force")
            print("                  the standard (commutative, associative) AVCA-⊗ table.")
            model = s.get_model()
            print(f"\n  Alternative 'alt_mul' Table (Model for Ω={current_omega}):")
            header_parts = ["    a\\b |"]
            for k_print in py_keys: header_parts.append(f" {str(k_print).center(max(1,len(str(k_print))))} |")
            print("".join(header_parts))
            
            separator_parts = ["    ----|-"]
            for k_print in py_keys: separator_parts.append("-" * (max(1,len(str(k_print)))+2) + "|")
            print("".join(separator_parts))

            for r_val_key_print in py_keys:
                row_str_parts = [f"     {str(r_val_key_print).ljust(2)}|"]
                for c_val_key_print in py_keys:
                    val_model = model.get_value(alt_mul_results[(r_val_key_print, c_val_key_print)])
                    row_str_parts.append(f" {str(val_model.constant_value()).center(max(1,len(str(c_val_key_print))))} |")
                print("".join(row_str_parts))
        else: # UNSAT
            print("  INTERPRETATION: UNSAT means NO alternative table exists that satisfies M-core")
            print("                  (Ann, M-Cls, M-Ovfl) + RangeTotality AND also differs from std AVCA-⊗.")
            print("                  This strongly supports H⊗-Min: M-core axioms uniquely determine")
            print(f"                  the standard AVCA-⊗ table for Ω={current_omega}, making Commutativity")
            print("                  and Associativity for ⊗ emergent properties from these three operational rules.")
    print(f"\n====== Test_A2_MinimalMul_NoComm_OmegaN.py (Ω={current_omega}) Finished ======")

if __name__ == "__main__":
    # Per auditor roadmap task A2: Remove Comm from MinimalMul; Ω = 3, 4, 5. Expected UNSAT.
    run_A2_MinimalMul_NoComm_test(current_omega=3) 
    print("\n" + "="*70 + "\n")
    run_A2_MinimalMul_NoComm_test(current_omega=4) 
    print("\n" + "="*70 + "\n")
    run_A2_MinimalMul_NoComm_test(current_omega=5)
    print("\n" + "="*70 + "\n")
    # Sanity checks
    # run_A2_MinimalMul_NoComm_test(current_omega=2) 
    # print("\n" + "="*70 + "\n")
    # run_A2_MinimalMul_NoComm_test(current_omega=1)