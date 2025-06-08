from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals,
                             get_model, LT, GE)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode # <--- ADD THIS LINE
from typing import List, Dict, Tuple, Union

# --- Configuration ---
OMEGA_VAL = 3
U_SMT = Int(0)
DFI_SMT_ELEMENTS = [Int(i) for i in range(1, OMEGA_VAL)] # DFI = {1, 2} for Omega=3
S_OMEGA_SMT_ELEMENTS = [U_SMT] + DFI_SMT_ELEMENTS

# --- Helper to get standard AVCA add_v1.1 result (integer representation) ---
def get_std_avca_add_v11_result(val_a_int: int, val_b_int: int, current_omega: int) -> int:
    u_val = 0 # U is 0
    # Simulating Unio identity
    if val_a_int == u_val: return val_b_int
    if val_b_int == u_val: return val_a_int
    
    # Both DFI
    int_sum = val_a_int + val_b_int
    if int_sum < current_omega: # CCA3 (DFI Classicality)
        return int_sum
    else: # CCA4 (DFI Overflow) - sum >= current_omega
        return u_val

def run_fundamental_cycle_tests():
    print(f"--- H_FundamentalCycle SMT Tests for Omega={OMEGA_VAL} ---")
    print(f"S_Omega = {[e.constant_value() for e in S_OMEGA_SMT_ELEMENTS]} (U={U_SMT.constant_value()})")

    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    # Use Python ints as keys for consistency, derived from SMT constants
    s_omega_py_keys = [e.constant_value() for e in S_OMEGA_SMT_ELEMENTS]

    for x_py_key in s_omega_py_keys:
        for y_py_key in s_omega_py_keys:
            alt_add_results[(x_py_key, y_py_key)] = Symbol(f"res_{x_py_key}_{y_py_key}", SMT_INT_TYPE)

    base_assertions = []

    # --- Assert Minimal Cyclical Closure Axioms (CCA1-CCA4) ---

    # CCA1 (Totality): Each res_xy must be one of U_SMT, DFI1_SMT, DFI2_SMT
    for x_py_key in s_omega_py_keys:
        for y_py_key in s_omega_py_keys:
            res_var = alt_add_results[(x_py_key, y_py_key)]
            is_in_s_omega_clauses = [Equals(res_var, smt_elem) for smt_elem in S_OMEGA_SMT_ELEMENTS]
            base_assertions.append(Or(is_in_s_omega_clauses))

    # CCA2 (Two-Sided Identity U_SMT = Int(0)):
    u_py_key = U_SMT.constant_value()
    for x_py_key in s_omega_py_keys:
        x_smt_elem = Int(x_py_key) # Get the SMT constant for x_py_key
        # U @ x = x
        base_assertions.append(Equals(alt_add_results[(u_py_key, x_py_key)], x_smt_elem))
        # x @ U = x
        base_assertions.append(Equals(alt_add_results[(x_py_key, u_py_key)], x_smt_elem))
    
    # --- Corrected CCA3 & CCA4 assertion generation ---
    py_dfi_elements = [val.constant_value() for val in DFI_SMT_ELEMENTS]

    # CCA3 (DFI Classicality below Bound Omega=OMEGA_VAL):
    # If x, y are DFI and x_py + y_py < OMEGA_VAL, then x @ y = x_py + y_py (as SMT Int)
    for dfi_a_py in py_dfi_elements:
        for dfi_b_py in py_dfi_elements:
            py_sum = dfi_a_py + dfi_b_py
            if py_sum < OMEGA_VAL:
                sum_smt_val = Int(py_sum)
                is_valid_dfi_result = any(sum_smt_val.constant_value() == d_smt.constant_value() for d_smt in DFI_SMT_ELEMENTS)
                if is_valid_dfi_result:
                     base_assertions.append(Equals(alt_add_results[(dfi_a_py, dfi_b_py)], sum_smt_val))

    # CCA4 (DFI Overflow to U_SMT = Int(0) beyond Bound Omega=OMEGA_VAL):
    # If x, y are DFI and x_py + y_py >= OMEGA_VAL, then x @ y = U_SMT
    for dfi_a_py in py_dfi_elements:
        for dfi_b_py in py_dfi_elements:
            py_sum = dfi_a_py + dfi_b_py
            if py_sum >= OMEGA_VAL:
                base_assertions.append(Equals(alt_add_results[(dfi_a_py, dfi_b_py)], U_SMT))
    
    print(f"\nApplied {len(base_assertions)} base assertions for CCA1-CCA4.")

    # --- Test A: Uniqueness of the AVCA ⊕-Table ---
    print("\n--- Test A: Uniqueness of ⊕-Table under CCA1-CCA4 ---")
    std_avca_table_omega3_int_keys = {}
    for x_py_key_std in s_omega_py_keys:
        for y_py_key_std in s_omega_py_keys:
            std_avca_table_omega3_int_keys[(x_py_key_std, y_py_key_std)] = \
                get_std_avca_add_v11_result(x_py_key_std, y_py_key_std, OMEGA_VAL)
            
    differs_from_std_clauses = []
    for (x_py_key, y_py_key), std_res_py_val in std_avca_table_omega3_int_keys.items():
        differs_from_std_clauses.append(NotEquals(alt_add_results[(x_py_key, y_py_key)], Int(std_res_py_val)))
    
    assertion_differs = Or(differs_from_std_clauses)

    with Solver(name="z3") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        s.add_assertion(assertion_differs) 
        
        result_A = s.solve()
        print(f"Test A SMT Result: {'SAT (Found a differing table - UNEXPECTED)' if result_A else 'UNSAT (No differing table exists - EXPECTED)'}")
        if not result_A:
            print("  Proof: CCA1-CCA4 uniquely force the standard AVCA ⊕-table for Omega=3.")
        else:
            print("  WARNING: CCA1-CCA4 DO NOT uniquely force the standard AVCA ⊕-table.")
            model = get_model(s)
            if model: # Check if model is not None
                print("  Differing Model Found:")
                for x_py_m in s_omega_py_keys:
                    row_str = f"    {x_py_m} |"
                    for y_py_m in s_omega_py_keys:
                        model_val = model.get_value(alt_add_results[(x_py_m, y_py_m)])
                        row_str += f" {model_val.constant_value() if model_val else '?'}" 
                    print(row_str)
            else:
                print("  Solver returned SAT but no model was available.")


    # --- Test B: Emergent Commutativity ---
    print("\n--- Test B: Emergent Commutativity from CCA1-CCA4 ---")
    non_commutative_clauses = []
    for i in range(len(s_omega_py_keys)):
        for j in range(i + 1, len(s_omega_py_keys)):
            x_py_key = s_omega_py_keys[i]
            y_py_key = s_omega_py_keys[j]
            non_commutative_clauses.append(
                NotEquals(alt_add_results[(x_py_key, y_py_key)], 
                          alt_add_results[(y_py_key, x_py_key)])
            )
    assertion_is_non_commutative = Or(non_commutative_clauses) if non_commutative_clauses else FALSE() # Ensure it's FALSE if list is empty

    with Solver(name="z3") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        s.add_assertion(assertion_is_non_commutative) 
        
        result_B = s.solve()
        print(f"Test B SMT Result: {'SAT (Found non-commutative table - UNEXPECTED)' if result_B else 'UNSAT (Table must be commutative - EXPECTED)'}")
        if not result_B:
            print("  Proof: Any table satisfying CCA1-CCA4 for Omega=3 must be commutative.")
        else:
            print("  WARNING: CCA1-CCA4 allow for a non-commutative table.")
            model = get_model(s) 
            if model:
                print("  Non-Commutative Model Found (Error in reasoning if Test A was UNSAT):")
                for x_py_m in s_omega_py_keys:
                    row_str = f"    {x_py_m} |"
                    for y_py_m in s_omega_py_keys:
                        model_val = model.get_value(alt_add_results[(x_py_m, y_py_m)])
                        row_str += f" {model_val.constant_value() if model_val else '?'}"
                    print(row_str)
            else:
                print("  Solver returned SAT but no model was available.")


    # --- Test C: Emergent Non-Associativity ---
    print("\n--- Test C: Emergent Non-Associativity from CCA1-CCA4 ---")
    
    def smt_alt_add_expr(val_a_smt_op: FNode, val_b_smt_op: FNode) -> FNode:
        res_expression = U_SMT 
        for x_py_key_case in s_omega_py_keys:
            for y_py_key_case in s_omega_py_keys:
                condition = And(Equals(val_a_smt_op, Int(x_py_key_case)), 
                                Equals(val_b_smt_op, Int(y_py_key_case)))
                value_for_case = alt_add_results[(x_py_key_case, y_py_key_case)]
                res_expression = Ite(condition, value_for_case, res_expression)
        return res_expression

    all_triplets_are_associative_clauses = []
    counter_example_found_by_hand_c = False

    for x_smt_elem_c in S_OMEGA_SMT_ELEMENTS:
        for y_smt_elem_c in S_OMEGA_SMT_ELEMENTS:
            for z_smt_elem_c in S_OMEGA_SMT_ELEMENTS:
                op_xy_expr = smt_alt_add_expr(x_smt_elem_c, y_smt_elem_c)
                lhs_expr = smt_alt_add_expr(op_xy_expr, z_smt_elem_c)
                op_yz_expr = smt_alt_add_expr(y_smt_elem_c, z_smt_elem_c)
                rhs_expr = smt_alt_add_expr(x_smt_elem_c, op_yz_expr)
                all_triplets_are_associative_clauses.append(Equals(lhs_expr, rhs_expr))
                
                if (x_smt_elem_c.constant_value(), y_smt_elem_c.constant_value(), z_smt_elem_c.constant_value()) == (1,1,2):
                    counter_example_found_by_hand_c = True

    assertion_is_fully_associative = And(all_triplets_are_associative_clauses)
    
    with Solver(name="z3") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        s.add_assertion(assertion_is_fully_associative) 
        
        result_C = s.solve()
        print(f"Test C SMT Result (Asserting Associativity Holds for derived table): {'SAT (Associativity holds - UNEXPECTED for Omega=3)' if result_C else 'UNSAT (Associativity fails - EXPECTED for Omega=3)'}")
        if not result_C:
            print("  Proof: The unique table derived from CCA1-CCA4 for Omega=3 is NON-ASSOCIATIVE.")
            if counter_example_found_by_hand_c:
                 print("  The known counterexample (1,1,2) -> (1⊕1)⊕2 = 0 vs 1⊕(1⊕2) = 1 (using U=0) demonstrates this.")
        else: 
            print("  WARNING: Associativity unexpectedly holds. This implies either the table was not uniquely AVCA-like or there's a logic error.")
            # Adding model printing if SAT for Test C
            model = get_model(s)
            if model:
                print("  Model where associativity holds (UNEXPECTED):")
                for x_py_m in s_omega_py_keys:
                    row_str = f"    {x_py_m} |"
                    for y_py_m in s_omega_py_keys:
                        model_val = model.get_value(alt_add_results[(x_py_m, y_py_m)])
                        row_str += f" {model_val.constant_value() if model_val else '?'}"
                    print(row_str)
            else:
                print("  Solver returned SAT for Test C but no model was available.")


if __name__ == "__main__":
    run_fundamental_cycle_tests()