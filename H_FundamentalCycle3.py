from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals,
                             get_model, LT, GE)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode 
from typing import List, Dict, Tuple, Union

# --- Global Configuration (will be set in run_fundamental_cycle_tests) ---
U_SMT = Int(0) # Algebraic Unio representation in SMT


# --- Helper to get standard AVCA add_v1.1 result (integer representation) ---
def get_std_avca_add_v11_result(val_a_int: int, val_b_int: int, current_omega_val: int) -> int:
    u_val = U_SMT.constant_value() 

    if val_a_int == u_val: return val_b_int
    if val_b_int == u_val: return val_a_int
    
    int_sum = val_a_int + val_b_int
    
    if int_sum < current_omega_val: 
        # Result must be a DFI, so it must be >= 1 (conceptual DFI value)
        # Our SMT DFI representation is Int(1) ... Int(omega-1)
        if int_sum >= 1: # Check if sum is conceptually a DFI value
             return int_sum
        else: 
            # This should only happen if we somehow allow non-positive DFIs, which we don't.
            # If conceptual DFIs are >=1, then sum of two DFIs is >=2.
            # So if sum < omega, and omega >=2, sum must be >=1.
            # If omega=1, DFIs are empty, this path not taken.
            return int_sum # Should be safe if inputs are valid DFIs
    else: # CCA4 (DFI Overflow) - sum >= current_omega_val
        return u_val

def run_fundamental_cycle_tests(current_omega_val: int):
    print(f"\n--- H_FundamentalCycle SMT Tests for Omega={current_omega_val} ---")

    if current_omega_val < 1:
        print("OMEGA_VAL must be >= 1. Test skipped.")
        return
        
    local_U_SMT = Int(0) 
    local_DFI_SMT_ELEMENTS = [Int(i) for i in range(1, current_omega_val)]
    local_S_OMEGA_SMT_ELEMENTS = [local_U_SMT] + local_DFI_SMT_ELEMENTS
    local_s_omega_py_keys = [e.constant_value() for e in local_S_OMEGA_SMT_ELEMENTS]
    local_py_dfi_elements = [val.constant_value() for val in local_DFI_SMT_ELEMENTS]

    print(f"S_Omega = {local_s_omega_py_keys} (U={local_U_SMT.constant_value()})")
    if not local_py_dfi_elements:
        print("DFI is empty.")

    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    for x_py_key in local_s_omega_py_keys:
        for y_py_key in local_s_omega_py_keys:
            alt_add_results[(x_py_key, y_py_key)] = Symbol(f"res_{x_py_key}_{y_py_key}_w{current_omega_val}", SMT_INT_TYPE)

    base_assertions = []

    # CCA1 (Totality)
    for x_py_key in local_s_omega_py_keys:
        for y_py_key in local_s_omega_py_keys:
            res_var = alt_add_results[(x_py_key, y_py_key)]
            is_in_s_omega_clauses = [Equals(res_var, smt_elem) for smt_elem in local_S_OMEGA_SMT_ELEMENTS]
            base_assertions.append(Or(is_in_s_omega_clauses))

    # CCA2 (Two-Sided Identity U_SMT)
    u_py_key = local_U_SMT.constant_value()
    for x_py_key in local_s_omega_py_keys:
        x_smt_elem = Int(x_py_key) 
        base_assertions.append(Equals(alt_add_results[(u_py_key, x_py_key)], x_smt_elem))
        base_assertions.append(Equals(alt_add_results[(x_py_key, u_py_key)], x_smt_elem))
    
    if local_py_dfi_elements:
        # CCA3 (DFI Classicality below Bound Omega)
        for dfi_a_py in local_py_dfi_elements:
            for dfi_b_py in local_py_dfi_elements:
                py_sum = dfi_a_py + dfi_b_py
                if py_sum < current_omega_val:
                    sum_smt_val = Int(py_sum)
                    is_valid_dfi_result = any(sum_smt_val.constant_value() == d_smt.constant_value() for d_smt in local_DFI_SMT_ELEMENTS)
                    if is_valid_dfi_result:
                         base_assertions.append(Equals(alt_add_results[(dfi_a_py, dfi_b_py)], sum_smt_val))

        # CCA4 (DFI Overflow to U_SMT beyond Bound Omega)
        for dfi_a_py in local_py_dfi_elements:
            for dfi_b_py in local_py_dfi_elements:
                py_sum = dfi_a_py + dfi_b_py
                if py_sum >= current_omega_val:
                    base_assertions.append(Equals(alt_add_results[(dfi_a_py, dfi_b_py)], local_U_SMT))
    
    print(f"\nApplied {len(base_assertions)} base assertions for CCA1-CCA4 for Omega={current_omega_val}.")

    # --- Test A: Uniqueness of the AVCA ⊕-Table ---
    print(f"\n--- Test A (Omega={current_omega_val}): Uniqueness of ⊕-Table under CCA1-CCA4 ---")
    std_avca_table_int_keys = {}
    for x_py_key_std in local_s_omega_py_keys:
        for y_py_key_std in local_s_omega_py_keys:
            std_avca_table_int_keys[(x_py_key_std, y_py_key_std)] = \
                get_std_avca_add_v11_result(x_py_key_std, y_py_key_std, current_omega_val)
            
    differs_from_std_clauses = []
    if not alt_add_results: # Handles Ω=0 if it slipped through, or no cells
        assertion_differs = FALSE()
    else:
        for (x_py_key, y_py_key), std_res_py_val in std_avca_table_int_keys.items():
            differs_from_std_clauses.append(NotEquals(alt_add_results[(x_py_key, y_py_key)], Int(std_res_py_val)))
        assertion_differs = Or(differs_from_std_clauses) if differs_from_std_clauses else FALSE()

    with Solver(name="z3") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        if differs_from_std_clauses : # Only assert difference if there's something to differ from
             s.add_assertion(assertion_differs) 
        
        result_A = s.solve()
        
        print(f"Test A SMT Result: {'SAT (Found a differing table - UNEXPECTED for these axioms)' if result_A else 'UNSAT (No differing table exists - EXPECTED)'}")
        if not result_A:
            print(f"  Proof: CCA1-CCA4 uniquely force the standard AVCA ⊕-table for Omega={current_omega_val}.")
        else:
            print(f"  WARNING: CCA1-CCA4 DO NOT uniquely force the standard AVCA ⊕-table for Omega={current_omega_val}.")
            model = get_model(s)
            if model: 
                print("  Differing Model Found:")
                for x_py_m in local_s_omega_py_keys:
                    row_str = f"    {x_py_m} |"
                    for y_py_m in local_s_omega_py_keys:
                        model_val = model.get_value(alt_add_results[(x_py_m, y_py_m)])
                        row_str += f" {(model_val.constant_value() if model_val else '?'):<2}" 
                    print(row_str)
            else:
                print("  Solver returned SAT but no model was available.")

    # --- Test B: Emergent Commutativity ---
    print(f"\n--- Test B (Omega={current_omega_val}): Emergent Commutativity from CCA1-CCA4 ---")
    non_commutative_cell_clauses = []
    if len(local_s_omega_py_keys) > 1: # Commutativity is trivial for a single element set
        for i in range(len(local_s_omega_py_keys)):
            for j in range(i + 1, len(local_s_omega_py_keys)): 
                x_py_key = local_s_omega_py_keys[i]
                y_py_key = local_s_omega_py_keys[j]
                non_commutative_cell_clauses.append(
                    NotEquals(alt_add_results[(x_py_key, y_py_key)], 
                              alt_add_results[(y_py_key, x_py_key)])
                )
    assertion_is_globally_non_commutative = Or(non_commutative_cell_clauses) if non_commutative_cell_clauses else FALSE()

    with Solver(name="z3") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        s.add_assertion(assertion_is_globally_non_commutative) 
        
        result_B = s.solve()
        print(f"Test B SMT Result: {'SAT (Found non-commutative table - UNEXPECTED for these axioms)' if result_B else 'UNSAT (Table must be commutative - EXPECTED)'}")
        if not result_B:
            print(f"  Proof: Any table satisfying CCA1-CCA4 for Omega={current_omega_val} must be commutative.")
        else:
            print(f"  WARNING: CCA1-CCA4 allow for a non-commutative table for Omega={current_omega_val}.")
            # (Model printing as in Test A if needed for debug)

    # --- Test C: Emergent Associativity / Non-Associativity ---
    print(f"\n--- Test C (Omega={current_omega_val}): Emergent Associativity/Non-Associativity from CCA1-CCA4 ---")
    
    # Memoization cache for smt_alt_add_expr_dynamic
    _smt_alt_add_expr_cache: Dict[Tuple[FNode, FNode, int], FNode] = {}

    def smt_alt_add_expr_dynamic(val_a_smt_op: FNode, val_b_smt_op: FNode, current_omega_val_inner: int,
                                 current_s_omega_py_keys: List[int], current_alt_add_results: Dict[Tuple[int,int],FNode]) -> FNode:
        cache_key = (val_a_smt_op, val_b_smt_op, current_omega_val_inner) # Simple cache key
        if cache_key in _smt_alt_add_expr_cache:
            return _smt_alt_add_expr_cache[cache_key]

        # Build the ITE cascade if not cached
        # Default to U_SMT if no case matches (should be covered by CCA1 for valid inputs to op)
        u_val_for_ite = Int(0) # Assuming U is always 0 for keying
        
        # Start with the result of the last possible cell (e.g., (Ω-1) + (Ω-1))
        # This is tricky because the alt_add_results are variables.
        # The ITE must be built from the symbolic variables `alt_add_results`.
        if not current_s_omega_py_keys: # Should not happen for omega >=1
            _smt_alt_add_expr_cache[cache_key] = u_val_for_ite 
            return u_val_for_ite

        # Build ITE from specific to general or an arbitrary order
        # Iterating through all keys and building nested ITEs
        res_expression = current_alt_add_results[(current_s_omega_py_keys[-1], current_s_omega_py_keys[-1])] # Default to last cell's var

        for x_py_key_case in reversed(current_s_omega_py_keys): # Iterate to build nested ITEs
            for y_py_key_case in reversed(current_s_omega_py_keys):
                condition = And(Equals(val_a_smt_op, Int(x_py_key_case)), 
                                Equals(val_b_smt_op, Int(y_py_key_case)))
                value_for_case = current_alt_add_results[(x_py_key_case, y_py_key_case)]
                if x_py_key_case == current_s_omega_py_keys[-1] and y_py_key_case == current_s_omega_py_keys[-1]:
                    res_expression = Ite(condition, value_for_case, u_val_for_ite) # Base for the last cell
                else:
                    res_expression = Ite(condition, value_for_case, res_expression)
        
        _smt_alt_add_expr_cache[cache_key] = res_expression
        return res_expression

    all_triplets_are_associative_clauses = []
    if not local_S_OMEGA_SMT_ELEMENTS: 
        assertion_is_fully_associative = TRUE()
    else:
        _smt_alt_add_expr_cache.clear() # Clear cache for current Omega
        for x_smt_elem_c in local_S_OMEGA_SMT_ELEMENTS:
            for y_smt_elem_c in local_S_OMEGA_SMT_ELEMENTS:
                for z_smt_elem_c in local_S_OMEGA_SMT_ELEMENTS:
                    op_xy_expr = smt_alt_add_expr_dynamic(x_smt_elem_c, y_smt_elem_c, current_omega_val, local_s_omega_py_keys, alt_add_results)
                    lhs_expr = smt_alt_add_expr_dynamic(op_xy_expr, z_smt_elem_c, current_omega_val, local_s_omega_py_keys, alt_add_results)
                    op_yz_expr = smt_alt_add_expr_dynamic(y_smt_elem_c, z_smt_elem_c, current_omega_val, local_s_omega_py_keys, alt_add_results)
                    rhs_expr = smt_alt_add_expr_dynamic(x_smt_elem_c, op_yz_expr, current_omega_val, local_s_omega_py_keys, alt_add_results)
                    all_triplets_are_associative_clauses.append(Equals(lhs_expr, rhs_expr))
        assertion_is_fully_associative = And(all_triplets_are_associative_clauses) if all_triplets_are_associative_clauses else TRUE()
    
    with Solver(name="z3") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        s.add_assertion(assertion_is_fully_associative) 
        
        result_C = s.solve()
        
        expected_associativity_holds = (current_omega_val <= 2)
        
        if expected_associativity_holds:
            print(f"Test C SMT Result (Asserting Associativity Holds): {'SAT (Associativity holds - EXPECTED)' if result_C else 'UNSAT (Associativity fails - UNEXPECTED for Omega<=2)'}")
            if result_C:
                print(f"  Proof: The unique table from CCA1-CCA4 for Omega={current_omega_val} IS ASSOCIATIVE.")
            else:
                print(f"  WARNING: Associativity unexpectedly FAILS for Omega={current_omega_val}.")
        else: 
            print(f"Test C SMT Result (Asserting Associativity Holds): {'SAT (Associativity holds - UNEXPECTED for Omega>=3)' if result_C else 'UNSAT (Associativity fails - EXPECTED for Omega>=3)'}")
            if not result_C:
                print(f"  Proof: The unique table from CCA1-CCA4 for Omega={current_omega_val} IS NON-ASSOCIATIVE.")
            else:
                print(f"  WARNING: Associativity unexpectedly HOLDS for Omega={current_omega_val}.")
                # (Model printing as in Test A if needed for debug)

if __name__ == "__main__":
    run_fundamental_cycle_tests(1)
    run_fundamental_cycle_tests(2)
    # Test Omega=3 was previously verified and successful
    # print("\nSkipping Omega=3 (already verified)") 
    run_fundamental_cycle_tests(4) # Already verified
    print("\nRunning for Omega=5 (new test)")
    run_fundamental_cycle_tests(5)