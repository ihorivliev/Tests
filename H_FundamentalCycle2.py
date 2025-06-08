from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals,
                             get_model, LT, GE)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Global Configuration (will be set in run_fundamental_cycle_tests) ---
# OMEGA_VAL = 0 
U_SMT = Int(0) # Algebraic Unio representation in SMT
# DFI_SMT_ELEMENTS = []
# S_OMEGA_SMT_ELEMENTS = []
# s_omega_py_keys = []
# py_dfi_elements = []


# --- Helper to get standard AVCA add_v1.1 result (integer representation) ---
def get_std_avca_add_v11_result(val_a_int: int, val_b_int: int, current_omega_val: int) -> int:
    u_val = U_SMT.constant_value() # Use the SMT constant for U's value

    if val_a_int == u_val: return val_b_int
    if val_b_int == u_val: return val_a_int
    
    # Both DFI conceptual values
    # DFI elements are conceptually 1 to current_omega_val-1.
    # Our SMT representation uses Int(1) to Int(current_omega_val-1).
    int_sum = val_a_int + val_b_int # Standard integer sum of conceptual DFI values
    
    if int_sum < current_omega_val: # CCA3 (DFI Classicality)
        # Result must be a DFI, so it must be >= 1
        if int_sum >= 1:
             return int_sum
        else: 
            # This case should not be hit if val_a_int, val_b_int are valid DFIs (>=1)
            # and sum is < current_omega_val. It implies sum became <=0 but not >=omega.
            # For safety, this path should ideally lead to U or be impossible.
            # Given current CCA3, if sum < omega, it's the sum.
            # We assume inputs are valid DFIs (1 to omega-1)
            return int_sum 
    else: # CCA4 (DFI Overflow) - sum >= current_omega_val
        return u_val

def run_fundamental_cycle_tests(current_omega_val: int):
    print(f"\n--- H_FundamentalCycle SMT Tests for Omega={current_omega_val} ---")

    # --- Dynamically set up S_Omega and DFI based on current_omega_val ---
    if current_omega_val < 1:
        print("OMEGA_VAL must be >= 1. Test skipped.")
        return
        
    local_U_SMT = Int(0) # Consistent Unio representation
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

    # --- Assert Minimal Cyclical Closure Axioms (CCA1-CCA4) ---
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
    
    # CCA3 (DFI Classicality below Bound Omega)
    if local_py_dfi_elements: # Only if DFI is not empty
        for dfi_a_py in local_py_dfi_elements:
            for dfi_b_py in local_py_dfi_elements:
                py_sum = dfi_a_py + dfi_b_py
                if py_sum < current_omega_val:
                    sum_smt_val = Int(py_sum)
                    # Ensure the sum_val is a valid DFI element in S_OMEGA_SMT_ELEMENTS
                    is_valid_dfi_result = any(sum_smt_val.constant_value() == d_smt.constant_value() for d_smt in local_DFI_SMT_ELEMENTS)
                    if is_valid_dfi_result: # Sum must be one of the defined DFI SMT constants
                         base_assertions.append(Equals(alt_add_results[(dfi_a_py, dfi_b_py)], sum_smt_val))
                    # else: e.g. if current_omega_val=2, DFI={1}. 1+1=2. py_sum < 2 is false.
                    # No classical DFI sum for Omega=2.

    # CCA4 (DFI Overflow to U_SMT beyond Bound Omega)
    if local_py_dfi_elements: # Only if DFI is not empty
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
    if not std_avca_table_int_keys and not alt_add_results : # Handle Omega=0 case if it ever gets here by mistake
         pass # No table to compare
    elif not std_avca_table_int_keys and alt_add_results: # Should not happen if s_omega_py_keys is populated
        assertion_differs = TRUE() # Force failure if tables mismatch in structure
    elif std_avca_table_int_keys and not alt_add_results: # Should not happen
        assertion_differs = TRUE()
    else:
        for (x_py_key, y_py_key), std_res_py_val in std_avca_table_int_keys.items():
            if (x_py_key, y_py_key) in alt_add_results: # check if key exists if S_Omega was empty
                differs_from_std_clauses.append(NotEquals(alt_add_results[(x_py_key, y_py_key)], Int(std_res_py_val)))
        assertion_differs = Or(differs_from_std_clauses) if differs_from_std_clauses else FALSE() # If no cells, means tables are identical (empty list of diffs)

    with Solver(name="z3") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        if differs_from_std_clauses: # Only add if there are cells to compare
             s.add_assertion(assertion_differs) 
        
        result_A = s.solve()
        # If differs_from_std_clauses is empty, assertion_differs is FALSE.
        # So if base_assertions define a table, and we assert FALSE, it should be UNSAT.
        # Correct logic: if differs_from_std_clauses is empty, it means the base_assertions might have fully constrained alt_add_results to match std_avca_table_int_keys,
        # OR there were no DFI cells to even apply CCA3/4.
        # If assertion_differs is FALSE (no differences possible), result_A being UNSAT implies uniqueness.
        # If assertion_differs has clauses, result_A being UNSAT implies uniqueness.
        expected_A_unsat = True if local_S_OMEGA_SMT_ELEMENTS else False # Expect UNSAT if there are elements
        
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
                        row_str += f" {model_val.constant_value() if model_val else '?'}" 
                    print(row_str)
            else:
                print("  Solver returned SAT but no model was available.")

    # --- Test B: Emergent Commutativity ---
    print(f"\n--- Test B (Omega={current_omega_val}): Emergent Commutativity from CCA1-CCA4 ---")
    non_commutative_cell_clauses = []
    for i in range(len(local_s_omega_py_keys)):
        for j in range(i + 1, len(local_s_omega_py_keys)): # Unique pairs (x_py_key < y_py_key conceptually)
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
    print(f"\n--- Test C (Omega={current_omega_val}): Emergent Associativity from CCA1-CCA4 ---")
    
    def smt_alt_add_expr_dynamic(val_a_smt_op: FNode, val_b_smt_op: FNode, current_omega_val_inner: int) -> FNode:
        # Default needed if S_Omega is empty (though current_omega_val >= 1 prevents this)
        res_expression = Int(0) if current_omega_val_inner > 0 else Int(0) # default to U_SMT or arbitrary if no elements
        
        # Need to re-fetch these based on current_omega_val_inner if this func is truly general
        # For this script, they are effectively global to run_fundamental_cycle_tests call
        inner_s_omega_py_keys = [Int(i).constant_value() for i in range(current_omega_val_inner)]
        if 0 not in inner_s_omega_py_keys: # Assuming U=0 for keying
            inner_s_omega_py_keys = [0] + [k for k in inner_s_omega_py_keys if k !=0]
            inner_s_omega_py_keys.sort()


        # Construct the ITE cascade in reverse for potentially better SMT handling
        # Start with a base case, e.g., the last cell in the conceptual table.
        # This is complex to make truly general for any Omega via simple ITE.
        # A direct mapping for Omega=1,2,4 would be more robust here if general ITE fails.
        
        # Fallback: for small Omega, explicitly build the ITE
        if current_omega_val_inner == 1: # S_Omega = {0}
            return alt_add_results[(0,0)] # which is U_SMT by CCA2
        elif current_omega_val_inner == 2: # S_Omega = {0,1}
            key_map = {(0,0):0, (0,1):1, (1,0):1, (1,1):0} # From std AVCA Omega=2
            res_expression = alt_add_results[(1,1)] # start with an arbitrary cell's variable
            for x_k in [0,1]:
                for y_k in [0,1]:
                    cond = And(Equals(val_a_smt_op, Int(x_k)), Equals(val_b_smt_op, Int(y_k)))
                    res_expression = Ite(cond, alt_add_results[(x_k,y_k)], res_expression)
            return res_expression
        elif current_omega_val_inner == 3: # S_Omega = {0,1,2}
            res_expression = alt_add_results[(2,2)] # start with an arbitrary cell's variable
            for x_k in [0,1,2]:
                for y_k in [0,1,2]:
                    cond = And(Equals(val_a_smt_op, Int(x_k)), Equals(val_b_smt_op, Int(y_k)))
                    res_expression = Ite(cond, alt_add_results[(x_k,y_k)], res_expression)
            return res_expression
        elif current_omega_val_inner == 4: # S_Omega = {0,1,2,3}
            res_expression = alt_add_results[(3,3)]
            for x_k in [0,1,2,3]:
                for y_k in [0,1,2,3]:
                    cond = And(Equals(val_a_smt_op, Int(x_k)), Equals(val_b_smt_op, Int(y_k)))
                    res_expression = Ite(cond, alt_add_results[(x_k,y_k)], res_expression)
            return res_expression
        else: # Should not happen for this test plan
            raise ValueError(f"smt_alt_add_expr_dynamic not explicitly handled for Omega={current_omega_val_inner}")


    all_triplets_are_associative_clauses = []
    if not local_S_OMEGA_SMT_ELEMENTS: # Omega=0 case
        assertion_is_fully_associative = TRUE() # Vacuously true
    else:
        for x_smt_elem_c in local_S_OMEGA_SMT_ELEMENTS:
            for y_smt_elem_c in local_S_OMEGA_SMT_ELEMENTS:
                for z_smt_elem_c in local_S_OMEGA_SMT_ELEMENTS:
                    op_xy_expr = smt_alt_add_expr_dynamic(x_smt_elem_c, y_smt_elem_c, current_omega_val)
                    lhs_expr = smt_alt_add_expr_dynamic(op_xy_expr, z_smt_elem_c, current_omega_val)
                    op_yz_expr = smt_alt_add_expr_dynamic(y_smt_elem_c, z_smt_elem_c, current_omega_val)
                    rhs_expr = smt_alt_add_expr_dynamic(x_smt_elem_c, op_yz_expr, current_omega_val)
                    all_triplets_are_associative_clauses.append(Equals(lhs_expr, rhs_expr))
        assertion_is_fully_associative = And(all_triplets_are_associative_clauses) if all_triplets_are_associative_clauses else TRUE()
    
    with Solver(name="z3") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        s.add_assertion(assertion_is_fully_associative) 
        
        result_C = s.solve()
        
        expected_associativity_holds = (current_omega_val <= 2)
        
        if expected_associativity_holds:
            print(f"Test C SMT Result (Asserting Associativity Holds for derived table): {'SAT (Associativity holds - EXPECTED)' if result_C else 'UNSAT (Associativity fails - UNEXPECTED for Omega<=2)'}")
            if result_C:
                print(f"  Proof: The unique table derived from CCA1-CCA4 for Omega={current_omega_val} IS ASSOCIATIVE.")
            else:
                print(f"  WARNING: Associativity unexpectedly FAILS for Omega={current_omega_val}.")
        else: # Expect non-associativity (current_omega_val >= 3)
            print(f"Test C SMT Result (Asserting Associativity Holds for derived table): {'SAT (Associativity holds - UNEXPECTED for Omega>=3)' if result_C else 'UNSAT (Associativity fails - EXPECTED for Omega>=3)'}")
            if not result_C:
                print(f"  Proof: The unique table derived from CCA1-CCA4 for Omega={current_omega_val} IS NON-ASSOCIATIVE.")
            else:
                print(f"  WARNING: Associativity unexpectedly HOLDS for Omega={current_omega_val}.")

if __name__ == "__main__":
    run_fundamental_cycle_tests(1)
    run_fundamental_cycle_tests(2)
    # run_fundamental_cycle_tests(3) # Already verified
    run_fundamental_cycle_tests(4)