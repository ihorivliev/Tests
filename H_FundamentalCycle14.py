from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Exists, ForAll,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, LE, NotEquals,
                             get_model)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Global Symbolic Constants ---
U_S = Int(0)

# --- Helper to get standard AVCA add_v1.1 result (integer representation) ---
def get_std_avca_add_v11_result(val_a_int: int, val_b_int: int, current_omega_val: int, u_val_int: int) -> int:
    if val_a_int == u_val_int: return val_b_int
    if val_b_int == u_val_int: return val_a_int
    int_sum = val_a_int + val_b_int
    return int_sum if int_sum < current_omega_val else u_val_int

# --- SMT Helper: Construct ITE cascade for op(val_a, val_b) using symbolic table cells ---
def smt_op_from_symbolic_table(val_a_smt_op: FNode, val_b_smt_op: FNode,
                               current_s_omega_py_keys: List[int],
                               symbolic_table: Dict[Tuple[int,int],FNode]) -> FNode:
    final_else_expr = U_S 
    if not current_s_omega_py_keys: return final_else_expr
    expr = final_else_expr
    for x_key in reversed(current_s_omega_py_keys): 
        for y_key in reversed(current_s_omega_py_keys):
            condition = And(Equals(val_a_smt_op, Int(x_key)), Equals(val_b_smt_op, Int(y_key)))
            value_for_this_cell = symbolic_table[(x_key, y_key)]
            expr = Ite(condition, value_for_this_cell, expr)
    return expr

# --- Helper functions to build assertion lists for Axioms ---
def create_symbolic_table(prefix: str, current_omega_val: int, s_omega_py_keys: List[int]) -> Dict[Tuple[int, int], FNode]:
    table = {}
    for x_k in s_omega_py_keys:
        for y_k in s_omega_py_keys:
            table[(x_k, y_k)] = Symbol(f"{prefix}_{x_k}_{y_k}_w{current_omega_val}", SMT_INT_TYPE)
    return table

def assert_cca1_range(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                      s_omega_py_keys: List[int], s_omega_smt_elements: List[FNode]):
    for x_k in s_omega_py_keys:
        for y_k in s_omega_py_keys:
            res_var = table[(x_k, y_k)]
            assertions_list.append(Or([Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]))

def assert_idr_right_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys:
        assertions_list.append(Equals(table[(x_k, u_py_key)], Int(x_k)))

def assert_idl_left_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys:
        assertions_list.append(Equals(table[(u_py_key, x_k)], Int(x_k)))
        
def assert_cca2_two_sided_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                                   s_omega_py_keys: List[int], u_py_key: int):
    assert_idr_right_identity(assertions_list, table, s_omega_py_keys, u_py_key)
    assert_idl_left_identity(assertions_list, table, s_omega_py_keys, u_py_key)

def assert_cca3_classical_dfi(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              py_dfi_elements: List[int], current_omega_val: int,
                              dfi_smt_elements: List[FNode], omit_cell: Tuple[int,int] = None):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                if omit_cell and (dfi_a_py, dfi_b_py) == omit_cell:
                    continue
                py_sum = dfi_a_py + dfi_b_py
                if py_sum < current_omega_val:
                    sum_smt_val = Int(py_sum)
                    # Ensure the sum is a valid DFI for this Omega before asserting
                    if any(sum_smt_val.constant_value() == d.constant_value() for d in dfi_smt_elements):
                        assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], sum_smt_val))

def assert_cca4_dfi_overflow(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               py_dfi_elements: List[int], current_omega_val: int, local_U_SMT: FNode,
                               omit_cells: List[Tuple[int,int]] = None, only_cells: List[Tuple[int,int]] = None):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                current_cell = (dfi_a_py, dfi_b_py)
                if omit_cells and current_cell in omit_cells:
                    continue
                if only_cells and current_cell not in only_cells: # Assert only for cells in this list
                    continue
                
                py_sum = dfi_a_py + dfi_b_py
                if py_sum >= current_omega_val:
                    assertions_list.append(Equals(table[current_cell], local_U_SMT))

def assert_explicit_commutativity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode], 
                                  s_omega_py_keys: List[int]):
    if len(s_omega_py_keys) > 1:
        for i in range(len(s_omega_py_keys)):
            for j in range(i + 1, len(s_omega_py_keys)):
                k1,k2 = s_omega_py_keys[i], s_omega_py_keys[j]
                assertions_list.append(Equals(table[(k1,k2)], table[(k2,k1)]))

def print_model_table_if_sat(result: bool, solver_model: Union[Dict,None], 
                             table: Dict[Tuple[int,int],FNode], s_omega_py_keys: List[int], 
                             test_name: str, expectation_msg: str, success_msg: str, failure_msg:str):
    outcome = "SAT" if result else "UNSAT"
    final_status_msg = ""
    if "EXPECTED" in expectation_msg: # Check if expectation_msg is not None or empty
        if (result and "SAT" in expectation_msg) or (not result and "UNSAT" in expectation_msg):
            final_status_msg = success_msg
        else:
            final_status_msg = failure_msg
    else:
        final_status_msg = "Status unclear (expectation_msg not set)."


    print(f"  SMT Result: {outcome} ({expectation_msg})")
    print(f"    {final_status_msg}")

    if result and solver_model:
        print("    Model Table Found:")
        header = "⊕ |" + "".join([f" {str(k):<2}" for k in s_omega_py_keys])
        print(f"    {header}")
        print(f"    ---" + "".join(["----" for _ in s_omega_py_keys]))
        for x_k in s_omega_py_keys:
            row_str = f"    {str(x_k):<2}|"
            for y_k in s_omega_py_keys:
                val_node = table.get((x_k,y_k))
                val = solver_model.get_value(val_node) if val_node is not None else None
                row_str += f" {str(val.constant_value() if val else '?'):<2}"
            print(row_str)
    elif result and not solver_model:
        print("    Solver returned SAT but no model was available.")

# --- Main test function for "Axiom Component Necessity" tests ---
def run_axiom_component_necessity_tests(current_omega_val: int):
    print(f"\n--- Axiom Component Necessity Tests for Omega={current_omega_val} ---")

    if current_omega_val < 1: print("OMEGA_VAL must be >= 1."); return
        
    local_U_SMT = Int(0) 
    local_DFI_SMT_ELEMENTS = [Int(i) for i in range(1, current_omega_val)]
    local_S_OMEGA_SMT_ELEMENTS = [local_U_SMT] + local_DFI_SMT_ELEMENTS
    local_s_omega_py_keys = [e.constant_value() for e in local_S_OMEGA_SMT_ELEMENTS]
    local_py_dfi_elements = [val.constant_value() for val in local_DFI_SMT_ELEMENTS]

    print(f"S_Omega = {local_s_omega_py_keys} (U={local_U_SMT.constant_value()})")
    if not local_py_dfi_elements: print("DFI is empty.")

    STD_AVCA_TABLE = {}
    for x_k_std in local_s_omega_py_keys:
        for y_k_std in local_s_omega_py_keys:
            STD_AVCA_TABLE[(x_k_std, y_k_std)] = get_std_avca_add_v11_result(x_k_std, y_k_std, current_omega_val, local_U_SMT.constant_value())

    # --- Test N-IdL (Necessity of Left-Identity U⊕x = x from CCA2_TwoSided) ---
    print(f"\n--- Test N-IdL (Omega={current_omega_val}): Weakening CCA2 to Right-Identity Only ---")
    R_acn_idl = create_symbolic_table("nIdL", current_omega_val, local_s_omega_py_keys)
    assertions_acn_idl = []
    assert_cca1_range(assertions_acn_idl, R_acn_idl, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_idr_right_identity(assertions_acn_idl, R_acn_idl, local_s_omega_py_keys, local_U_SMT.constant_value()) # ONLY Right ID
    assert_cca3_classical_dfi(assertions_acn_idl, R_acn_idl, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS) 
    assert_cca4_dfi_overflow(assertions_acn_idl, R_acn_idl, local_py_dfi_elements, current_omega_val, local_U_SMT)      

    list_for_fails_left_id = [NotEquals(R_acn_idl[(local_U_SMT.constant_value(), x_k)], Int(x_k)) for x_k in local_s_omega_py_keys if (local_U_SMT.constant_value(),x_k) in R_acn_idl]
    fails_left_id_nid = Or(list_for_fails_left_id) if list_for_fails_left_id else FALSE()
    
    non_comm_clauses_nid = []
    if len(local_s_omega_py_keys) > 1:
        for i in range(len(local_s_omega_py_keys)):
            for j in range(i + 1, len(local_s_omega_py_keys)):
                k1,k2 = local_s_omega_py_keys[i], local_s_omega_py_keys[j]
                non_comm_clauses_nid.append(NotEquals(R_acn_idl[(k1,k2)], R_acn_idl[(k2,k1)]))
    fails_commutativity_nid = Or(non_comm_clauses_nid) if non_comm_clauses_nid else FALSE()
    
    list_for_differs_std = [NotEquals(R_acn_idl[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in R_acn_idl]
    differs_from_std_nid = Or(list_for_differs_std) if list_for_differs_std else FALSE()
    
    assertion_bad_model_nid = Or(fails_left_id_nid, fails_commutativity_nid, differs_from_std_nid)
    if not (fails_left_id_nid.is_or() or fails_left_id_nid.is_not() or \
            fails_commutativity_nid.is_or() or fails_commutativity_nid.is_not() or \
            differs_from_std_nid.is_or() or differs_from_std_nid.is_not()):
        assertion_bad_model_nid = FALSE()

    with Solver(name="z3") as s:
        for a_assertion in assertions_acn_idl: s.add_assertion(a_assertion)
        s.add_assertion(assertion_bad_model_nid) 
        result_ind1 = s.solve()
        print_model_table_if_sat(result_ind1, s.get_model() if result_ind1 else None, R_acn_idl, local_s_omega_py_keys,
                                 "Test N-IdL", "SAT (Bad model found - EXPECTED)",
                                 "Proof: Omitting Left-Identity from CCA2 allows degenerate tables.",
                                 "UNSAT (Only standard table - UNEXPECTED, Left-ID not necessary?)")

    # --- Test N-Cls.lit (Necessity of a specific Cls literal, e.g., 1⊕1=2 for Ω=3) ---
    if current_omega_val == 3 : 
        print(f"\n--- Test N-Cls.lit (Omega={current_omega_val}): Necessity of CCA3 literal (1+1=2) ---")
        R_acn_cls = create_symbolic_table("nCls", current_omega_val, local_s_omega_py_keys)
        assertions_acn_cls = []
        assert_cca1_range(assertions_acn_cls, R_acn_cls, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_acn_cls, R_acn_cls, local_s_omega_py_keys, local_U_SMT.constant_value())
        assert_cca3_classical_dfi(assertions_acn_cls, R_acn_cls, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS, omit_cell=(1,1)) # Omit 1+1=2
        assert_cca4_dfi_overflow(assertions_acn_cls, R_acn_cls, local_py_dfi_elements, current_omega_val, local_U_SMT) 
        assert_explicit_commutativity(assertions_acn_cls, R_acn_cls, local_s_omega_py_keys)

        list_differs_cls = [NotEquals(R_acn_cls[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in R_acn_cls]
        assertion_differs_acn_cls = Or(list_differs_cls) if list_differs_cls else FALSE()
        
        with Solver(name="z3") as s_uniq_cls: 
            for a_assertion in assertions_acn_cls: s_uniq_cls.add_assertion(a_assertion)
            s_uniq_cls.add_assertion(assertion_differs_acn_cls)
            result_acn_cls_uniq = s_uniq_cls.solve()
            print_model_table_if_sat(result_acn_cls_uniq, s_uniq_cls.get_model() if result_acn_cls_uniq else None, R_acn_cls, local_s_omega_py_keys,
                                     "N-Cls.lit (Query Uniqueness)", "SAT (Differing table - EXPECTED)",
                                     "Proof: Omitting CCA3 literal '1+1=2' allows alternative (commutative) tables.",
                                     "UNSAT (Still unique - UNEXPECTED)")
            
            if result_acn_cls_uniq: 
                print("--- Query N-Cls.lit: Commutativity of Alternative Table (Check if still comm despite weakened Cls) ---")
                non_comm_clauses_ncls_alt = []
                if len(local_s_omega_py_keys) > 1:
                    for i in range(len(local_s_omega_py_keys)):
                        for j in range(i + 1, len(local_s_omega_py_keys)):
                            k1,k2 = local_s_omega_py_keys[i], local_s_omega_py_keys[j]
                            non_comm_clauses_ncls_alt.append(NotEquals(R_acn_cls[(k1,k2)], R_acn_cls[(k2,k1)]))
                assert_non_comm_ncls_alt = Or(non_comm_clauses_ncls_alt) if non_comm_clauses_ncls_alt else FALSE()
                
                with Solver(name="z3") as s_comm_cls: # New solver instance for this specific sub-query
                    # We need to re-assert the conditions that LED to an alternative table
                    # These are CCA1_Range, CCA2_TwoSided, CCA3_Classical_minus_11, CCA4_Full, AND explicit_commutativity
                    # The `assertions_acn_cls` already contains these.
                    for a_assertion in assertions_acn_cls: s_comm_cls.add_assertion(a_assertion)
                    # Now, additionally assert that THIS table (which satisfies weakened Cls + explicit Comm) is NON-COMMUTATIVE
                    # This is a contradiction if explicit commutativity was effectively asserted.
                    # Let's remove explicit_commutativity from assertions_acn_cls for this particular check.
                    # No, the auditor's point was "alt but STILL commutative table".
                    # So we assert the weakened set (that produced SAT for diff) and then ask if non-comm is possible.
                    # The previous script section for this test *did* assert explicit commutativity.
                    # So we expect non_comm to be UNSAT.
                    s_comm_cls.add_assertion(assert_non_comm_ncls_alt) 
                    result_ncls_comm_check = s_comm_cls.solve()
                    print_model_table_if_sat(result_ncls_comm_check, s_comm_cls.get_model() if result_ncls_comm_check else None, R_acn_cls, local_s_omega_py_keys,
                                             "N-Cls.lit (Query Commutativity of Alt Table)", 
                                             "SAT (Non-commutative alternative found after weakening Cls - UNEXPECTED, explicit comm was asserted!)",
                                             "Error: A non-commutative model was found despite explicit commutativity assertion in the base set for Query 1.",
                                             "UNSAT (All alternatives under weakened Cls + explicit Comm are Commutative - EXPECTED)")


    # --- Test N-Ovfl.lit.comm (P-SYM: Necessity of specific Ovfl literal for Commutativity) ---
    if current_omega_val == 3:
        print(f"\n--- Test N-Ovfl.lit.comm (Omega={current_omega_val}): Weakening Ovfl for (1,2)/(2,1) vs Commutativity ---")
        R_acn_ovfl_comm = create_symbolic_table("nOvflComm", current_omega_val, local_s_omega_py_keys)
        assertions_acn_ovfl_comm = []
        assert_cca1_range(assertions_acn_ovfl_comm, R_acn_ovfl_comm, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_acn_ovfl_comm, R_acn_ovfl_comm, local_s_omega_py_keys, local_U_SMT.constant_value())
        assert_cca3_classical_dfi(assertions_acn_ovfl_comm, R_acn_ovfl_comm, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
        # Partial CCA4: Omit for (1,2) and (2,1). Assert for (2,2)=U if it's an overflow.
        omit_these_ovfl_cells = []
        if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
            omit_these_ovfl_cells.extend([(1,2), (2,1)])
        assert_cca4_dfi_overflow(assertions_acn_ovfl_comm, R_acn_ovfl_comm, local_py_dfi_elements, current_omega_val, local_U_SMT, omit_cells=omit_these_ovfl_cells)
        
        non_comm_12_21_clauses = []
        if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
            # Assert that THIS specific pair is non-commutative
            non_comm_12_21_clauses.append(NotEquals(R_acn_ovfl_comm[(1,2)], R_acn_ovfl_comm[(2,1)]))
        assert_non_comm_12_21 = Or(non_comm_12_21_clauses) if non_comm_12_21_clauses else FALSE()
        
        assertions_acn_ovfl_comm.append(assert_non_comm_12_21) # Search for a model where this specific non-commutativity holds

        with Solver(name="z3") as s:
            for an_assertion in assertions_acn_ovfl_comm: s.add_assertion(an_assertion)
            result_acn_ovfl_comm = s.solve()
            print_model_table_if_sat(result_acn_ovfl_comm, s.get_model() if result_acn_ovfl_comm else None, R_acn_ovfl_comm, local_s_omega_py_keys,
                                     "N-Ovfl.lit.comm (Query Non-Comm for 1,2 pair)", 
                                     "SAT (Non-commutative model for (1,2) found - EXPECTED)",
                                     "Proof: Weakening symmetric CCA4_Ovfl for (1,2)/(2,1) allows non-commutative tables for this pair.",
                                     "UNSAT (Still commutative for (1,2) - UNEXPECTED)")

# --- Main Execution Block ---
if __name__ == "__main__":
    run_axiom_component_necessity_tests(2)
    run_axiom_component_necessity_tests(3)
    run_axiom_component_necessity_tests(4)