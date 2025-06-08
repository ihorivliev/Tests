from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Exists, ForAll,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, LE, NotEquals,
                             get_model)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Global Symbolic Constants ---
U_S = Int(0) 
UNDEFINED_VAL_S = Int(-1) 

# --- Helper to get standard AVCA add_v1.1 result ---
def get_std_avca_add_v11_result(val_a_int: int, val_b_int: int, current_omega_val: int, u_val_int: int) -> int:
    # ... (implementation as before)
    if val_a_int == u_val_int: return val_b_int
    if val_b_int == u_val_int: return val_a_int
    int_sum = val_a_int + val_b_int
    return int_sum if int_sum < current_omega_val else u_val_int

# --- SMT Helper: Construct ITE cascade ---
def smt_op_from_symbolic_table(val_a_smt_op: FNode, val_b_smt_op: FNode,
                               current_s_omega_py_keys: List[int],
                               symbolic_table: Dict[Tuple[int,int],FNode]) -> FNode:
    # ... (implementation as before)
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
    # ... (implementation as before)
    table = {}
    for x_k in s_omega_py_keys:
        for y_k in s_omega_py_keys:
            table[(x_k, y_k)] = Symbol(f"{prefix}_{x_k}_{y_k}_w{current_omega_val}", SMT_INT_TYPE)
    return table

def assert_cca1_range(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                      s_omega_py_keys: List[int], s_omega_smt_elements: List[FNode]):
    # ... (implementation as before)
    for x_k in s_omega_py_keys:
        for y_k in s_omega_py_keys:
            res_var = table[(x_k, y_k)]
            assertions_list.append(Or([Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]))

def assert_cca2_right_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               s_omega_py_keys: List[int], u_py_key: int):
    # ... (implementation as before)
    for x_k in s_omega_py_keys:
        assertions_list.append(Equals(table[(x_k, u_py_key)], Int(x_k)))

def assert_cca2_left_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              s_omega_py_keys: List[int], u_py_key: int):
    # ... (implementation as before)
    for x_k in s_omega_py_keys:
        assertions_list.append(Equals(table[(u_py_key, x_k)], Int(x_k)))
        
def assert_cca2_two_sided_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                                   s_omega_py_keys: List[int], u_py_key: int):
    # ... (implementation as before)
    assert_cca2_right_identity(assertions_list, table, s_omega_py_keys, u_py_key)
    assert_cca2_left_identity(assertions_list, table, s_omega_py_keys, u_py_key)

def assert_cca3_classical_dfi(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              py_dfi_elements: List[int], current_omega_val: int,
                              dfi_smt_elements: List[FNode], omit_cell: Tuple[int,int] = None):
    # ... (implementation as before)
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                if omit_cell and (dfi_a_py, dfi_b_py) == omit_cell:
                    continue
                py_sum = dfi_a_py + dfi_b_py
                if py_sum < current_omega_val:
                    sum_smt_val = Int(py_sum)
                    if any(sum_smt_val.constant_value() == d.constant_value() for d in dfi_smt_elements):
                        assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], sum_smt_val))

def assert_cca4_dfi_overflow(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               py_dfi_elements: List[int], current_omega_val: int, local_U_SMT: FNode,
                               omit_cell: Tuple[int,int] = None, only_cells: List[Tuple[int,int]] = None):
    # ... (implementation as before)
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                current_cell = (dfi_a_py, dfi_b_py)
                if omit_cell and current_cell == omit_cell:
                    continue
                if only_cells and current_cell not in only_cells:
                    continue
                
                py_sum = dfi_a_py + dfi_b_py
                if py_sum >= current_omega_val:
                    assertions_list.append(Equals(table[current_cell], local_U_SMT))

def assert_explicit_commutativity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode], 
                                  s_omega_py_keys: List[int]):
    # ... (implementation as before)
    if len(s_omega_py_keys) > 1:
        for i in range(len(s_omega_py_keys)):
            for j in range(i + 1, len(s_omega_py_keys)):
                k1,k2 = s_omega_py_keys[i], s_omega_py_keys[j]
                assertions_list.append(Equals(table[(k1,k2)], table[(k2,k1)]))

def print_model_table_if_sat(result: bool, solver_model: Union[Dict,None], 
                             table: Dict[Tuple[int,int],FNode], s_omega_py_keys: List[int], 
                             message_if_sat: str, message_if_unsat: str):
    # ... (implementation as before)
    print(f"  SMT Result: {message_if_sat if result else message_if_unsat}")
    if result:
        if solver_model:
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
        else:
            print("    Solver returned SAT but no model was available.")

# --- Main test function for "Independence Grid" style tests ---
# THIS FUNCTION DEFINITION MUST COME BEFORE THE if __name__ == "__main__": BLOCK
def run_axiom_independence_grid_tests(current_omega_val: int):
    print(f"\n--- Axiom Independence Grid Tests for Omega={current_omega_val} ---")
    # ... (all the test logic as in the previous script version) ...
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

    # --- Test ACN-IdL (Necessity of Left-Identity U⊕x = x from CCA2_TwoSided) ---
    print(f"\n--- Test ACN-IdL (Omega={current_omega_val}): Necessity of U@x=x ---")
    R_acn_idl = create_symbolic_table("acnIdL", current_omega_val, local_s_omega_py_keys)
    assertions_acn_idl = []
    assert_cca1_range(assertions_acn_idl, R_acn_idl, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_cca2_right_identity(assertions_acn_idl, R_acn_idl, local_s_omega_py_keys, local_U_SMT.constant_value()) # ONLY Right ID
    assert_cca3_classical_dfi(assertions_acn_idl, R_acn_idl, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    assert_cca4_dfi_overflow(assertions_acn_idl, R_acn_idl, local_py_dfi_elements, current_omega_val, local_U_SMT)

    # Query if Left Identity Fails OR Commutativity Fails OR Differs from Standard
    # Build list of clauses for Or - ensures Or is not empty if one part is empty
    bad_model_clauses_ind1 = []
    list_for_fails_left_id = [NotEquals(R_acn_idl[(local_U_SMT.constant_value(), x_k)], Int(x_k)) for x_k in local_s_omega_py_keys if (local_U_SMT.constant_value(),x_k) in R_acn_idl]
    if list_for_fails_left_id: bad_model_clauses_ind1.append(Or(list_for_fails_left_id))
    
    non_comm_clauses_ind1 = []
    if len(local_s_omega_py_keys) > 1:
        for i in range(len(local_s_omega_py_keys)):
            for j in range(i + 1, len(local_s_omega_py_keys)):
                k1,k2 = local_s_omega_py_keys[i], local_s_omega_py_keys[j]
                non_comm_clauses_ind1.append(NotEquals(R_acn_idl[(k1,k2)], R_acn_idl[(k2,k1)]))
    if non_comm_clauses_ind1: bad_model_clauses_ind1.append(Or(non_comm_clauses_ind1))
    
    list_for_differs_std = [NotEquals(R_acn_idl[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in R_acn_idl]
    if list_for_differs_std: bad_model_clauses_ind1.append(Or(list_for_differs_std))
    
    assertion_bad_model_ind1 = Or(bad_model_clauses_ind1) if bad_model_clauses_ind1 else FALSE() # If all are false, it means it IS std, comm, and left-ID

    with Solver(name="z3") as s:
        for a_assertion in assertions_acn_idl: s.add_assertion(a_assertion) # Renamed loop variable
        s.add_assertion(assertion_bad_model_ind1) 
        result_ind1 = s.solve()
        msg1 = "SAT (Alternative/Non-Std/Non-Comm/Non-LeftID table found - EXPECTED)" if result_ind1 else "UNSAT (Only standard table possible - UNEXPECTED for IdR only)"
        print_model_table_if_sat(result_ind1, s.get_model() if result_ind1 else None, R_acn_idl, local_s_omega_py_keys, msg1, msg1)
        if result_ind1: print("    Proof: Omitting Left-Identity from CCA2 (keeping Right-ID, Cls, Ovfl, Range) allows tables that may differ from standard AVCA, fail Left-ID, or fail commutativity.")

    # --- Test ACN-Cls.lit (Necessity of a specific Cls literal, e.g., 1⊕1=2 for Ω=3) ---
    if current_omega_val == 3 : 
        print(f"\n--- Test ACN-Cls.lit (Omega={current_omega_val}): Necessity of CCA3 literal (1+1=2) ---")
        R_acn_cls = create_symbolic_table("acnCls", current_omega_val, local_s_omega_py_keys)
        assertions_acn_cls = []
        assert_cca1_range(assertions_acn_cls, R_acn_cls, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_acn_cls, R_acn_cls, local_s_omega_py_keys, local_U_SMT.constant_value())
        assert_cca3_classical_dfi(assertions_acn_cls, R_acn_cls, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS, omit_cell=(1,1)) # Omit 1+1=2
        assert_cca4_dfi_overflow(assertions_acn_cls, R_acn_cls, local_py_dfi_elements, current_omega_val, local_U_SMT) 
        assert_explicit_commutativity(assertions_acn_cls, R_acn_cls, local_s_omega_py_keys)

        list_differs_cls = [NotEquals(R_acn_cls[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in R_acn_cls]
        assertion_differs_acn_cls = Or(list_differs_cls) if list_differs_cls else FALSE()
        
        with Solver(name="z3") as s:
            for a_assertion in assertions_acn_cls: s.add_assertion(a_assertion) # Renamed
            s.add_assertion(assertion_differs_acn_cls)
            result_acn_cls = s.solve()
            msg3 = "SAT (Differing commutative table found when 1+1=2 omitted - EXPECTED)" if result_acn_cls else "UNSAT (Still unique & standard - UNEXPECTED)"
            print_model_table_if_sat(result_acn_cls, s.get_model() if result_acn_cls else None, R_acn_cls, local_s_omega_py_keys, msg3, msg3)
            if result_acn_cls: print("    Proof: Omitting the CCA3 clause '1+1=2' (while keeping commutativity) allows alternative tables.")

    # --- Test ACN-Ovfl.lit.comm (Auditor's P-SYM: Necessity of specific Ovfl literal for Commutativity) ---
    if current_omega_val == 3:
        print(f"\n--- Test ACN-Ovfl.lit.comm (Omega={current_omega_val}): Necessity of Ovfl literal (1+2=U) for Commutativity ---")
        R_acn_ovfl_comm = create_symbolic_table("acnOvflComm", current_omega_val, local_s_omega_py_keys)
        assertions_acn_ovfl_comm = []
        assert_cca1_range(assertions_acn_ovfl_comm, R_acn_ovfl_comm, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_acn_ovfl_comm, R_acn_ovfl_comm, local_s_omega_py_keys, local_U_SMT.constant_value())
        assert_cca3_classical_dfi(assertions_acn_ovfl_comm, R_acn_ovfl_comm, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
        # Partial CCA4: only assert for (2,2)=U. Omit (1,2)=U and (2,1)=U.
        assert_cca4_dfi_overflow(assertions_acn_ovfl_comm, R_acn_ovfl_comm, [2], current_omega_val, local_U_SMT, only_cells=[(2,2)])
        
        non_comm_12_21_clauses = []
        if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
            non_comm_12_21_clauses.append(NotEquals(R_acn_ovfl_comm[(1,2)], R_acn_ovfl_comm[(2,1)]))
        assert_non_comm_12_21 = Or(non_comm_12_21_clauses) if non_comm_12_21_clauses else FALSE()
        
        assertions_acn_ovfl_comm.append(assert_non_comm_12_21)

        with Solver(name="z3") as s:
            for an_assertion in assertions_acn_ovfl_comm: s.add_assertion(an_assertion)
            result_acn_ovfl_comm = s.solve()
            msg4 = "SAT (Non-commutative model found when Ovfl for (1,2)/(2,1) omitted - EXPECTED)" if result_acn_ovfl_comm else "UNSAT (Still commutative - UNEXPECTED)"
            print_model_table_if_sat(result_acn_ovfl_comm, s.get_model() if result_acn_ovfl_comm else None, R_acn_ovfl_comm, local_s_omega_py_keys, msg4, msg4)
            if result_acn_ovfl_comm: print("    Proof: Weakening symmetric CCA4_Ovfl application allows non-commutative tables.")

# --- Main Execution Block ---
if __name__ == "__main__":
    # Test suite based on auditor's final recommendations for "irreducible core" and "independence grid"
    run_axiom_independence_grid_tests(2) 
    run_axiom_independence_grid_tests(3)
    # run_axiom_independence_grid_tests(4) # Can be added for more comprehensive testing