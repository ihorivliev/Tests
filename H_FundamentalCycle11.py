from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Exists, ForAll,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, LE, NotEquals,
                             get_model)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Global Symbolic Constants ---
U_S = Int(0) # Canonical SMT representation for Unio
UNDEFINED_VAL_S = Int(-1) # A value outside S_Omega for testing Totality

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
    for x_key in reversed(current_s_omega_py_keys): # Iterate consistently for ITE structure
        for y_key in reversed(current_s_omega_py_keys):
            condition = And(Equals(val_a_smt_op, Int(x_key)), Equals(val_b_smt_op, Int(y_key)))
            value_for_this_cell = symbolic_table[(x_key, y_key)]
            expr = Ite(condition, value_for_this_cell, expr)
    return expr

# --- Helper functions to build assertion lists for Core Axioms ---
def create_alt_add_table(prefix: str, current_omega_val: int, s_omega_py_keys: List[int]) -> Dict[Tuple[int, int], FNode]:
    table = {}
    for x_k in s_omega_py_keys:
        for y_k in s_omega_py_keys:
            table[(x_k, y_k)] = Symbol(f"{prefix}_{x_k}_{y_k}_w{current_omega_val}", SMT_INT_TYPE)
    return table

# CCA1_Range: Output is in S_Omega
def assert_cca1_range(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                      s_omega_py_keys: List[int], s_omega_smt_elements: List[FNode]):
    for x_k in s_omega_py_keys:
        for y_k in s_omega_py_keys:
            res_var = table[(x_k, y_k)]
            assertions_list.append(Or([Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]))

# Auditor's "IdR" (Right Identity only): x⊕U = x
def assert_idr_right_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys:
        assertions_list.append(Equals(table[(x_k, u_py_key)], Int(x_k)))

# Auditor's "IdL" (Left Identity only): U⊕x = x
def assert_idl_left_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys:
        assertions_list.append(Equals(table[(u_py_key, x_k)], Int(x_k)))

# CCA2_TwoSided (Auditor's "Id"): U⊕x = x AND x⊕U = x
def assert_cca2_two_sided_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                                   s_omega_py_keys: List[int], u_py_key: int):
    assert_idr_right_identity(assertions_list, table, s_omega_py_keys, u_py_key)
    assert_idl_left_identity(assertions_list, table, s_omega_py_keys, u_py_key)

# CCA3_Cls (Auditor's "Cls"): x,y∈DFI ∧ x+y<Ω → x⊕y = x+y
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
                    if any(sum_smt_val.constant_value() == d.constant_value() for d in dfi_smt_elements):
                        assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], sum_smt_val))

# CCA4_Ovfl (Auditor's "Ovfl"): x,y∈DFI ∧ x+y≥Ω → x⊕y = U
def assert_cca4_dfi_overflow(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               py_dfi_elements: List[int], current_omega_val: int, local_U_SMT: FNode,
                               omit_cell: Tuple[int,int] = None, only_cell: Tuple[int,int] = None):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                if omit_cell and (dfi_a_py, dfi_b_py) == omit_cell:
                    continue
                if only_cell and (dfi_a_py, dfi_b_py) != only_cell:
                    continue
                py_sum = dfi_a_py + dfi_b_py
                if py_sum >= current_omega_val:
                    assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], local_U_SMT))

def assert_explicit_commutativity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode], 
                                  s_omega_py_keys: List[int]):
    if len(s_omega_py_keys) > 1:
        for i in range(len(s_omega_py_keys)):
            for j in range(i + 1, len(s_omega_py_keys)):
                k1,k2 = s_omega_py_keys[i], s_omega_py_keys[j]
                assertions_list.append(Equals(table[(k1,k2)], table[(k2,k1)]))

def print_model_table(model: Union[Dict,None], table: Dict[Tuple[int,int],FNode], s_omega_py_keys: List[int]):
    if model:
        print("    Model Table Found:")
        header = "⊕ |" + "".join([f" {str(k):<2}" for k in s_omega_py_keys])
        print(f"    {header}")
        print(f"    ---" + "".join(["----" for _ in s_omega_py_keys]))
        for x_k in s_omega_py_keys:
            row_str = f"    {str(x_k):<2}|"
            for y_k in s_omega_py_keys:
                val_node = table.get((x_k,y_k))
                # Check if val_node is None, which it shouldn't be if table is complete
                val = model.get_value(val_node) if val_node is not None else None
                row_str += f" {str(val.constant_value() if val else '?'):<2}"
            print(row_str)
    else:
        print("    Solver returned SAT but no model was available to print (or model printing skipped).")

# --- Main test function (Auditor's "P-Tests" on their refined "irreducible" set) ---
def run_auditor_refined_axiom_tests(current_omega_val: int):
    print(f"\n--- Auditor's Refined Axiom Tests for Omega={current_omega_val} ---")
    print("    Using Auditor's Minimal Set A_Min = {CCA1_Range, IdR_RightIdentity, Cls, Ovfl}")

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

    R_results_auditor = create_alt_add_table("audR", current_omega_val, local_s_omega_py_keys)
    
    A_Min_auditor_assertions = []
    assert_cca1_range(A_Min_auditor_assertions, R_results_auditor, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_idr_right_identity(A_Min_auditor_assertions, R_results_auditor, local_s_omega_py_keys, local_U_SMT.constant_value()) # IdR only
    assert_cca3_classical_dfi(A_Min_auditor_assertions, R_results_auditor, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    assert_cca4_dfi_overflow(A_Min_auditor_assertions, R_results_auditor, local_py_dfi_elements, current_omega_val, local_U_SMT)
    print(f"Applied {len(A_Min_auditor_assertions)} assertions for Auditor's Minimal Axiom Set A_Min.")

    # Test P-Uniq (from Auditor's A_Min)
    print(f"\n--- Test P-Uniq (Auditor A_Min) (Omega={current_omega_val}): Uniqueness ---")
    differs_uniq_aud = [NotEquals(R_results_auditor[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in R_results_auditor]
    assert_differs_uniq_aud = Or(differs_uniq_aud) if differs_uniq_aud else FALSE()
    with Solver(name="z3") as s:
        for a in A_Min_auditor_assertions: s.add_assertion(a)
        s.add_assertion(assert_differs_uniq_aud)
        res_uniq = s.solve()
        msg = "SAT (Differing table found - A_Min IS NOT SUFFICIENT for uniqueness - As per prior SMT run)" if res_uniq else "UNSAT (Unique AVCA table from A_Min - CONTRADICTS prior SMT run)"
        print(f"  Test P-Uniq (Auditor A_Min) SMT Result: {msg}")
        if res_uniq: print_model_table(s.get_model(), R_results_auditor, local_s_omega_py_keys)

    # Test P-CMT (Emergent Commutativity from Auditor's A_Min)
    print(f"\n--- Test P-CMT (Auditor A_Min) (Omega={current_omega_val}): Emergent Commutativity ---")
    non_comm_pcmt_aud = []
    if len(local_s_omega_py_keys) > 1:
        for i in range(len(local_s_omega_py_keys)):
            for j in range(i + 1, len(local_s_omega_py_keys)):
                k1,k2 = local_s_omega_py_keys[i], local_s_omega_py_keys[j]
                non_comm_pcmt_aud.append(NotEquals(R_results_auditor[(k1,k2)], R_results_auditor[(k2,k1)]))
    assert_non_comm_pcmt_aud = Or(non_comm_pcmt_aud) if non_comm_pcmt_aud else FALSE()
    with Solver(name="z3") as s:
        for a in A_Min_auditor_assertions: s.add_assertion(a)
        s.add_assertion(assert_non_comm_pcmt_aud)
        res_pcmt = s.solve()
        msg = "SAT (Non-commutative table found - Commutativity DOES NOT EMERGE from A_Min - As per prior SMT run)" if res_pcmt else "UNSAT (Must be commutative - CONTRADICTS prior SMT run for A_Min)"
        print(f"  Test P-CMT (Auditor A_Min) SMT Result: {msg}")
        if res_pcmt: print_model_table(s.get_model(), R_results_auditor, local_s_omega_py_keys)

    # Test P-ID (Emergent Left-Identity from Auditor's A_Min)
    print(f"\n--- Test P-ID (Auditor A_Min) (Omega={current_omega_val}): Emergent Left-Identity ---")
    fails_left_id_pid_aud = []
    u_k_pid = local_U_SMT.constant_value()
    for x_k_pid in local_s_omega_py_keys:
        fails_left_id_pid_aud.append(NotEquals(R_results_auditor[(u_k_pid, x_k_pid)], Int(x_k_pid)))
    assert_fails_left_id_pid_aud = Or(fails_left_id_pid_aud) if fails_left_id_pid_aud else FALSE()
    with Solver(name="z3") as s:
        for a in A_Min_auditor_assertions: s.add_assertion(a)
        s.add_assertion(assert_fails_left_id_pid_aud)
        res_pid = s.solve()
        msg = "SAT (Left-Identity fails - Left-ID DOES NOT EMERGE from A_Min - As per prior SMT run)" if res_pid else "UNSAT (Left-Identity must hold - CONTRADICTS prior SMT run for A_Min)"
        print(f"  Test P-ID (Auditor A_Min) SMT Result: {msg}")
        if res_pid: print_model_table(s.get_model(), R_results_auditor, local_s_omega_py_keys)

    # Test P-ASSOC (Associativity Phase using table from Auditor's A_Min)
    print(f"\n--- Test P-ASSOC (Auditor A_Min) (Omega={current_omega_val}): Associativity Phase ---")
    sa, sb, sc = Symbol(f"sa_pa_aud_w{current_omega_val}", SMT_INT_TYPE), Symbol(f"sb_pa_aud_w{current_omega_val}", SMT_INT_TYPE), Symbol(f"sc_pa_aud_w{current_omega_val}", SMT_INT_TYPE)
    assoc_test_base_aud = list(A_Min_auditor_assertions)
    assoc_test_base_aud.extend([Or([Equals(sa, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
    assoc_test_base_aud.extend([Or([Equals(sb, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
    assoc_test_base_aud.extend([Or([Equals(sc, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
    
    op_ab_paud = smt_op_from_symbolic_table(sa, sb, local_s_omega_py_keys, R_results_auditor)
    lhs_paud = smt_op_from_symbolic_table(op_ab_paud, sc, local_s_omega_py_keys, R_results_auditor)
    op_bc_paud = smt_op_from_symbolic_table(sb, sc, local_s_omega_py_keys, R_results_auditor)
    rhs_paud = smt_op_from_symbolic_table(sa, op_bc_paud, local_s_omega_py_keys, R_results_auditor)
    prop_assoc_holds_triplet_aud = Equals(lhs_paud, rhs_paud)

    with Solver(name="z3") as s:
        for an_assertion in assoc_test_base_aud: s.add_assertion(an_assertion)
        if current_omega_val <= 2:
            s.add_assertion(Not(prop_assoc_holds_triplet_aud)) # Assert non-associativity
            res_passoc = s.solve()
            msg = "SAT (Non-Associative found - UNEXPECTED for Ω≤2 with A_Min)" if res_passoc else "UNSAT (Must be Associative - A_Min implies assoc for Ω≤2)"
            print(f"  Test P-ASSOC (Ω≤2 with A_Min) SMT Result (Asserting Triplet Non-Assoc): {msg}")
            if res_passoc: print_model_table(s.get_model(), R_results_auditor, local_s_omega_py_keys) # Model of table and a,b,c
        else: # current_omega_val >= 3
            s.add_assertion(NotEquals(lhs_paud, rhs_paud)) # Assert a non-associative triplet exists
            res_passoc = s.solve()
            msg = "SAT (Non-Associative Triplet found - EXPECTED for Ω≥3 with A_Min)" if res_passoc else "UNSAT (All Triplets Associative - UNEXPECTED for Ω≥3 with A_Min)"
            print(f"  Test P-ASSOC (Ω≥3 with A_Min) SMT Result (Asserting Triplet Non-Assoc): {msg}")
            if res_passoc: print_model_table(s.get_model(), R_results_auditor, local_s_omega_py_keys)

    # Test P-SYM (Auditor's "half-Ovfl" breaks commutativity for Ω=3)
    if current_omega_val == 3:
        print(f"\n--- Test P-SYM (Omega={current_omega_val}): 'half-Ovfl' breaks Commutativity ---")
        # Axioms: CCA1_Range, CCA2_TwoSided, CCA3_Cls_Full
        # CCA4_Partial: Only res_22 = U for Omega=3. res_12, res_21 are "free".
        alt_add_psym = create_alt_add_table("psym", current_omega_val, local_s_omega_py_keys)
        assertions_psym = []
        assert_cca1_range(assertions_psym, alt_add_psym, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_psym, alt_add_psym, local_s_omega_py_keys, local_U_SMT.constant_value())
        assert_cca3_classical_dfi(assertions_psym, alt_add_psym, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)

        if 2 in local_py_dfi_elements: # DFI2 for Omega=3
            assert_cca4_dfi_overflow(assertions_psym, alt_add_psym, [2], current_omega_val, local_U_SMT, only_cell=(2,2))
        
        if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
            assertions_psym.append(NotEquals(alt_add_psym[(1,2)], alt_add_psym[(2,1)]))
        else: assertions_psym.append(FALSE()) 

        with Solver(name="z3") as s:
            for an_assertion in assertions_psym: s.add_assertion(an_assertion)
            result_P_SYM = s.solve()
            psym_msg = "SAT (Non-commutative model found with half-Ovfl - EXPECTED)" if result_P_SYM else "UNSAT (Still commutative - Problem in P-SYM logic or expectation)"
            print(f"  Test P-SYM SMT Result: {psym_msg}")
            if result_P_SYM:
                print("    Proof: Weakening symmetric CCA4_Ovfl (keeping only 2+2=U) allows non-commutative tables for Ω=3.")
                print_model_table(s.get_model(), alt_add_psym, local_s_omega_py_keys)

if __name__ == "__main__":
    run_auditor_refined_axiom_tests(2)
    run_auditor_refined_axiom_tests(3)
    run_auditor_refined_axiom_tests(4)