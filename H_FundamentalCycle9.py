from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Exists, ForAll,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, LE, NotEquals,
                             get_model)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Global Symbolic Constants ---
U_S = Int(0) # Canonical SMT representation for Unio

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

# --- Helper functions to build assertion lists for A_Min ---
def create_alt_add_table(prefix: str, current_omega_val: int, s_omega_py_keys: List[int]) -> Dict[Tuple[int, int], FNode]:
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

def assert_cls_classical_dfi(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode], 
                              py_dfi_elements: List[int], current_omega_val: int, 
                              dfi_smt_elements: List[FNode]):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                py_sum = dfi_a_py + dfi_b_py
                if py_sum < current_omega_val:
                    sum_smt_val = Int(py_sum)
                    if any(sum_smt_val.constant_value() == d.constant_value() for d in dfi_smt_elements):
                        assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], sum_smt_val))

def assert_ovfl_dfi_overflow(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode], 
                               py_dfi_elements: List[int], current_omega_val: int, local_U_SMT: FNode):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                py_sum = dfi_a_py + dfi_b_py
                if py_sum >= current_omega_val:
                    assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], local_U_SMT))

# Main test function
def run_auditor_suggested_axiom_tests(current_omega_val: int):
    print(f"\n--- Auditor-Suggested Axiom Tests for Omega={current_omega_val} ---")
    print("    Testing consequences of A_Min = {CCA1_Range, IdR, Cls, Ovfl}")

    if current_omega_val < 1:
        print("OMEGA_VAL must be >= 1. Test skipped.")
        return
        
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

    alt_add_results = create_alt_add_table("raud", current_omega_val, local_s_omega_py_keys)

    A_Min_assertions = []
    assert_cca1_range(A_Min_assertions, alt_add_results, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_idr_right_identity(A_Min_assertions, alt_add_results, local_s_omega_py_keys, local_U_SMT.constant_value())
    assert_cls_classical_dfi(A_Min_assertions, alt_add_results, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    assert_ovfl_dfi_overflow(A_Min_assertions, alt_add_results, local_py_dfi_elements, current_omega_val, local_U_SMT)
    
    print(f"Applied {len(A_Min_assertions)} assertions for Auditor's Minimal Axiom Set A_Min.")

    # --- Test P-Uniq (Does A_Min uniquely define the AVCA table?) ---
    print(f"\n--- Test P-Uniq (Omega={current_omega_val}): Uniqueness under A_Min ---")
    differs_from_std_uniq = [NotEquals(alt_add_results[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in alt_add_results]
    assertion_differs_uniq = Or(differs_from_std_uniq) if differs_from_std_uniq else FALSE()

    with Solver(name="z3") as s:
        for an_assertion in A_Min_assertions: s.add_assertion(an_assertion)
        s.add_assertion(assertion_differs_uniq)
        result_P_Uniq = s.solve()
        
        uniq_msg_key = "SAT (Differing table - A_Min not unique for std table)" if result_P_Uniq else "UNSAT (Unique AVCA table from A_Min - EXPECTED)"
        print(f"  Test P-Uniq SMT Result: {uniq_msg_key}")
        if not result_P_Uniq: print("    Proof: A_Min (+ CCA1_Range implicitly via table structure) uniquely forces the standard AVCA ⊕-table.")
        else: 
            model = s.get_model()
            if model:
                print("    Alternative Model Found with A_Min (Problem for P-Uniq):")
                for x_k in local_s_omega_py_keys:
                    row = f"      {x_k} |"
                    for y_k in local_s_omega_py_keys:
                        val_node = alt_add_results.get((x_k,y_k))
                        val = model.get_value(val_node) if val_node else None
                        row += f" {val.constant_value() if val else '?'}"
                    print(row)

    # --- Test P-CMT (Emergent Commutativity from A_Min) ---
    print(f"\n--- Test P-CMT (Omega={current_omega_val}): Emergent Commutativity from A_Min ---")
    non_comm_clauses_pcmt = []
    if len(local_s_omega_py_keys) > 1:
        for i in range(len(local_s_omega_py_keys)):
            for j in range(i + 1, len(local_s_omega_py_keys)):
                k1,k2 = local_s_omega_py_keys[i], local_s_omega_py_keys[j]
                non_comm_clauses_pcmt.append(NotEquals(alt_add_results[(k1,k2)], alt_add_results[(k2,k1)]))
    assert_non_comm_pcmt = Or(non_comm_clauses_pcmt) if non_comm_clauses_pcmt else FALSE()

    with Solver(name="z3") as s:
        for an_assertion in A_Min_assertions: s.add_assertion(an_assertion)
        s.add_assertion(assert_non_comm_pcmt)
        result_P_CMT = s.solve()
        cmt_msg_key = "SAT (Non-commutative table found - Auditor's P-CMT fails)" if result_P_CMT else "UNSAT (Must be commutative - EXPECTED by Auditor)"
        print(f"  Test P-CMT SMT Result: {cmt_msg_key}")
        if not result_P_CMT: print("    Proof: A_Min forces emergent commutativity.")
        else:
            model = s.get_model()
            if model:
                print("    Non-Commutative Model Found with A_Min:")
                for x_k in local_s_omega_py_keys:
                    row = f"      {x_k} |"
                    for y_k in local_s_omega_py_keys:
                        val_node = alt_add_results.get((x_k,y_k))
                        val = model.get_value(val_node) if val_node else None
                        row += f" {val.constant_value() if val else '?'}"
                    print(row)

    # --- Test P-ID (Emergent Left-Identity from A_Min) ---
    print(f"\n--- Test P-ID (Omega={current_omega_val}): Emergent Left-Identity from A_Min ---")
    fails_left_id_clauses = []
    u_k = local_U_SMT.constant_value()
    for x_k in local_s_omega_py_keys: 
        fails_left_id_clauses.append(NotEquals(alt_add_results[(u_k, x_k)], Int(x_k)))
    assert_fails_left_id = Or(fails_left_id_clauses) if fails_left_id_clauses else FALSE()
    
    with Solver(name="z3") as s:
        for an_assertion in A_Min_assertions: s.add_assertion(an_assertion)
        s.add_assertion(assert_fails_left_id) 
        result_P_ID = s.solve()
        id_msg_key = "SAT (Left-Identity fails - Auditor's P-ID fails)" if result_P_ID else "UNSAT (Left-Identity must hold - EXPECTED by Auditor)"
        print(f"  Test P-ID SMT Result: {id_msg_key}")
        if not result_P_ID: print("    Proof: A_Min forces emergent Left-Identity (U@x = x).")

    # --- Test P-ASSOC (Associativity Phase from A_Min) ---
    print(f"\n--- Test P-ASSOC (Omega={current_omega_val}): Associativity Phase from A_Min ---")
    
    sa = Symbol(f"sa_passoc_w{current_omega_val}", SMT_INT_TYPE)
    sb = Symbol(f"sb_passoc_w{current_omega_val}", SMT_INT_TYPE)
    sc = Symbol(f"sc_passoc_w{current_omega_val}", SMT_INT_TYPE)

    assoc_assertions = list(A_Min_assertions) 
    
    assoc_assertions.extend([Or([Equals(sa, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
    assoc_assertions.extend([Or([Equals(sb, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
    assoc_assertions.extend([Or([Equals(sc, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
    
    op_ab_passoc = smt_op_from_symbolic_table(sa, sb, local_s_omega_py_keys, alt_add_results)
    lhs_passoc = smt_op_from_symbolic_table(op_ab_passoc, sc, local_s_omega_py_keys, alt_add_results)
    op_bc_passoc = smt_op_from_symbolic_table(sb, sc, local_s_omega_py_keys, alt_add_results)
    rhs_passoc = smt_op_from_symbolic_table(sa, op_bc_passoc, local_s_omega_py_keys, alt_add_results)
    
    property_is_associative_for_triplet = Equals(lhs_passoc, rhs_passoc)

    with Solver(name="z3") as s:
        for an_assertion in assoc_assertions: s.add_assertion(an_assertion)

        if current_omega_val <= 2:
            s.add_assertion(Not(property_is_associative_for_triplet)) 
            result_P_ASSOC = s.solve()
            assoc_msg_key = "SAT (Non-Associative found - UNEXPECTED for Ω≤2)" if result_P_ASSOC else "UNSAT (Must be Associative - EXPECTED for Ω≤2)"
            print(f"  Test P-ASSOC (Ω≤2) SMT Result (Asserting Triplet is Non-Associative): {assoc_msg_key}")
            if not result_P_ASSOC: print("    Proof: A_Min forces associativity for Ω≤2.")
            else: 
                model=s.get_model()
                if model: print(f"      Counterexample to Ω≤2 associativity: a={model.get_value(sa)}, b={model.get_value(sb)}, c={model.get_value(sc)}")
        else: # current_omega_val >= 3
            # We expect non-associativity, so there EXISTS a triplet where LHS != RHS.
            # So, assert LHS != RHS and expect SAT.
            s.add_assertion(NotEquals(lhs_passoc, rhs_passoc))
            result_P_ASSOC = s.solve()
            assoc_msg_key = "SAT (Non-Associative Triplet found - EXPECTED for Ω≥3)" if result_P_ASSOC else "UNSAT (All Triplets Associative - UNEXPECTED for Ω≥3)"
            print(f"  Test P-ASSOC (Ω≥3) SMT Result (Asserting Triplet is Non-Associative): {assoc_msg_key}")
            if result_P_ASSOC: 
                print("    Proof: A_Min allows/forces non-associativity for Ω≥3.")
                model=s.get_model()
                if model: print(f"      Counterexample: a={model.get_value(sa)}, b={model.get_value(sb)}, c={model.get_value(sc)}")

if __name__ == "__main__":
    run_auditor_suggested_axiom_tests(2)
    run_auditor_suggested_axiom_tests(3) 
    run_auditor_suggested_axiom_tests(4)