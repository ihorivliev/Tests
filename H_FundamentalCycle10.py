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

# CCA2_TwoSided (Auditor's "Id"): U⊕x = x AND x⊕U = x
def assert_cca2_two_sided_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                                   s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys:
        x_smt = Int(x_k)
        assertions_list.append(Equals(table[(u_py_key, x_k)], x_smt)) # U @ x = x
        assertions_list.append(Equals(table[(x_k, u_py_key)], x_smt)) # x @ U = x

# CCA3_Cls (Auditor's "Cls"): x,y∈DFI ∧ x+y<Ω → x⊕y = x+y
def assert_cca3_classical_dfi(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
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

# CCA4_Ovfl (Auditor's "Ovfl"): x,y∈DFI ∧ x+y≥Ω → x⊕y = U
def assert_cca4_dfi_overflow(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               py_dfi_elements: List[int], current_omega_val: int, local_U_SMT: FNode):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                py_sum = dfi_a_py + dfi_b_py
                if py_sum >= current_omega_val:
                    assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], local_U_SMT))

# --- Main test function ---
def run_final_core_axiom_tests(current_omega_val: int):
    print(f"\n--- Final Core Axiom Tests for Omega={current_omega_val} ---")
    print("    Using Core Axioms: {CCA1_Range, CCA2_TwoSided, CCA3_Cls, CCA4_Ovfl}")

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

    R_results = create_alt_add_table("R", current_omega_val, local_s_omega_py_keys)

    CoreAxioms_assertions = []
    assert_cca1_range(CoreAxioms_assertions, R_results, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_cca2_two_sided_identity(CoreAxioms_assertions, R_results, local_s_omega_py_keys, local_U_SMT.constant_value())
    assert_cca3_classical_dfi(CoreAxioms_assertions, R_results, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    assert_cca4_dfi_overflow(CoreAxioms_assertions, R_results, local_py_dfi_elements, current_omega_val, local_U_SMT)
    print(f"Applied {len(CoreAxioms_assertions)} assertions for Core Axiom Set.")

    # --- Test P-CORE-Uniq (Uniqueness from CoreAxioms) ---
    print(f"\n--- Test P-CORE-Uniq (Omega={current_omega_val}): Uniqueness under CoreAxioms ---")
    differs_from_std_core = [NotEquals(R_results[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in R_results]
    assertion_differs_core = Or(differs_from_std_core) if differs_from_std_core else FALSE()

    with Solver(name="z3") as s:
        for an_assertion in CoreAxioms_assertions: s.add_assertion(an_assertion)
        s.add_assertion(assertion_differs_core)
        result_P_CORE_Uniq = s.solve()
        uniq_msg = "SAT (Differing table - CoreAxioms not unique for std table - UNEXPECTED)" if result_P_CORE_Uniq else "UNSAT (Unique AVCA table from CoreAxioms - EXPECTED)"
        print(f"  Test P-CORE-Uniq SMT Result: {uniq_msg}")
        if not result_P_CORE_Uniq: print("    Proof: CoreAxioms uniquely force the standard AVCA ⊕-table.")
        else:
            model = s.get_model()
            if model:
                print("    Alternative Model Found (Problem for P-CORE-Uniq):")
                for x_k in local_s_omega_py_keys:
                    row = f"      {x_k} |"
                    for y_k in local_s_omega_py_keys:
                        val_node = R_results.get((x_k,y_k))
                        val = model.get_value(val_node) if val_node else None
                        row += f" {val.constant_value() if val else '?'}"
                    print(row)

    # --- Test P-CORE-CMT (Emergent Commutativity from CoreAxioms) ---
    print(f"\n--- Test P-CORE-CMT (Omega={current_omega_val}): Emergent Commutativity from CoreAxioms ---")
    non_comm_clauses_core_cmt = []
    if len(local_s_omega_py_keys) > 1:
        for i in range(len(local_s_omega_py_keys)):
            for j in range(i + 1, len(local_s_omega_py_keys)):
                k1,k2 = local_s_omega_py_keys[i], local_s_omega_py_keys[j]
                non_comm_clauses_core_cmt.append(NotEquals(R_results[(k1,k2)], R_results[(k2,k1)]))
    assert_non_comm_core_cmt = Or(non_comm_clauses_core_cmt) if non_comm_clauses_core_cmt else FALSE()

    with Solver(name="z3") as s:
        for an_assertion in CoreAxioms_assertions: s.add_assertion(an_assertion)
        s.add_assertion(assert_non_comm_core_cmt)
        result_P_CORE_CMT = s.solve()
        cmt_msg = "SAT (Non-commutative table found - UNEXPECTED with CoreAxioms)" if result_P_CORE_CMT else "UNSAT (Must be commutative - EXPECTED with CoreAxioms)"
        print(f"  Test P-CORE-CMT SMT Result: {cmt_msg}")
        if not result_P_CORE_CMT: print("    Proof: CoreAxioms force emergent commutativity.")
        else:
            model = s.get_model()
            if model:
                print("    Non-Commutative Model Found with CoreAxioms:")
                for x_k in local_s_omega_py_keys:
                    row = f"      {x_k} |"
                    for y_k in local_s_omega_py_keys:
                        val_node = R_results.get((x_k,y_k))
                        val = model.get_value(val_node) if val_node else None
                        row += f" {val.constant_value() if val else '?'}"
                    print(row)

    # --- Test P-CORE-ASSOC (Associativity Phase from CoreAxioms) ---
    print(f"\n--- Test P-CORE-ASSOC (Omega={current_omega_val}): Associativity Phase from CoreAxioms ---")

    sa = Symbol(f"sa_passoc_core_w{current_omega_val}", SMT_INT_TYPE)
    sb = Symbol(f"sb_passoc_core_w{current_omega_val}", SMT_INT_TYPE)
    sc = Symbol(f"sc_passoc_core_w{current_omega_val}", SMT_INT_TYPE)

    assoc_test_assertions = list(CoreAxioms_assertions)
    assoc_test_assertions.extend([Or([Equals(sa, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
    assoc_test_assertions.extend([Or([Equals(sb, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
    assoc_test_assertions.extend([Or([Equals(sc, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])

    op_ab_passoc = smt_op_from_symbolic_table(sa, sb, local_s_omega_py_keys, R_results)
    lhs_passoc = smt_op_from_symbolic_table(op_ab_passoc, sc, local_s_omega_py_keys, R_results)
    op_bc_passoc = smt_op_from_symbolic_table(sb, sc, local_s_omega_py_keys, R_results)
    rhs_passoc = smt_op_from_symbolic_table(sa, op_bc_passoc, local_s_omega_py_keys, R_results)

    property_is_associative_for_triplet = Equals(lhs_passoc, rhs_passoc)

    with Solver(name="z3") as s:
        for an_assertion in assoc_test_assertions: s.add_assertion(an_assertion)

        if current_omega_val <= 2:
            s.add_assertion(Not(property_is_associative_for_triplet))
            result_P_ASSOC = s.solve()
            assoc_msg = "SAT (Non-Associative found - UNEXPECTED for Ω≤2 with CoreAxioms)" if result_P_ASSOC else "UNSAT (Must be Associative - EXPECTED for Ω≤2 with CoreAxioms)"
            print(f"  Test P-CORE-ASSOC (Ω≤2) SMT Result (Asserting Triplet is Non-Associative): {assoc_msg}")
            if not result_P_ASSOC: print("    Proof: CoreAxioms force associativity for Ω≤2.")
            else:
                model=s.get_model()
                if model: print(f"      Counterexample to Ω≤2 associativity: a={model.get_value(sa)}, b={model.get_value(sb)}, c={model.get_value(sc)}")
        else: # current_omega_val >= 3
            s.add_assertion(NotEquals(lhs_passoc, rhs_passoc))
            result_P_ASSOC = s.solve()
            assoc_msg = "SAT (Non-Associative Triplet found - EXPECTED for Ω≥3 with CoreAxioms)" if result_P_ASSOC else "UNSAT (All Triplets Associative - UNEXPECTED for Ω≥3 with CoreAxioms)"
            print(f"  Test P-CORE-ASSOC (Ω≥3) SMT Result (Asserting Triplet is Non-Associative): {assoc_msg}")
            if result_P_ASSOC:
                print("    Proof: CoreAxioms force/allow non-associativity for Ω≥3.")
                model=s.get_model()
                if model: print(f"      Counterexample: a={model.get_value(sa)}, b={model.get_value(sb)}, c={model.get_value(sc)}")

    # --- Test P-SYM (Auditor's "half-Ovfl" breaks commutativity for Ω=3) ---
    if current_omega_val == 3:
        print(f"\n--- Test P-SYM (Omega={current_omega_val}): 'half-Ovfl' breaks Commutativity ---")
        alt_add_psym = create_alt_add_table("psym", current_omega_val, local_s_omega_py_keys) # CORRECTED
        assertions_psym = []
        assert_cca1_range(assertions_psym, alt_add_psym, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_psym, alt_add_psym, local_s_omega_py_keys, local_U_SMT.constant_value())
        assert_cca3_classical_dfi(assertions_psym, alt_add_psym, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)

        # Partial CCA4 for Ω=3: only assert res_22 = U. Leave res_12 and res_21 free.
        if 2 in local_py_dfi_elements: # DFI2 for Omega=3
            assertions_psym.append(Equals(alt_add_psym[(2,2)], local_U_SMT))
        # Cells (1,2) and (2,1) are only constrained by CCA1_Range (to be 0,1, or 2)

        # Assert Non-Commutativity for the (1,2) pair
        if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
            assertions_psym.append(NotEquals(alt_add_psym[(1,2)], alt_add_psym[(2,1)]))
        else: # Should not happen for Omega=3
            assertions_psym.append(FALSE()) # Force fail if DFI elements not as expected

        with Solver(name="z3") as s:
            for an_assertion in assertions_psym: s.add_assertion(an_assertion)
            result_P_SYM = s.solve()
            psym_msg = "SAT (Non-commutative model found with half-Ovfl - EXPECTED)" if result_P_SYM else "UNSAT (Still commutative - check logic/UNEXPECTED)"
            print(f"  Test P-SYM SMT Result: {psym_msg}")
            if result_P_SYM:
                print("    Proof: Weakening symmetric CCA4_Ovfl allows non-commutative tables.")
                model = s.get_model()
                if model:
                    print("    Non-Commutative Model Found (res_12 vs res_21):")
                    for x_k in local_s_omega_py_keys:
                        row = f"      {x_k} |"
                        for y_k in local_s_omega_py_keys:
                            val_node = alt_add_psym.get((x_k,y_k))
                            val = model.get_value(val_node) if val_node else None
                            row += f" {val.constant_value() if val else '?'}"
                        print(row)

# --- Main Execution Block ---
if __name__ == "__main__":
    run_final_core_axiom_tests(2)
    run_final_core_axiom_tests(3)
    run_final_core_axiom_tests(4)