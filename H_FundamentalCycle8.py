from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Exists, ForAll,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, LE, NotEquals,
                             get_model) # Retaining for now, though direct s.get_model() is preferred
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Global Symbolic Constants ---
U_S = Int(0) # Canonical SMT representation for Unio
UNDEFINED_VAL_S = Int(-1) # A value outside S_Omega for testing Totality

# --- Helper to get standard AVCA add_v1.1 result (integer representation) ---
def get_std_avca_add_v11_result(val_a_int: int, val_b_int: int, current_omega_val: int) -> int:
    u_val = U_S.constant_value()
    if val_a_int == u_val: return val_b_int
    if val_b_int == u_val: return val_a_int
    int_sum = val_a_int + val_b_int
    return int_sum if int_sum < current_omega_val else u_val

# Memoization cache for smt_alt_add_expr_dynamic
_smt_alt_add_expr_cache: Dict[Tuple[FNode, FNode, int, str], FNode] = {}


def smt_alt_add_expr_dynamic(val_a_smt_op: FNode, val_b_smt_op: FNode,
                             current_omega_val_inner: int,
                             current_s_omega_py_keys: List[int],
                             current_alt_add_results: Dict[Tuple[int,int],FNode],
                             cache_prefix: str # Not strictly used by cache key, but good for context
                             ) -> FNode:
    # This function builds an SMT ITE cascade representing the symbolic table lookup
    # for val_a_smt_op @ val_b_smt_op using the SMT variables in current_alt_add_results.

    final_else_expr = U_S # Default if no conditions match (CCA1 should prevent this for valid inputs)
    expr = final_else_expr
    for x_key in reversed(current_s_omega_py_keys):
        for y_key in reversed(current_s_omega_py_keys):
            condition = And(Equals(val_a_smt_op, Int(x_key)), Equals(val_b_smt_op, Int(y_key)))
            value_for_this_cell = current_alt_add_results[(x_key, y_key)]
            expr = Ite(condition, value_for_this_cell, expr)
    return expr

def run_deep_axiom_scrutiny_tests(current_omega_val: int):
    print(f"\n--- Deep Axiom Scrutiny for Omega={current_omega_val} ---")

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
            STD_AVCA_TABLE[(x_k_std, y_k_std)] = get_std_avca_add_v11_result(x_k_std, y_k_std, current_omega_val)

    def create_alt_add_table(prefix: str) -> Dict[Tuple[int, int], FNode]:
        table = {}
        for x_k in local_s_omega_py_keys:
            for y_k in local_s_omega_py_keys:
                table[(x_k, y_k)] = Symbol(f"{prefix}_{x_k}_{y_k}_w{current_omega_val}", SMT_INT_TYPE)
        return table

    def assert_cca1_totality(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode]):
        for x_k in local_s_omega_py_keys:
            for y_k in local_s_omega_py_keys:
                res_var = table[(x_k, y_k)]
                assertions_list.append(Or([Equals(res_var, smt_elem) for smt_elem in local_S_OMEGA_SMT_ELEMENTS]))

    def assert_cca2_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode]):
        u_k = local_U_SMT.constant_value()
        for x_k in local_s_omega_py_keys:
            x_smt = Int(x_k)
            assertions_list.append(Equals(table[(u_k, x_k)], x_smt))
            assertions_list.append(Equals(table[(x_k, u_k)], x_smt))

    def assert_full_cca3(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode]):
        if local_py_dfi_elements:
            for dfi_a_py in local_py_dfi_elements:
                for dfi_b_py in local_py_dfi_elements:
                    py_sum = dfi_a_py + dfi_b_py
                    if py_sum < current_omega_val:
                        sum_smt_val = Int(py_sum)
                        if any(sum_smt_val.constant_value() == d.constant_value() for d in local_DFI_SMT_ELEMENTS):
                            assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], sum_smt_val))

    def assert_full_cca4(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode]):
        if local_py_dfi_elements:
            for dfi_a_py in local_py_dfi_elements:
                for dfi_b_py in local_py_dfi_elements:
                    py_sum = dfi_a_py + dfi_b_py
                    if py_sum >= current_omega_val:
                        assertions_list.append(Equals(table[(dfi_a_py, dfi_b_py)], local_U_SMT))

    # --- Test Suite 1: Necessity of CCA3 & CCA4 conditions ---
    print(f"\n--- Test 1.A (Omega={current_omega_val}): Weaken CCA3, No Commutativity Assumed ---")
    alt_add_t1a = create_alt_add_table("t1a")
    assertions_t1a = []
    assert_cca1_totality(assertions_t1a, alt_add_t1a)
    assert_cca2_identity(assertions_t1a, alt_add_t1a)
    assert_full_cca4(assertions_t1a, alt_add_t1a)

    temp_cca3_assertions = []
    if local_py_dfi_elements:
        for dfi_a_py_t1a in local_py_dfi_elements: # Renamed loop var
            for dfi_b_py_t1a in local_py_dfi_elements: # Renamed loop var
                py_sum_t1a = dfi_a_py_t1a + dfi_b_py_t1a # Renamed
                if py_sum_t1a < current_omega_val:
                    sum_smt_val_t1a = Int(py_sum_t1a) # Renamed
                    if any(sum_smt_val_t1a.constant_value() == d.constant_value() for d in local_DFI_SMT_ELEMENTS):
                        skip_this_cca3 = False
                        if current_omega_val == 3 and dfi_a_py_t1a == 1 and dfi_b_py_t1a == 1: skip_this_cca3 = True
                        if current_omega_val == 4 and dfi_a_py_t1a == 1 and dfi_b_py_t1a == 1: skip_this_cca3 = True
                        # Add more specific omissions if needed for other Omega
                        if not skip_this_cca3:
                            temp_cca3_assertions.append(Equals(alt_add_t1a[(dfi_a_py_t1a, dfi_b_py_t1a)], sum_smt_val_t1a))
    assertions_t1a.extend(temp_cca3_assertions)

    differs_clauses_t1a = [NotEquals(alt_add_t1a[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in alt_add_t1a]
    assertions_t1a.append(Or(differs_clauses_t1a) if differs_clauses_t1a else TRUE()) # If no diffs, it implies it IS std table

    with Solver(name="z3") as s:
        for an_assertion in assertions_t1a: s.add_assertion(an_assertion)
        result_t1a = s.solve()
        print(f"  Test 1.A Result (Weaken CCA3): {'SAT (Differing table found - EXPECTED)' if result_t1a else 'UNSAT (Still unique - UNEXPECTED)'}")
        if result_t1a:
            print("    Proof: Weakening a CCA3 condition allows alternative tables satisfying CCA1,2,full CCA4.")
            model = s.get_model() # CORRECTED
            if model:
                print("    Alternative Model Found:")
                is_symmetric = True
                for x_k in local_s_omega_py_keys:
                    row_str = f"      {x_k} |"
                    for y_k in local_s_omega_py_keys:
                        val_node = alt_add_t1a.get((x_k,y_k))
                        val = model.get_value(val_node) if val_node else None
                        row_str += f" {val.constant_value() if val else '?'}"
                        if x_k != y_k:
                            val_xy = model.get_value(alt_add_t1a.get((x_k,y_k)))
                            val_yx = model.get_value(alt_add_t1a.get((y_k,x_k)))
                            if (val_xy and val_yx and val_xy != val_yx) or (not val_xy and val_yx) or (val_xy and not val_yx):
                                is_symmetric = False
                    print(row_str)
                print(f"    Model is Commutative: {is_symmetric}")
            else: print("    Solver returned SAT but no model was available.")
    
    print(f"\n--- Test 1.B (Omega={current_omega_val}): Weaken CCA4, No Commutativity Assumed ---")
    alt_add_t1b = create_alt_add_table("t1b")
    assertions_t1b = []
    assert_cca1_totality(assertions_t1b, alt_add_t1b)
    assert_cca2_identity(assertions_t1b, alt_add_t1b)
    assert_full_cca3(assertions_t1b, alt_add_t1b)

    temp_cca4_assertions = []
    if local_py_dfi_elements:
        for dfi_a_py_t1b in local_py_dfi_elements: # Renamed
            for dfi_b_py_t1b in local_py_dfi_elements: # Renamed
                py_sum_t1b = dfi_a_py_t1b + dfi_b_py_t1b # Renamed
                if py_sum_t1b >= current_omega_val:
                    skip_this_cca4 = False
                    if current_omega_val == 2 and dfi_a_py_t1b==1 and dfi_b_py_t1b==1: skip_this_cca4 = True
                    if current_omega_val == 3 and ((dfi_a_py_t1b==1 and dfi_b_py_t1b==2) or (dfi_a_py_t1b==2 and dfi_b_py_t1b==1)): skip_this_cca4 = True
                    if current_omega_val == 4 and ((dfi_a_py_t1b==1 and dfi_b_py_t1b==3) or (dfi_a_py_t1b==3 and dfi_b_py_t1b==1)): skip_this_cca4 = True
                    if not skip_this_cca4:
                        temp_cca4_assertions.append(Equals(alt_add_t1b[(dfi_a_py_t1b, dfi_b_py_t1b)], local_U_SMT))
    assertions_t1b.extend(temp_cca4_assertions)

    differs_clauses_t1b = [NotEquals(alt_add_t1b[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in alt_add_t1b]
    assertions_t1b.append(Or(differs_clauses_t1b) if differs_clauses_t1b else TRUE())

    with Solver(name="z3") as s:
        for an_assertion in assertions_t1b: s.add_assertion(an_assertion)
        result_t1b = s.solve()
        print(f"  Test 1.B Result (Weaken CCA4): {'SAT (Differing table found - EXPECTED)' if result_t1b else 'UNSAT (Still unique - UNEXPECTED)'}")
        if result_t1b:
            print("    Proof: Weakening a CCA4 condition allows alternative tables satisfying CCA1,2,full CCA3.")
            model = s.get_model() # CORRECTED
            if model:
                print("    Alternative Model Found:")
                is_symmetric = True
                for x_k in local_s_omega_py_keys:
                    row_str = f"      {x_k} |"
                    for y_k in local_s_omega_py_keys:
                        val_node = alt_add_t1b.get((x_k,y_k))
                        val = model.get_value(val_node) if val_node else None
                        row_str += f" {val.constant_value() if val else '?'}"
                        if x_k != y_k :
                            val_xy = model.get_value(alt_add_t1b.get((x_k,y_k)))
                            val_yx = model.get_value(alt_add_t1b.get((y_k,x_k)))
                            if (val_xy and val_yx and val_xy != val_yx) or (not val_xy and val_yx) or (val_xy and not val_yx):
                                is_symmetric = False
                    print(row_str)
                print(f"    Model is Commutative: {is_symmetric}")

    if current_omega_val >= 2:
        print(f"\n--- Test 2 (Omega={current_omega_val}): Necessity of Two-Sided Identity (CCA2) ---")
        alt_add_t2a = create_alt_add_table("t2a")
        assertions_t2a = []
        assert_cca1_totality(assertions_t2a, alt_add_t2a)
        assert_full_cca3(assertions_t2a, alt_add_t2a)
        assert_full_cca4(assertions_t2a, alt_add_t2a)
        for i_idx in range(len(local_s_omega_py_keys)):
            for j_idx in range(i_idx + 1, len(local_s_omega_py_keys)):
                k1,k2 = local_s_omega_py_keys[i_idx], local_s_omega_py_keys[j_idx]
                assertions_t2a.append(Equals(alt_add_t2a[(k1,k2)], alt_add_t2a[(k2,k1)]))
        u_k = local_U_SMT.constant_value()
        for x_k in local_s_omega_py_keys:
            assertions_t2a.append(Equals(alt_add_t2a[(x_k, u_k)], Int(x_k)))
        
        differs_clauses_t2a = [NotEquals(alt_add_t2a[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in alt_add_t2a]
        assertions_t2a.append(Or(differs_clauses_t2a) if differs_clauses_t2a else TRUE())

        with Solver(name="z3") as s:
            for an_assertion in assertions_t2a: s.add_assertion(an_assertion)
            result_t2a = s.solve()
            print(f"  Test 2.A Result (Weaken CCA2 - Left Identity U@x=x Omitted): {'SAT (Differing table - EXPECTED)' if result_t2a else 'UNSAT (Still unique - UNEXPECTED)'}")
            if result_t2a: print("    Proof: Omitting U@x=x from CCA2 allows alternative tables.")

        alt_add_t2b = create_alt_add_table("t2b")
        assertions_t2b = []
        assert_cca1_totality(assertions_t2b, alt_add_t2b)
        assert_full_cca3(assertions_t2b, alt_add_t2b)
        assert_full_cca4(assertions_t2b, alt_add_t2b)
        for i_idx in range(len(local_s_omega_py_keys)):
            for j_idx in range(i_idx + 1, len(local_s_omega_py_keys)):
                k1,k2 = local_s_omega_py_keys[i_idx], local_s_omega_py_keys[j_idx]
                assertions_t2b.append(Equals(alt_add_t2b[(k1,k2)], alt_add_t2b[(k2,k1)]))
        u_k = local_U_SMT.constant_value()
        for x_k in local_s_omega_py_keys:
            assertions_t2b.append(Equals(alt_add_t2b[(u_k, x_k)], Int(x_k)))
        
        differs_clauses_t2b = [NotEquals(alt_add_t2b[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in alt_add_t2b]
        assertions_t2b.append(Or(differs_clauses_t2b) if differs_clauses_t2b else TRUE())

        with Solver(name="z3") as s:
            for an_assertion in assertions_t2b: s.add_assertion(an_assertion)
            result_t2b = s.solve()
            print(f"  Test 2.B Result (Weaken CCA2 - Right Identity x@U=x Omitted): {'SAT (Differing table - EXPECTED)' if result_t2b else 'UNSAT (Still unique - UNEXPECTED)'}")
            if result_t2b: print("    Proof: Omitting x@U=x from CCA2 allows alternative tables.")

    if current_omega_val >= 3:
        print(f"\n--- Test 3 (Omega={current_omega_val}): General Non-Associativity Check (∃ non-assoc triplet) ---")
        alt_add_t3 = create_alt_add_table("t3_assoc")
        assertions_t3 = []
        assert_cca1_totality(assertions_t3, alt_add_t3)
        assert_cca2_identity(assertions_t3, alt_add_t3)
        assert_full_cca3(assertions_t3, alt_add_t3)
        assert_full_cca4(assertions_t3, alt_add_t3)

        sa = Symbol("sa_assoc", SMT_INT_TYPE)
        sb = Symbol("sb_assoc", SMT_INT_TYPE)
        sc = Symbol("sc_assoc", SMT_INT_TYPE)
        
        assertions_t3.extend([Or([Equals(sa, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
        assertions_t3.extend([Or([Equals(sb, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])
        assertions_t3.extend([Or([Equals(sc, s_el) for s_el in local_S_OMEGA_SMT_ELEMENTS])])

        _smt_alt_add_expr_cache.clear()
        op_ab_t3 = smt_alt_add_expr_dynamic(sa, sb, current_omega_val, local_s_omega_py_keys, alt_add_t3, "t3ab")
        lhs_t3 = smt_alt_add_expr_dynamic(op_ab_t3, sc, current_omega_val, local_s_omega_py_keys, alt_add_t3, "t3lhs")
        _smt_alt_add_expr_cache.clear()
        op_bc_t3 = smt_alt_add_expr_dynamic(sb, sc, current_omega_val, local_s_omega_py_keys, alt_add_t3, "t3bc")
        rhs_t3 = smt_alt_add_expr_dynamic(sa, op_bc_t3, current_omega_val, local_s_omega_py_keys, alt_add_t3, "t3rhs")

        assertions_t3.append(NotEquals(lhs_t3, rhs_t3))

        with Solver(name="z3") as s:
            for an_assertion in assertions_t3: s.add_assertion(an_assertion)
            result_t3 = s.solve()
            print(f"  Test 3 Result (Existential Non-Associativity): {'SAT (Counterexample found - EXPECTED for Ω>=3)' if result_t3 else 'UNSAT (No counterexample found - UNEXPECTED)'}")
            if result_t3:
                model = s.get_model() # CORRECTED
                if model:
                    print(f"    Counterexample Triplet: a={model.get_value(sa)}, b={model.get_value(sb)}, c={model.get_value(sc)}")
                else: print("    Solver returned SAT but no model was available.")
    
    print(f"\n--- Test 4 (Omega={current_omega_val}): Logical Independence of CCA1 (Totality) ---")
    alt_add_t4 = create_alt_add_table("t4_total")
    assertions_t4 = []
    assert_cca2_identity(assertions_t4, alt_add_t4)
    assert_full_cca3(assertions_t4, alt_add_t4)
    assert_full_cca4(assertions_t4, alt_add_t4)
    
    exists_undefined_cell_clauses = []
    for x_k in local_s_omega_py_keys:
        for y_k in local_s_omega_py_keys:
            exists_undefined_cell_clauses.append(Equals(alt_add_t4[(x_k,y_k)], UNDEFINED_VAL_S))
    
    assertions_t4.append(Or(exists_undefined_cell_clauses))

    with Solver(name="z3") as s:
        for an_assertion in assertions_t4: s.add_assertion(an_assertion)
        result_t4 = s.solve()
        print(f"  Test 4 Result (CCA1 Independence): {'SAT (Model where result is outside S_Omega found - EXPECTED)' if result_t4 else 'UNSAT (Result always in S_Omega even without CCA1 - UNEXPECTED)'}")
        if result_t4:
            print("    Proof: CCA2,3,4 do not by themselves force results to be in S_Omega.")
            model = s.get_model() # CORRECTED
            if model:
                found_undefined = False
                for x_k in local_s_omega_py_keys:
                    for y_k in local_s_omega_py_keys:
                        val_node = alt_add_t4.get((x_k,y_k))
                        val = model.get_value(val_node) if val_node else None
                        if val and val.constant_value() == UNDEFINED_VAL_S.constant_value():
                            print(f"    Cell ({x_k},{y_k}) resulted in UNDEFINED_VAL_S ({UNDEFINED_VAL_S.constant_value()})")
                            found_undefined = True
                            break
                    if found_undefined: break
                if not found_undefined: print("    Odd, SAT but no cell was UNDEFINED_VAL_S in printed check.")

if __name__ == "__main__":
    # Run minimality tests for Omega=2,3,4
    # run_deep_axiom_scrutiny_tests(1) # Test for Omega=1 to ensure robustness
    run_deep_axiom_scrutiny_tests(2)
    run_deep_axiom_scrutiny_tests(3) 
    run_deep_axiom_scrutiny_tests(4)