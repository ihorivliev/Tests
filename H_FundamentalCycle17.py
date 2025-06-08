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

# --- Helper functions for Axiom Assertions & Table Creation ---
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

# Defined assert_idr_right_identity
def assert_idr_right_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys:
        assertions_list.append(Equals(table[(x_k, u_py_key)], Int(x_k)))

# Defined assert_idl_left_identity
def assert_idl_left_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys:
        assertions_list.append(Equals(table[(u_py_key, x_k)], Int(x_k)))
        
def assert_cca2_two_sided_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                                   s_omega_py_keys: List[int], u_py_key: int):
    assert_idr_right_identity(assertions_list, table, s_omega_py_keys, u_py_key) # Calls helper
    assert_idl_left_identity(assertions_list, table, s_omega_py_keys, u_py_key) # Calls helper

def assert_cca3_classical_dfi(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              py_dfi_elements: List[int], current_omega_val: int,
                              dfi_smt_elements: List[FNode], omit_cell: Tuple[int,int] = None):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                current_cell = (dfi_a_py, dfi_b_py)
                symmetric_omit_cell = (omit_cell[1], omit_cell[0]) if omit_cell else None
                
                skip_assertion = False
                if omit_cell:
                    if current_cell == omit_cell:
                        skip_assertion = True
                    # If omit_cell is not diagonal, also skip its symmetric counterpart for safety
                    # (though for (1,1) this second condition is redundant with the first)
                    elif omit_cell[0] != omit_cell[1] and current_cell == symmetric_omit_cell:
                        skip_assertion = True
                
                if skip_assertion:
                    continue

                py_sum = dfi_a_py + dfi_b_py
                if py_sum < current_omega_val:
                    sum_smt_val = Int(py_sum)
                    if any(sum_smt_val.constant_value() == d.constant_value() for d in dfi_smt_elements):
                        assertions_list.append(Equals(table[current_cell], sum_smt_val))

def assert_cca4_dfi_overflow(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               py_dfi_elements: List[int], current_omega_val: int, local_U_SMT: FNode,
                               omit_cells: List[Tuple[int,int]] = None):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                current_cell = (dfi_a_py, dfi_b_py)
                skip = False
                if omit_cells:
                    symmetric_cell = (dfi_b_py, dfi_a_py) 
                    if current_cell in omit_cells or symmetric_cell in omit_cells:
                         if current_cell in omit_cells or (symmetric_cell in omit_cells and current_cell != symmetric_cell) : # ensure we omit both if in list
                            skip = True
                if skip:
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

def print_model_table(model: Union[Dict,None], table: Dict[Tuple[int,int],FNode], s_omega_py_keys: List[int], test_name_detail: str = ""):
    if model:
        if test_name_detail: print(f"    Model Table ({test_name_detail}):")
        header = "⊕ |" + "".join([f" {str(k):<2}" for k in s_omega_py_keys])
        print(f"    {header}")
        print(f"    ---" + "".join(["----" for _ in s_omega_py_keys]))
        for x_k in s_omega_py_keys:
            row_str = f"    {str(x_k):<2}|"
            for y_k in s_omega_py_keys:
                val_node = table.get((x_k,y_k))
                val = model.get_value(val_node) if val_node is not None else None
                row_str += f" {str(val.constant_value() if val else '?'):<2}"
            print(row_str)
    else:
        print("    No model content to print (solver_model was None).")

def find_all_models(solver: Solver, table_vars: Dict[Tuple[int,int],FNode], 
                    s_omega_py_keys: List[int], max_models=10) -> List[Dict]:
    found_models_objects = []
    iterations = 0
    while len(found_models_objects) < max_models:
        iterations += 1
        if iterations > max_models + 5 : 
            print(f"    Exceeded max iterations ({max_models+5}), breaking model search.")
            break
        
        result = solver.solve()

        if result:
            model_obj = solver.get_model()
            if model_obj is None: 
                print("Warning: solver.solve() was True but get_model() returned None. Breaking.")
                break
            found_models_objects.append(model_obj)
            
            blocking_clauses = []
            if not s_omega_py_keys: break 
            for x_k in s_omega_py_keys:
                for y_k in s_omega_py_keys:
                    cell_var = table_vars[(x_k,y_k)]
                    model_cell_value = model_obj.get_value(cell_var)
                    if model_cell_value is not None and model_cell_value.is_constant():
                         blocking_clauses.append(NotEquals(cell_var, model_cell_value))
            
            if not blocking_clauses and s_omega_py_keys : 
                break
            if blocking_clauses:
                solver.add_assertion(Or(blocking_clauses))
            else: 
                break
        else:
            break 
    return found_models_objects

# --- Main test function for Model Counting ---
def run_model_counting_tests(current_omega_val: int):
    print(f"\n--- Model Counting Tests for Omega={current_omega_val} ---")

    if current_omega_val < 1: print("OMEGA_VAL must be >= 1."); return
        
    local_U_SMT = Int(0) 
    local_DFI_SMT_ELEMENTS = [Int(i) for i in range(1, current_omega_val)]
    local_S_OMEGA_SMT_ELEMENTS = [local_U_SMT] + local_DFI_SMT_ELEMENTS
    local_s_omega_py_keys = [e.constant_value() for e in local_S_OMEGA_SMT_ELEMENTS]
    local_py_dfi_elements = [val.constant_value() for val in local_DFI_SMT_ELEMENTS]

    print(f"S_Omega = {local_s_omega_py_keys} (U={local_U_SMT.constant_value()}); DFI = {local_py_dfi_elements if local_py_dfi_elements else 'empty'}")

    STD_AVCA_TABLE = {} 
    for x_k_std in local_s_omega_py_keys:
        for y_k_std in local_s_omega_py_keys:
            STD_AVCA_TABLE[(x_k_std, y_k_std)] = get_std_avca_add_v11_result(x_k_std, y_k_std, current_omega_val, local_U_SMT.constant_value())

    # --- Part 1: Uniqueness via Model Counting for Core Axioms ---
    print(f"\n--- Part 1 (Omega={current_omega_val}): Model Count for CoreAxioms {{CCA1_Range, Id_TwoSided, Cls, Ovfl}} ---")
    R_core_mc = create_symbolic_table("RcoreMC", current_omega_val, local_s_omega_py_keys)
    CoreAxioms_mc = []
    assert_cca1_range(CoreAxioms_mc, R_core_mc, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_cca2_two_sided_identity(CoreAxioms_mc, R_core_mc, local_s_omega_py_keys, local_U_SMT.constant_value())
    assert_cca3_classical_dfi(CoreAxioms_mc, R_core_mc, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    assert_cca4_dfi_overflow(CoreAxioms_mc, R_core_mc, local_py_dfi_elements, current_omega_val, local_U_SMT)
    
    with Solver(name="z3", logic="QF_LIA") as s:
        for an_assertion in CoreAxioms_mc: s.add_assertion(an_assertion)
        
        all_core_models = find_all_models(s, R_core_mc, local_s_omega_py_keys, max_models=5)
        print(f"  Number of models found satisfying CoreAxioms: {len(all_core_models)}")
        if len(all_core_models) == 1:
            print("    SUCCESS (EXPECTED): Exactly 1 model found (Standard AVCA Table). Uniqueness confirmed by enumeration.")
            print_model_table(all_core_models[0], R_core_mc, local_s_omega_py_keys, "CoreAxioms Model 1")
        elif len(all_core_models) > 1:
            print(f"    WARNING (UNEXPECTED): {len(all_core_models)} models found for CoreAxioms. Expected 1. Models:")
            for i, model_obj in enumerate(all_core_models):
                print(f"    --- Model {i+1} ---")
                print_model_table(model_obj, R_core_mc, local_s_omega_py_keys, f"CoreAxioms Model {i+1}")
        else: 
            print("    ERROR: No model found for CoreAxioms - This should mean UNSAT (inconsistent axioms).")

    # --- Part 2: Model Counting for Weakened Cls Axiom (Ω=3), keeping Commutativity ---
    if current_omega_val == 3:
        print(f"\n--- Part 2 (Omega={current_omega_val}): Model Count for Weakened Cls (omit 1+1=2), keeping Commutativity ---")
        R_weak_cls = create_symbolic_table("RweakCls", current_omega_val, local_s_omega_py_keys)
        WeakCls_assertions = []
        assert_cca1_range(WeakCls_assertions, R_weak_cls, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(WeakCls_assertions, R_weak_cls, local_s_omega_py_keys, local_U_SMT.constant_value())
        assert_cca3_classical_dfi(WeakCls_assertions, R_weak_cls, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS, omit_cell=(1,1)) # Omit 1+1=2
        assert_cca4_dfi_overflow(WeakCls_assertions, R_weak_cls, local_py_dfi_elements, current_omega_val, local_U_SMT)
        assert_explicit_commutativity(WeakCls_assertions, R_weak_cls, local_s_omega_py_keys) # Explicit Commutativity

        with Solver(name="z3", logic="QF_LIA") as s:
            for an_assertion in WeakCls_assertions: s.add_assertion(an_assertion)

            all_weak_cls_models = find_all_models(s, R_weak_cls, local_s_omega_py_keys, max_models=5)
            print(f"  Number of models found satisfying Weakened Cls + Commutativity: {len(all_weak_cls_models)}")
            if len(all_weak_cls_models) > 1: 
                print(f"    SUCCESS (EXPECTED {len(all_weak_cls_models)}): Multiple models found.")
                for i, model_obj in enumerate(all_weak_cls_models):
                    print(f"    --- Model {i+1} ---")
                    print_model_table(model_obj, R_weak_cls, local_s_omega_py_keys, f"WeakenedClsComm Model {i+1}")
            elif len(all_weak_cls_models) == 1:
                 print("    WARNING (UNEXPECTED): Only 1 model found. Expected more freedom from weakened Cls.")
                 print_model_table(all_weak_cls_models[0], R_weak_cls, local_s_omega_py_keys, "WeakenedClsComm Model 1")
            else:
                print("    ERROR: No model found for Weakened Cls + Commutativity.")

    # --- Part 3: Necessity of Left-Identity (from Two-Sided Identity) via Model Counting ---
    print(f"\n--- Part 3 (Omega={current_omega_val}): Model Count when Left-ID (U@x=x) is Dropped ---")
    R_no_lid = create_symbolic_table("RnoLID", current_omega_val, local_s_omega_py_keys)
    NoLID_assertions = []
    assert_cca1_range(NoLID_assertions, R_no_lid, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_idr_right_identity(NoLID_assertions, R_no_lid, local_s_omega_py_keys, local_U_SMT.constant_value()) # ONLY Right ID
    assert_cca3_classical_dfi(NoLID_assertions, R_no_lid, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    assert_cca4_dfi_overflow(NoLID_assertions, R_no_lid, local_py_dfi_elements, current_omega_val, local_U_SMT)
    
    with Solver(name="z3", logic="QF_LIA") as s:
        for a_assertion in NoLID_assertions: s.add_assertion(a_assertion)
        all_no_lid_models = find_all_models(s, R_no_lid, local_s_omega_py_keys, max_models=5) 
        print(f"  Number of models found when Left-ID is dropped: {len(all_no_lid_models)}")

        if len(all_no_lid_models) >= 1: # Expecting at least 1, likely >1 if standard AVCA has Left-ID
            print(f"    INFO: Found {len(all_no_lid_models)} model(s). Analyzing properties...")
        else: 
             print("    ERROR: No models found when Left-ID is dropped. Axiom set might be inconsistent.")

        failed_lid_count = 0
        non_comm_count = 0
        std_table_count = 0 # Count how many are the standard AVCA table

        for i, model_obj in enumerate(all_no_lid_models):
            print(f"    --- Model {i+1} ---")
            print_model_table(model_obj, R_no_lid, local_s_omega_py_keys, f"NoLeftID Model {i+1}")
            
            # Check if this model matches STD_AVCA_TABLE
            is_std_model = True
            for k_cell, v_std_val in STD_AVCA_TABLE.items():
                model_val = model_obj.get_value(R_no_lid[k_cell])
                if model_val.constant_value() != v_std_val:
                    is_std_model = False; break
            if is_std_model: std_table_count +=1
            print(f"      Model matches Standard AVCA Table: {is_std_model}")
            
            model_fails_lid = False
            for x_k_check in local_s_omega_py_keys:
                if model_obj.get_value(R_no_lid[(local_U_SMT.constant_value(), x_k_check)]) != Int(x_k_check):
                    model_fails_lid = True; break
            if model_fails_lid: failed_lid_count +=1
            print(f"      Model satisfies Left-ID: {not model_fails_lid}")

            model_is_comm = True
            if len(local_s_omega_py_keys) > 1:
                for r_idx in range(len(local_s_omega_py_keys)):
                    for c_idx in range(r_idx + 1, len(local_s_omega_py_keys)):
                        k1,k2 = local_s_omega_py_keys[r_idx], local_s_omega_py_keys[c_idx]
                        val1 = model_obj.get_value(R_no_lid[(k1,k2)])
                        val2 = model_obj.get_value(R_no_lid[(k2,k1)])
                        if val1.constant_value() != val2.constant_value() : 
                            model_is_comm = False; break
                    if not model_is_comm: break
            if not model_is_comm: non_comm_count +=1
            print(f"      Model is Commutative: {model_is_comm}")

        if len(all_no_lid_models) > 0 :
             print(f"    Summary for Dropped Left-ID (found {len(all_no_lid_models)} models):")
             print(f"      Models matching Standard AVCA: {std_table_count}")
             print(f"      Models failing Left-ID: {failed_lid_count}")
             print(f"      Models that were Non-Commutative: {non_comm_count}")
             if std_table_count < len(all_no_lid_models) or failed_lid_count > 0 or non_comm_count > 0 :
                 print("    CONCLUSION: Dropping Left-ID allows non-standard, non-LeftID, or non-commutative tables (EXPECTED).")
             else: # All models were standard, which would be very unexpected
                 print("    CONCLUSION: All models were standard AVCA even with Left-ID dropped (UNEXPECTED - check logic).")


    # --- Part 4: Necessity of Symmetric/Full Ovfl for Commutativity (P-SYM) via Model Counting ---
    if current_omega_val == 3: 
        print(f"\n--- Part 4 (P-SYM Model Count for Omega={current_omega_val}): Weakening Ovfl for (1,2)/(2,1) ---")
        R_psym_mc = create_symbolic_table("RpsymMC", current_omega_val, local_s_omega_py_keys)
        assertions_psym_mc = []
        assert_cca1_range(assertions_psym_mc, R_psym_mc, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_psym_mc, R_psym_mc, local_s_omega_py_keys, local_U_SMT.constant_value())
        assert_cca3_classical_dfi(assertions_psym_mc, R_psym_mc, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
        
        omit_ovfl_cells_psym = []
        if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
            omit_ovfl_cells_psym.extend([(1,2), (2,1)]) 
        assert_cca4_dfi_overflow(assertions_psym_mc, R_psym_mc, local_py_dfi_elements, current_omega_val, local_U_SMT, omit_cells=omit_ovfl_cells_psym)
        # Ensure (2,2)=U is still asserted
        if 2 in local_py_dfi_elements and (2,2) not in omit_ovfl_cells_psym: 
             if (2+2) >= current_omega_val: 
                 assertions_psym_mc.append(Equals(R_psym_mc[(2,2)], local_U_SMT))
        
        with Solver(name="z3", logic="QF_LIA") as s:
            for an_assertion in assertions_psym_mc: s.add_assertion(an_assertion)
            all_psym_models = find_all_models(s, R_psym_mc, local_s_omega_py_keys, max_models=10)
            print(f"  Number of models found when Ovfl for (1,2)/(2,1) is weakened: {len(all_psym_models)}")

            non_commutative_psym_models_count = 0
            if len(all_psym_models) > 0:
                print("    Models found (checking for non-commutativity on (1,2) vs (2,1)):")
            for i, model_obj in enumerate(all_psym_models):
                print(f"    --- Model {i+1} ---")
                print_model_table(model_obj, R_psym_mc, local_s_omega_py_keys, f"WeakenedOvfl_PSYM Model {i+1}")
                model_is_comm_for_12 = True
                if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
                    val12_node = R_psym_mc.get((1,2))
                    val21_node = R_psym_mc.get((2,1))
                    val12 = model_obj.get_value(val12_node) if val12_node else None
                    val21 = model_obj.get_value(val21_node) if val21_node else None

                    if val12 and val21 and val12.constant_value() != val21.constant_value():
                        model_is_comm_for_12 = False
                        non_commutative_psym_models_count += 1
                        print(f"      Model is NON-COMMUTATIVE for (1,2): {val12.constant_value()} vs {val21.constant_value()}")
                    elif val12 and val21:
                        print(f"      Model is Commutative for (1,2): {val12.constant_value()} vs {val21.constant_value()}")
                    else:
                        print(f"      Could not get values for (1,2) or (2,1) in model {i+1}")

            if non_commutative_psym_models_count > 0:
                print(f"    SUCCESS (EXPECTED): Found {non_commutative_psym_models_count} non-commutative model(s) for (1,2) pair out of {len(all_psym_models)}.")
            elif len(all_psym_models) > 0:
                print(f"    WARNING (UNEXPECTED): All {len(all_psym_models)} models were commutative for (1,2) despite weakened Ovfl.")
            elif len(all_psym_models) == 0:
                 print(f"    ERROR: No models found. Axiom set might be inconsistent.")

# --- Main Execution Block ---
if __name__ == "__main__":
    # Ensure function definition is above this block
    run_model_counting_tests(3) 
    # run_model_counting_tests(2) # Can add to check MC.1 and MC.3 for Omega=2