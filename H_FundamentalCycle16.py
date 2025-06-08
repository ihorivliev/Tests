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

# --- Helper functions for Axiom Assertions & Table Creation (copied from previous) ---
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

def assert_cca2_two_sided_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                                   s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys: # x loops over all S_Omega
        x_smt = Int(x_k)
        assertions_list.append(Equals(table[(u_py_key, x_k)], x_smt)) # U @ x = x
        assertions_list.append(Equals(table[(x_k, u_py_key)], x_smt)) # x @ U = x

def assert_cca3_classical_dfi(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              py_dfi_elements: List[int], current_omega_val: int,
                              dfi_smt_elements: List[FNode], omit_cell: Tuple[int,int] = None):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                current_cell = (dfi_a_py, dfi_b_py)
                symmetric_omit_cell = (omit_cell[1], omit_cell[0]) if omit_cell else None
                if omit_cell and (current_cell == omit_cell or (omit_cell[0]!=omit_cell[1] and current_cell == symmetric_omit_cell)):
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
                val = model.get_value(val_node) if val_node is not None else None
                row_str += f" {str(val.constant_value() if val else '?'):<2}"
            print(row_str)
    else:
        print("    No model to print or solver_model was None.")

def find_all_models(solver: Solver, table_vars: Dict[Tuple[int,int],FNode], s_omega_py_keys: List[int], max_models=10):
    models_found = []
    iterations = 0
    while len(models_found) < max_models:
        iterations += 1
        if iterations > max_models + 5 : # Safety break for unexpected loops
            print(f"    Exceeded max iterations ({max_models+5}), breaking model search.")
            break
        result = solver.solve()
        if result:
            model = solver.get_model()
            models_found.append(model) # Store the model object
            
            # Add blocking clause to find a *different* model next time
            blocking_clauses = []
            for x_k in s_omega_py_keys:
                for y_k in s_omega_py_keys:
                    cell_var = table_vars[(x_k,y_k)]
                    blocking_clauses.append(NotEquals(cell_var, model.get_value(cell_var)))
            solver.add_assertion(Or(blocking_clauses))
        else:
            break # No more models
    return models_found

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

    # --- Part 1: Uniqueness via Model Counting for Core Axioms ---
    print(f"\n--- Part 1 (Omega={current_omega_val}): Model Count for CoreAxioms {{CCA1_Range, Id_TwoSided, Cls, Ovfl}} ---")
    R_core = create_symbolic_table("Rcore", current_omega_val, local_s_omega_py_keys)
    CoreAxioms_assertions = []
    assert_cca1_range(CoreAxioms_assertions, R_core, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_cca2_two_sided_identity(CoreAxioms_assertions, R_core, local_s_omega_py_keys, local_U_SMT.constant_value())
    assert_cca3_classical_dfi(CoreAxioms_assertions, R_core, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    assert_cca4_dfi_overflow(CoreAxioms_assertions, R_core, local_py_dfi_elements, current_omega_val, local_U_SMT)
    
    with Solver(name="z3", logic="QF_LIA") as s: # Quantifier-Free Linear Integer Arithmetic
        for an_assertion in CoreAxioms_assertions: s.add_assertion(an_assertion)
        
        all_core_models = find_all_models(s, R_core, local_s_omega_py_keys, max_models=5) # Look for up to 5 models
        print(f"  Number of models found satisfying CoreAxioms: {len(all_core_models)}")
        if len(all_core_models) == 1:
            print("    SUCCESS: Exactly 1 model found (Standard AVCA Table) - Uniqueness confirmed by enumeration.")
            print_model_table(all_core_models[0], R_core, local_s_omega_py_keys)
        elif len(all_core_models) > 1:
            print("    WARNING: Multiple models found for CoreAxioms - Uniqueness FAILED. Models:")
            for i, model_obj in enumerate(all_core_models):
                print(f"    --- Model {i+1} ---")
                print_model_table(model_obj, R_core, local_s_omega_py_keys)
        else: # 0 models
            print("    ERROR: No model found for CoreAxioms - This should not happen (UNSAT implies inconsistency).")


    # --- Part 2: Model Counting for Weakened Cls Axiom (Ω=3) ---
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
                print("    SUCCESS: Multiple models found (EXPECTED, e.g., standard and 1+1=U).")
                for i, model_obj in enumerate(all_weak_cls_models):
                    print(f"    --- Model {i+1} ---")
                    print_model_table(model_obj, R_weak_cls, local_s_omega_py_keys)
            elif len(all_weak_cls_models) == 1:
                print("    WARNING: Only 1 model found - Expected more freedom from weakened Cls.")
                print_model_table(all_weak_cls_models[0], R_weak_cls, local_s_omega_py_keys)
            else:
                print("    ERROR: No model found for Weakened Cls + Commutativity.")

if __name__ == "__main__":
    run_model_counting_tests(3) 
    # We can add run_model_counting_tests(2) and run_model_counting_tests(4) later
    # For Omega=2, weakening Cls should have no effect as Cls is vacuous.
    # For Omega=4, weakening one Cls literal should also yield multiple models.