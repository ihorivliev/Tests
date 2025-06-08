from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, LE, NotEquals,
                             get_model)
from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
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

def assert_cca2_two_sided_identity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                                   s_omega_py_keys: List[int], u_py_key: int):
    for x_k in s_omega_py_keys: # x loops over all S_Omega
        x_smt = Int(x_k)
        assertions_list.append(Equals(table[(u_py_key, x_k)], x_smt)) # U @ x = x
        assertions_list.append(Equals(table[(x_k, u_py_key)], x_smt)) # x @ U = x

def assert_cca3_classical_dfi(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                              py_dfi_elements: List[int], current_omega_val: int,
                              dfi_smt_elements: List[FNode]):
    if py_dfi_elements:
        for dfi_a_py in py_dfi_elements:
            for dfi_b_py in py_dfi_elements:
                current_cell = (dfi_a_py, dfi_b_py)
                py_sum = dfi_a_py + dfi_b_py
                if py_sum < current_omega_val:
                    sum_smt_val = Int(py_sum)
                    # Ensure the sum is a valid DFI for this Omega before asserting
                    if any(sum_smt_val.constant_value() == d.constant_value() for d in dfi_smt_elements):
                        assertions_list.append(Equals(table[current_cell], sum_smt_val))

def assert_explicit_commutativity(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode], 
                                  s_omega_py_keys: List[int]):
    if len(s_omega_py_keys) > 1:
        for i in range(len(s_omega_py_keys)):
            for j in range(i + 1, len(s_omega_py_keys)):
                k1,k2 = s_omega_py_keys[i], s_omega_py_keys[j]
                assertions_list.append(Equals(table[(k1,k2)], table[(k2,k1)]))

def assert_inverse_count_law(assertions_list: List[FNode], table: Dict[Tuple[int,int],FNode],
                               py_dfi_elements: List[int], current_omega_val: int, 
                               s_omega_smt_elements: List[FNode], local_U_SMT: FNode):
    if not py_dfi_elements: # Law is vacuous if DFI is empty (Omega=1)
        return

    for a_val in py_dfi_elements: # a_val is a Python int e.g. 1, 2 for Omega=3
        a_smt = Int(a_val)
        
        is_inverse_conditions_for_a = []
        for x_val in py_dfi_elements: # x must be DFI
            x_smt = Int(x_val)
            # Condition: table[(a_val, x_val)] == U_SMT
            is_inverse_conditions_for_a.append(Equals(table[(a_val, x_val)], local_U_SMT))
            
        # Sum of (Ite(condition_is_inverse, 1, 0)) for all x in DFI
        sum_of_inverses_for_a = Plus(
            [Ite(cond, Int(1), Int(0)) for cond in is_inverse_conditions_for_a]
        ) if is_inverse_conditions_for_a else Int(0)
        
        # Assert this sum equals a_val
        assertions_list.append(Equals(sum_of_inverses_for_a, a_smt))

def print_model_table_if_sat(result: bool, solver_model: Union[Dict,None], 
                             table: Dict[Tuple[int,int],FNode], s_omega_py_keys: List[int], 
                             test_name: str, expectation_str: str, 
                             success_msg: str, failure_msg:str):
    outcome = "SAT" if result else "UNSAT"
    final_status_msg = ""
    expected_sat = "EXPECTED_SAT" in expectation_str.upper()
    expected_unsat = "EXPECTED_UNSAT" in expectation_str.upper()

    if result and expected_sat: final_status_msg = success_msg
    elif not result and expected_unsat: final_status_msg = success_msg
    elif result and expected_unsat: final_status_msg = failure_msg + " (Got SAT, Expected UNSAT)"
    elif not result and expected_sat: final_status_msg = failure_msg + " (Got UNSAT, Expected SAT)"
    else: final_status_msg = f"Outcome: {outcome} (Raw expectation: {expectation_str})"

    print(f"  SMT Result: {outcome} ({expectation_str})")
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

# --- Main test function for C-3: Inverse-Count Characterisation ---
def run_inverse_count_characterization_test(current_omega_val: int):
    print(f"\n--- Test C-3 (Inverse-Count Law Characterizes ⊕) for Omega={current_omega_val} ---")

    if current_omega_val < 1: print("OMEGA_VAL must be >= 1."); return
        
    local_U_SMT = Int(0) 
    local_DFI_SMT_ELEMENTS = [Int(i) for i in range(1, current_omega_val)]
    local_S_OMEGA_SMT_ELEMENTS = [local_U_SMT] + local_DFI_SMT_ELEMENTS
    local_s_omega_py_keys = [e.constant_value() for e in local_S_OMEGA_SMT_ELEMENTS] # Python ints for keys
    local_py_dfi_elements = [val.constant_value() for val in local_DFI_SMT_ELEMENTS]

    print(f"S_Omega = {local_s_omega_py_keys} (U={local_U_SMT.constant_value()}); DFI = {local_py_dfi_elements if local_py_dfi_elements else 'empty'}")

    STD_AVCA_TABLE = {}
    for x_k_std in local_s_omega_py_keys:
        for y_k_std in local_s_omega_py_keys:
            STD_AVCA_TABLE[(x_k_std, y_k_std)] = get_std_avca_add_v11_result(x_k_std, y_k_std, current_omega_val, local_U_SMT.constant_value())

    alt_add_results = create_symbolic_table("C3add", current_omega_val, local_s_omega_py_keys)
    
    C3_axioms = []
    # 1. CCA1_Range (Output Totality)
    assert_cca1_range(C3_axioms, alt_add_results, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    # 2. Id_⊕ (Two-Sided U-Identity)
    assert_cca2_two_sided_identity(C3_axioms, alt_add_results, local_s_omega_py_keys, local_U_SMT.constant_value())
    # 3. Cls_⊕ (DFI Classicality < Ω)
    assert_cca3_classical_dfi(C3_axioms, alt_add_results, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    # 4. InvCnt_⊕ (DFI Additive Inverse-Count Law)
    assert_inverse_count_law(C3_axioms, alt_add_results, local_py_dfi_elements, current_omega_val, local_S_OMEGA_SMT_ELEMENTS, local_U_SMT)
    # 5. Explicit Commutativity for alt_add_results (as per Auditor's C-3: "finite commutative monoid")
    assert_explicit_commutativity(C3_axioms, alt_add_results, local_s_omega_py_keys)

    # DFI Overflow cells (a+b >= Omega) are NOT explicitly constrained by an Ovfl axiom here.
    # Their values should be forced by the InvCnt_⊕ law.
    
    print(f"Applied {len(C3_axioms)} assertions for C-3 axioms.")

    # Assert that this table, defined by C-3 axioms, DIFFERs from standard AVCA ⊕
    differs_from_std_c3 = [NotEquals(alt_add_results[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in alt_add_results]
    assertion_differs_c3 = Or(differs_from_std_c3) if differs_from_std_c3 else FALSE()
    
    with Solver(name="z3", logic="QF_LIA") as s:
        for an_assertion in C3_axioms: s.add_assertion(an_assertion)
        s.add_assertion(assertion_differs_c3) # Ask: Can a differing table exist?
        
        result_c3_uniq = s.solve()
        print_model_table_if_sat(result_c3_uniq, s.get_model() if result_c3_uniq else None, alt_add_results, local_s_omega_py_keys,
                                 "Test C-3 (Query Uniqueness)", "EXPECTED_UNSAT",
                                 "Proof: C-3 axioms (Id, Cls, InvCnt, Comm, Range) uniquely force the standard AVCA ⊕-table.",
                                 "SAT - Differing table found! C-3 axioms are NOT sufficient for uniqueness (CONTRADICTS C-3 HYPOTHESIS)")

if __name__ == "__main__":
    run_inverse_count_characterization_test(3)
    # run_inverse_count_characterization_test(4) # Can be added later
