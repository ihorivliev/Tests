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
                current_cell = (dfi_a_py, dfi_b_py)
                # For omit_cell, if it's (1,1), only (1,1) is omitted.
                # If we needed symmetric omission for non-diagonal, that would be more complex here.
                # For N-Cls.lit testing 1+1=2, omit_cell=(1,1) is sufficient.
                if omit_cell and current_cell == omit_cell:
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
                    # For P-SYM, we omit (1,2) and (2,1) symmetrically if they are in omit_cells
                    if current_cell in omit_cells:
                        skip = True
                if skip:
                    continue
                
                py_sum = dfi_a_py + dfi_b_py
                if py_sum >= current_omega_val:
                    assertions_list.append(Equals(table[current_cell], local_U_SMT))

def print_model_table_if_sat(result: bool, solver_model: Union[Dict,None], 
                             table: Dict[Tuple[int,int],FNode], s_omega_py_keys: List[int], 
                             test_name: str, expectation_str: str, 
                             success_msg: str, failure_msg:str): # failure_msg for when result contradicts expectation
    outcome = "SAT" if result else "UNSAT"
    final_status_msg = ""

    expected_sat = "EXPECTED_SAT" in expectation_str.upper()
    expected_unsat = "EXPECTED_UNSAT" in expectation_str.upper()

    if result and expected_sat: 
        final_status_msg = success_msg
    elif not result and expected_unsat: 
        final_status_msg = success_msg
    elif result and expected_unsat: 
        final_status_msg = failure_msg + " (Got SAT, Expected UNSAT)"
    elif not result and expected_sat: 
        final_status_msg = failure_msg + " (Got UNSAT, Expected SAT)"
    else: 
        final_status_msg = f"Outcome: {outcome} (Raw expectation: {expectation_str})"


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

# --- Main test function for "Axiom Component Necessity Grid" tests ---
def run_axiom_component_necessity_tests(current_omega_val: int):
    print(f"\n--- Axiom Component Necessity Tests for Omega={current_omega_val} ---")
    print(f"    Testing necessity of components within CoreAxioms = {{CCA1_Range, CCA2_TwoSided, CCA3_Cls, CCA4_Ovfl}}")

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

    # --- Test N.1.a (Necessity of Left-Identity U⊕x = x from CCA2_TwoSided) ---
    # Axioms: CCA1_Range, CCA2_RightIdentityOnly, CCA3_Cls_Full, CCA4_Ovfl_Full.
    # Query: Can we find a table that is Non-Commutative? (Auditor: "drop left-ID → non-comm tables exist")
    print(f"\n--- Test N.1.a (Omega={current_omega_val}): Drop Left-ID (U@x=x), Check for Non-Commutativity ---")
    R_n1a = create_symbolic_table("n1a", current_omega_val, local_s_omega_py_keys)
    assertions_n1a = []
    assert_cca1_range(assertions_n1a, R_n1a, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
    assert_idr_right_identity(assertions_n1a, R_n1a, local_s_omega_py_keys, local_U_SMT.constant_value()) # ONLY Right ID
    assert_cca3_classical_dfi(assertions_n1a, R_n1a, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS)
    assert_cca4_dfi_overflow(assertions_n1a, R_n1a, local_py_dfi_elements, current_omega_val, local_U_SMT)

    non_comm_clauses_n1a = []
    if len(local_s_omega_py_keys) > 1:
        for i in range(len(local_s_omega_py_keys)):
            for j in range(i + 1, len(local_s_omega_py_keys)):
                k1,k2 = local_s_omega_py_keys[i], local_s_omega_py_keys[j]
                non_comm_clauses_n1a.append(NotEquals(R_n1a[(k1,k2)], R_n1a[(k2,k1)]))
    assertion_is_non_commutative = Or(non_comm_clauses_n1a) if non_comm_clauses_n1a else FALSE()
    assertions_n1a.append(assertion_is_non_commutative) # Assert table IS non-commutative

    with Solver(name="z3") as s:
        for a_assertion in assertions_n1a: s.add_assertion(a_assertion)
        result_n1a = s.solve()
        print_model_table_if_sat(result_n1a, s.get_model() if result_n1a else None, R_n1a, local_s_omega_py_keys,
                                 "Test N.1.a", "EXPECTED_SAT",
                                 "Proof: Omitting U@x=x (Left-ID) allows non-commutative tables.",
                                 "UNSAT - IdR+Cls+Ovfl implies Comm - UNEXPECTED")

    # --- Test N.2.b (Necessity of a Cls literal for Uniqueness, check if alt table is still Comm) ---
    # Auditor: "drop a single Cls literal ... -> alt but still commutative table"
    if current_omega_val == 3 : # This test is most illustrative for Omega=3
        print(f"\n--- Test N.2.b (Omega={current_omega_val}): Weaken Cls (1+1=2), Check Comm of Alt Table ---")
        R_ncls = create_symbolic_table("nCls", current_omega_val, local_s_omega_py_keys)
        assertions_ncls_base = [] 
        assert_cca1_range(assertions_ncls_base, R_ncls, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_ncls_base, R_ncls, local_s_omega_py_keys, local_U_SMT.constant_value()) # FULL Two-Sided ID
        assert_cca3_classical_dfi(assertions_ncls_base, R_ncls, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS, omit_cell=(1,1)) # Omit 1+1=2
        assert_cca4_dfi_overflow(assertions_ncls_base, R_ncls, local_py_dfi_elements, current_omega_val, local_U_SMT) 
        
        # Query 1: Does an alternative (differing from standard) table exist?
        list_differs_cls = [NotEquals(R_ncls[k], Int(v)) for k,v in STD_AVCA_TABLE.items() if k in R_ncls]
        assertion_differs_ncls = Or(list_differs_cls) if list_differs_cls else FALSE()
        
        print("--- Query N.2.b.1: Uniqueness of Alternative Table (from weakened Cls) ---")
        with Solver(name="z3") as s_uniq_cls:
            for a in assertions_ncls_base: s_uniq_cls.add_assertion(a)
            s_uniq_cls.add_assertion(assertion_differs_ncls)
            res_uniq_ncls = s_uniq_cls.solve()
            print_model_table_if_sat(res_uniq_ncls, s_uniq_cls.get_model() if res_uniq_ncls else None, R_ncls, local_s_omega_py_keys,
                                     "N.2.b.1 (Query Uniqueness)", "EXPECTED_SAT",
                                     "Proof: Omitting Cls literal '1+1=2' allows alternative tables.",
                                     "UNSAT - Weakened Cls still forces unique std table - UNEXPECTED")
            
        # Query 2: If alternative tables exist, are they necessarily commutative?
        if res_uniq_ncls: 
            print("--- Query N.2.b.2: Commutativity of Alternative Table (from weakened Cls) ---")
            non_comm_clauses_ncls_alt = []
            if len(local_s_omega_py_keys) > 1:
                for i in range(len(local_s_omega_py_keys)):
                    for j in range(i + 1, len(local_s_omega_py_keys)):
                        k1,k2 = local_s_omega_py_keys[i], local_s_omega_py_keys[j]
                        non_comm_clauses_ncls_alt.append(NotEquals(R_ncls[(k1,k2)], R_ncls[(k2,k1)]))
            assert_non_comm_ncls_alt = Or(non_comm_clauses_ncls_alt) if non_comm_clauses_ncls_alt else FALSE()
            
            with Solver(name="z3") as s_comm_cls:
                for a_assertion in assertions_ncls_base: s_comm_cls.add_assertion(a_assertion) 
                s_comm_cls.add_assertion(assert_non_comm_ncls_alt) # Assert it's NON-commutative
                result_ncls_comm_check = s_comm_cls.solve()
                print_model_table_if_sat(result_ncls_comm_check, s_comm_cls.get_model() if result_ncls_comm_check else None, R_ncls, local_s_omega_py_keys,
                                         "N.2.b.2 (Query Commutativity of Alt)", "EXPECTED_UNSAT", # Expecting UNSAT if auditor is right
                                         "Proof: Alternative tables from weakened Cls are still commutative.",
                                         "SAT - Non-commutative alternative found! (Contradicts auditor expectation for this part)")

    # --- Test N.3.a (P-SYM: Weakening Symmetric Ovfl breaks Commutativity for Ω=3) ---
    if current_omega_val == 3:
        print(f"\n--- Test N.3.a (P-SYM for Omega={current_omega_val}): Weakening Ovfl for (1,2)/(2,1) vs Commutativity ---")
        R_psym = create_symbolic_table("psym", current_omega_val, local_s_omega_py_keys)
        assertions_psym = []
        assert_cca1_range(assertions_psym, R_psym, local_s_omega_py_keys, local_S_OMEGA_SMT_ELEMENTS)
        assert_cca2_two_sided_identity(assertions_psym, R_psym, local_s_omega_py_keys, local_U_SMT.constant_value()) 
        assert_cca3_classical_dfi(assertions_psym, R_psym, local_py_dfi_elements, current_omega_val, local_DFI_SMT_ELEMENTS) 
        
        # Partial CCA4: Omit for (1,2) and (2,1). Assert for (2,2)=U for Omega=3.
        omit_these_ovfl_cells_psym = []
        if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
            omit_these_ovfl_cells_psym.extend([(1,2), (2,1)])
        assert_cca4_dfi_overflow(assertions_psym, R_psym, local_py_dfi_elements, current_omega_val, local_U_SMT, omit_cells=omit_these_ovfl_cells_psym)
        # Ensure (2,2)=U is still asserted by applying CCA4 to the remaining (non-omitted) cells
        # if not explicitly handled by omit_cells. The current helper asserts based on py_sum >= current_omega_val
        # for non-omitted cells. So (2,2) will be asserted = U if 2+2>=3.
        
        non_comm_12_21_psym_clauses = [] 
        if 1 in local_py_dfi_elements and 2 in local_py_dfi_elements:
            non_comm_12_21_psym_clauses.append(NotEquals(R_psym[(1,2)], R_psym[(2,1)]))
        assert_non_comm_12_21_psym = Or(non_comm_12_21_psym_clauses) if non_comm_12_21_psym_clauses else FALSE()
        
        assertions_psym.append(assert_non_comm_12_21_psym) 

        with Solver(name="z3") as s:
            for an_assertion in assertions_psym: s.add_assertion(an_assertion)
            result_P_SYM = s.solve()
            print_model_table_if_sat(result_P_SYM, s.get_model() if result_P_SYM else None, R_psym, local_s_omega_py_keys,
                                     "P-SYM", "EXPECTED_SAT",
                                     "Proof: Weakening symmetric CCA4_Ovfl for (1,2)/(2,1) allows non-commutative tables.",
                                     "UNSAT (Still commutative - UNEXPECTED)")

# --- Main Execution Block ---
if __name__ == "__main__":
    # Ensure function definition is above this block
    run_axiom_component_necessity_tests(2)
    run_axiom_component_necessity_tests(3)
    run_axiom_component_necessity_tests(4)