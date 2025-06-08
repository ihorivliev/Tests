from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, LE, NotEquals,
                             get_model) # get_model from shortcuts is fine if used with solver=s
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Configuration for this test ---
OMEGA_VAL = 3 # Focus on Omega=3
U_SMT = Int(0)
DFI_SMT_ELEMENTS = [Int(i) for i in range(1, OMEGA_VAL)]
S_OMEGA_SMT_ELEMENTS = [U_SMT] + DFI_SMT_ELEMENTS
s_omega_py_keys = [e.constant_value() for e in S_OMEGA_SMT_ELEMENTS]
py_dfi_elements = [val.constant_value() for val in DFI_SMT_ELEMENTS]

# --- Helper to get standard AVCA add_v1.1 result (integer representation) ---
def get_std_avca_add_v11_result(val_a_int: int, val_b_int: int, current_omega_val: int) -> int:
    u_val = U_SMT.constant_value()
    if val_a_int == u_val: return val_b_int
    if val_b_int == u_val: return val_a_int
    int_sum = val_a_int + val_b_int
    return int_sum if int_sum < current_omega_val else u_val

# --- Standard AVCA Table for Omega=3 ---
STD_AVCA_TABLE_OMEGA3 = {}
for x_k_std in s_omega_py_keys:
    for y_k_std in s_omega_py_keys:
        STD_AVCA_TABLE_OMEGA3[(x_k_std, y_k_std)] = get_std_avca_add_v11_result(x_k_std, y_k_std, OMEGA_VAL)

def run_axiom_minimality_tests():
    print(f"--- Testing Necessity of CCA3/CCA4 Conditions for Uniqueness (Omega={OMEGA_VAL}) ---")

    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    for x_py_key in s_omega_py_keys:
        for y_py_key in s_omega_py_keys:
            alt_add_results[(x_py_key, y_py_key)] = Symbol(f"res_{x_py_key}_{y_py_key}_min_w{OMEGA_VAL}", SMT_INT_TYPE)

    # --- Test 1: Weaken CCA3 (Classical Interior at 1+1=2) ---
    print("\n--- Test 1: Weaken CCA3 (res_11 not forced to 2), Assert CCA1, CCA2, CCA4, Commutativity ---")
    assertions_test1 = []
    # CCA1 (Totality)
    for x_py_key in s_omega_py_keys:
        for y_py_key in s_omega_py_keys:
            res_var = alt_add_results[(x_py_key, y_py_key)]
            assertions_test1.append(Or([Equals(res_var, smt_elem) for smt_elem in S_OMEGA_SMT_ELEMENTS]))
    # CCA2 (Two-Sided Identity U_SMT)
    u_py_key = U_SMT.constant_value()
    for x_py_key in s_omega_py_keys:
        x_smt_elem = Int(x_py_key)
        assertions_test1.append(Equals(alt_add_results[(u_py_key, x_py_key)], x_smt_elem))
        assertions_test1.append(Equals(alt_add_results[(x_py_key, u_py_key)], x_smt_elem))
    
    # Assert Commutativity for alt_add
    for i_idx in range(len(s_omega_py_keys)):
        for j_idx in range(i_idx + 1, len(s_omega_py_keys)):
            k1 = s_omega_py_keys[i_idx]
            k2 = s_omega_py_keys[j_idx]
            assertions_test1.append(Equals(alt_add_results[(k1,k2)], alt_add_results[(k2,k1)]))

    # CCA3 - WEAKENED for Omega=3: res_11 not forced to Int(2). Only constrained by Totality.
    
    # CCA4 - FULLY ASSERTED for Omega=3 DFI pairs:
    if 1 in py_dfi_elements and 2 in py_dfi_elements: 
        assertions_test1.append(Equals(alt_add_results[(1,2)], U_SMT)) 
        # res_21 = U_SMT is covered by commutativity assertion if res_12 = U_SMT
    if 2 in py_dfi_elements:
        assertions_test1.append(Equals(alt_add_results[(2,2)], U_SMT))

    differs_clauses_t1 = [NotEquals(alt_add_results[k], Int(v)) for k,v in STD_AVCA_TABLE_OMEGA3.items()]
    assertions_test1.append(Or(differs_clauses_t1))

    with Solver(name="z3") as s:
        for an_assertion in assertions_test1: s.add_assertion(an_assertion)
        result_t1 = s.solve()
        print(f"Test 1 Result (Weaken CCA3 for res_11): {'SAT (Differing table found - EXPECTED)' if result_t1 else 'UNSAT (Still unique - UNEXPECTED)'}")
        if result_t1:
            print("  Proof: Weakening CCA3 (1+1=2 rule for Ω=3) allows alternative commutative tables satisfying other CCAs.")
            model = s.get_model() # CORRECTED
            if model:
                print("  Alternative Model Found (res_11 might not be 2):")
                for x_k_model in s_omega_py_keys:
                    row = f"    {x_k_model} |"
                    for y_k_model in s_omega_py_keys:
                        val = model.get_value(alt_add_results[(x_k_model,y_k_model)])
                        row += f" {val.constant_value() if val else '?'}"
                    print(row)
            else: print("  Solver returned SAT but no model was available.")


    # --- Test 2: Weaken CCA4 (Overflow at 1+2=U) ---
    print("\n--- Test 2: Weaken CCA4 (res_12 not forced to U), Assert CCA1, CCA2, CCA3, Commutativity ---")
    alt_add_results_t2: Dict[Tuple[int, int], FNode] = {} 
    for x_py_key in s_omega_py_keys:
        for y_py_key in s_omega_py_keys:
            alt_add_results_t2[(x_py_key, y_py_key)] = Symbol(f"res_t2_{x_py_key}_{y_py_key}_min_w{OMEGA_VAL}", SMT_INT_TYPE)

    assertions_test2 = []
    # CCA1 (Totality)
    for x_py_key in s_omega_py_keys:
        for y_py_key in s_omega_py_keys:
            res_var = alt_add_results_t2[(x_py_key, y_py_key)]
            assertions_test2.append(Or([Equals(res_var, smt_elem) for smt_elem in S_OMEGA_SMT_ELEMENTS]))
    # CCA2 (Two-Sided Identity U_SMT)
    u_py_key = U_SMT.constant_value()
    for x_py_key in s_omega_py_keys:
        x_smt_elem = Int(x_py_key)
        assertions_test2.append(Equals(alt_add_results_t2[(u_py_key, x_py_key)], x_smt_elem))
        assertions_test2.append(Equals(alt_add_results_t2[(x_py_key, u_py_key)], x_smt_elem))

    # Assert Commutativity for alt_add_results_t2
    for i_idx in range(len(s_omega_py_keys)):
        for j_idx in range(i_idx + 1, len(s_omega_py_keys)):
            k1 = s_omega_py_keys[i_idx]
            k2 = s_omega_py_keys[j_idx]
            assertions_test2.append(Equals(alt_add_results_t2[(k1,k2)], alt_add_results_t2[(k2,k1)]))

    # CCA3 - FULLY ASSERTED for Omega=3:
    if 1 in py_dfi_elements: 
        assertions_test2.append(Equals(alt_add_results_t2[(1,1)], Int(2)))
    
    # CCA4 - WEAKENED for Omega=3 DFI pairs:
    # We *don't* assert res_12 = U (and by commutativity, res_21 = U).
    # We *do* assert other CCA4 cases: res_22 = U.
    if 2 in py_dfi_elements:
        assertions_test2.append(Equals(alt_add_results_t2[(2,2)], U_SMT))
    # res_12 (and res_21 by commutativity) only constrained by Totality.

    differs_clauses_t2 = [NotEquals(alt_add_results_t2[k], Int(v)) for k,v in STD_AVCA_TABLE_OMEGA3.items()]
    assertions_test2.append(Or(differs_clauses_t2))

    with Solver(name="z3") as s:
        for an_assertion in assertions_test2: s.add_assertion(an_assertion)
        result_t2 = s.solve()
        print(f"Test 2 Result (Weaken CCA4 for res_12): {'SAT (Differing table found - EXPECTED)' if result_t2 else 'UNSAT (Still unique - UNEXPECTED)'}")
        if result_t2:
            print("  Proof: Weakening CCA4 (1+2=U rule for Ω=3) allows alternative commutative tables satisfying other CCAs.")
            model = s.get_model() # CORRECTED
            if model:
                print("  Alternative Model Found (res_12 might not be U):")
                for x_k_model in s_omega_py_keys: 
                    row = f"    {x_k_model} |"
                    for y_k_model in s_omega_py_keys: 
                        val = model.get_value(alt_add_results_t2[(x_k_model,y_k_model)])
                        row += f" {val.constant_value() if val else '?'}"
                    print(row)
            else: print("  Solver returned SAT but no model was available.")

if __name__ == "__main__":
    run_axiom_minimality_tests()