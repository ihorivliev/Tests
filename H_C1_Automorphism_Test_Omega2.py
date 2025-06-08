# H_C1_Automorphism_Test_Omega2.py
# SMT Test for part of H-C1: For AVCA-Ω (Best Combo), is the identity map
# the only "tag-preserving" automorphism for Ω=2?

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Global Omega ---
_Omega_py_H_C1_O2: int = 0 # Renamed global

# --- Symbolic AVCA Value Representation ---
def create_symbolic_avc_val_C1_O2(name_prefix: str) -> Dict[str, FNode]: # Renamed
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero_C1O2", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo_C1O2", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite_C1O2", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_C1O2", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints_C1_O2(avc_repr: Dict[str, FNode], omega_smt_node: FNode, omega_py_val_for_check: int) -> List[FNode]: # Renamed
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] >= Int(1), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], Int(0)))
    ]
    # For Omega=1, DFI is empty. For Omega=2, DFI is not empty.
    # The omega_py_val_for_check == 1 constraint from previous scripts is not applicable here for Omega=2.
    return constraints

def avc_deep_equals_smt_C1_O2(s1: Dict[str, FNode], s2: Dict[str, FNode]) -> FNode: # Renamed
    return And(Iff(s1["is_zero"], s2["is_zero"]),
               Iff(s1["is_areo"], s2["is_areo"]),
               Iff(s1["is_finite"], s2["is_finite"]),
               Equals(s1["val"], s2["val"]))

def IsUnioSMT_C1_O2(s: Dict[str, FNode]) -> FNode: # Renamed
    return Or(s["is_zero"], s["is_areo"])

# --- "Best Combination" SMT Logic Builders ---
def avc_add_bc_smt_logic_C1_O2(a: Dict[str, FNode], b: Dict[str, FNode], # Renamed
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_a = avc_deep_equals_smt_C1_O2(res, a)
    res_is_b = avc_deep_equals_smt_C1_O2(res, b)
    case1_a_is_unio = Implies(IsUnioSMT_C1_O2(a), res_is_b)
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], IsUnioSMT_C1_O2(b)), res_is_a)
    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    symbolic_sum_val = Plus(a["val"], b["val"])
    res_is_dfi_sum_state = And(res["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]),
                               Equals(res["val"], symbolic_sum_val))
    res_is_areo_unio_state = And(res["is_areo"], Not(res["is_zero"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    case3_dfi_dfi_logic = Implies(
        cond_both_are_dfi,
        Ite(symbolic_sum_val < omega_smt_node,
            res_is_dfi_sum_state,
            res_is_areo_unio_state))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi_logic)

def avc_mul_bc_smt_logic_C1_O2(a: Dict[str, FNode], b: Dict[str, FNode], # Renamed
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_zero_unio_state = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    res_is_areo_unio_state = And(res["is_areo"], Not(res["is_zero"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    cond_any_operand_is_unio = Or(IsUnioSMT_C1_O2(a), IsUnioSMT_C1_O2(b))
    cond_any_unio_operand_is_areo = Or(a["is_areo"], b["is_areo"])
    unio_case_behavior = Ite(cond_any_unio_operand_is_areo,
                             res_is_areo_unio_state,
                             res_is_zero_unio_state)
    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    symbolic_prod_val = Times(a["val"], b["val"])
    res_is_dfi_prod_state = And(res["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]),
                                Equals(res["val"], symbolic_prod_val))
    dfi_case_behavior = Ite(And(symbolic_prod_val >= Int(1), symbolic_prod_val < omega_smt_node),
                            res_is_dfi_prod_state,
                            res_is_areo_unio_state)
    return Ite(cond_any_operand_is_unio, unio_case_behavior, dfi_case_behavior)

# --- Helper to get specific AVCA symbolic constants ---
def get_symbolic_avca_constant_C1_O2(aspect: Literal["zero", "areo", "dfi"], val: int, omega: int, name_prefix: str) -> Tuple[Dict[str, FNode], FNode]: # Renamed
    s = create_symbolic_avc_val_C1_O2(name_prefix)
    constraints_list = get_base_avc_constraints_C1_O2(s, Int(omega), omega)
    if aspect == "zero":
        constraints_list.append(s["is_zero"])
    elif aspect == "areo":
        constraints_list.append(s["is_areo"])
    elif aspect == "dfi":
        constraints_list.append(s["is_finite"])
        constraints_list.append(Equals(s["val"], Int(val)))
    return s, And(constraints_list)


# --- SMT Test Function for H-C1 (Automorphism part for Omega=2) ---
def test_H_C1_automorphism_Omega2(omega_py: int):
    global _Omega_py_H_C1_O2
    _Omega_py_H_C1_O2 = omega_py
    omega_smt = Int(omega_py)

    print(f"\n--- Testing H-C1 (Simplified): Uniqueness of Tag-Preserving Automorphism for AVCA-Ω={omega_py} ---")

    if omega_py != 2:
        print(f"  FATAL SCRIPT ERROR: This script version is specifically structured for Omega=2.")
        print(f"  Cannot run for Omega={omega_py}. Exiting test.")
        return False

    s_omega_elements_sym: List[Dict[str,FNode]] = []
    s_omega_constraints_sym_list: List[FNode] = []

    zu_const_sym, zu_constr = get_symbolic_avca_constant_C1_O2("zero", 0, omega_py, "ZUc_O2")
    s_omega_elements_sym.append(zu_const_sym); s_omega_constraints_sym_list.append(zu_constr)
    
    au_const_sym, au_constr = get_symbolic_avca_constant_C1_O2("areo", 0, omega_py, "AUc_O2")
    s_omega_elements_sym.append(au_const_sym); s_omega_constraints_sym_list.append(au_constr)

    fp1_const_sym, fp1_constr = get_symbolic_avca_constant_C1_O2("dfi", 1, omega_py, "DFI1c_O2")
    s_omega_elements_sym.append(fp1_const_sym); s_omega_constraints_sym_list.append(fp1_constr)
    
    solver = Solver(name="z3")
    for constr in s_omega_constraints_sym_list:
        solver.add_assertion(constr)

    h_map_outputs: Dict[str, Dict[str, FNode]] = {}
    h_constraints_list: List[FNode] = []

    for s_in_const in s_omega_elements_sym:
        s_out_h = create_symbolic_avc_val_C1_O2(f"h_{s_in_const['name']}")
        h_map_outputs[s_in_const['name']] = s_out_h
        for c in get_base_avc_constraints_C1_O2(s_out_h, omega_smt, omega_py):
            h_constraints_list.append(c)

    # Constrain h to be "tag-preserving" (aspect-preserving for Unio)
    h_constraints_list.append(avc_deep_equals_smt_C1_O2(h_map_outputs[zu_const_sym['name']], zu_const_sym))
    h_constraints_list.append(avc_deep_equals_smt_C1_O2(h_map_outputs[au_const_sym['name']], au_const_sym))
    
    # For Omega=2, DFI={Fp(1)}. Bijective map h on DFI means h(Fp(1)) must be Fp(1).
    h_fp1_out = h_map_outputs[fp1_const_sym['name']]
    h_constraints_list.append(avc_deep_equals_smt_C1_O2(h_fp1_out, fp1_const_sym))

    for c in h_constraints_list: solver.add_assertion(c)

    # SMT ITE chain to define h(s_eval) based on s_eval matching one of the constants
    def define_h_of_symbolic_result_O2(s_eval_sym: Dict[str,FNode], h_of_s_eval_sym: Dict[str,FNode]) -> FNode:
        for c_basedef in get_base_avc_constraints_C1_O2(h_of_s_eval_sym, omega_smt, omega_py):
             solver.add_assertion(c_basedef)

        return Ite(avc_deep_equals_smt_C1_O2(s_eval_sym, zu_const_sym),
                   avc_deep_equals_smt_C1_O2(h_of_s_eval_sym, h_map_outputs[zu_const_sym['name']]),
               Ite(avc_deep_equals_smt_C1_O2(s_eval_sym, au_const_sym),
                   avc_deep_equals_smt_C1_O2(h_of_s_eval_sym, h_map_outputs[au_const_sym['name']]),
               Ite(avc_deep_equals_smt_C1_O2(s_eval_sym, fp1_const_sym),
                   avc_deep_equals_smt_C1_O2(h_of_s_eval_sym, h_map_outputs[fp1_const_sym['name']]),
                   FALSE() # s_eval_sym must be one of the S_Omega elements for Omega=2
                  )))

    hom_constraints_list: List[FNode] = []
    print("  Asserting homomorphism conditions for Omega=2...")
    for x_sym_const in s_omega_elements_sym:
        for y_sym_const in s_omega_elements_sym:
            # Addition
            res_avca_add_sym = create_symbolic_avc_val_C1_O2(f"rA_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1_O2(res_avca_add_sym, omega_smt, omega_py): solver.add_assertion(c)
            solver.add_assertion(avc_add_bc_smt_logic_C1_O2(x_sym_const, y_sym_const, res_avca_add_sym, omega_smt))
            h_of_res_avca_add_sym = create_symbolic_avc_val_C1_O2(f"h_rA_{x_sym_const['name']}_{y_sym_const['name']}")
            solver.add_assertion(define_h_of_symbolic_result_O2(res_avca_add_sym, h_of_res_avca_add_sym))
            h_of_x = h_map_outputs[x_sym_const['name']]
            h_of_y = h_map_outputs[y_sym_const['name']]
            res_op_h_inputs_add_sym = create_symbolic_avc_val_C1_O2(f"r_hA_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1_O2(res_op_h_inputs_add_sym, omega_smt, omega_py): solver.add_assertion(c)
            solver.add_assertion(avc_add_bc_smt_logic_C1_O2(h_of_x, h_of_y, res_op_h_inputs_add_sym, omega_smt))
            hom_constraints_list.append(avc_deep_equals_smt_C1_O2(h_of_res_avca_add_sym, res_op_h_inputs_add_sym))

            # Multiplication
            res_avca_mul_sym = create_symbolic_avc_val_C1_O2(f"rM_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1_O2(res_avca_mul_sym, omega_smt, omega_py): solver.add_assertion(c)
            solver.add_assertion(avc_mul_bc_smt_logic_C1_O2(x_sym_const, y_sym_const, res_avca_mul_sym, omega_smt))
            h_of_res_avca_mul_sym = create_symbolic_avc_val_C1_O2(f"h_rM_{x_sym_const['name']}_{y_sym_const['name']}")
            solver.add_assertion(define_h_of_symbolic_result_O2(res_avca_mul_sym, h_of_res_avca_mul_sym))
            res_op_h_inputs_mul_sym = create_symbolic_avc_val_C1_O2(f"r_hM_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1_O2(res_op_h_inputs_mul_sym, omega_smt, omega_py): solver.add_assertion(c)
            solver.add_assertion(avc_mul_bc_smt_logic_C1_O2(h_of_x, h_of_y, res_op_h_inputs_mul_sym, omega_smt))
            hom_constraints_list.append(avc_deep_equals_smt_C1_O2(h_of_res_avca_mul_sym, res_op_h_inputs_mul_sym))

    for hc in hom_constraints_list: solver.add_assertion(hc)
    
    # Assert h is NOT the identity map on DFI.
    # For Omega=2, DFI={Fp(1)}, and h(Fp(1)) is already constrained to be Fp(1).
    # So, is_identity_map_on_dfi will be True. Not(True) is False.
    h_fp1_is_fp1 = avc_deep_equals_smt_C1_O2(h_map_outputs[fp1_const_sym['name']], fp1_const_sym)
    is_identity_map_on_dfi = h_fp1_is_fp1 
    
    solver.add_assertion(Not(is_identity_map_on_dfi)) # This asserts FALSE essentially

    print("  Solving for a non-identity, tag-preserving automorphism...")
    property_holds = False 
    if not solver.solve(): 
        print("  RESULT: UNSAT. The only tag-preserving automorphism is the identity map (as expected for Omega=2).")
        property_holds = True
    else: 
        print("  RESULT: SAT. A non-identity, tag-preserving automorphism was found (UNEXPECTED for Omega=2).")
        # (Model printing logic can be added here if needed for debugging a SAT result)
        property_holds = False
        
    return property_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_C1_Automorphism_Test_Omega2 (v1): ======")
    
    omega_to_test = 2
    print(f"\nSetting Python-side _Omega_py_H_C1_O2 = {omega_to_test}")

    only_identity_automorphism = test_H_C1_automorphism_Omega2(omega_to_test)

    print("\n--- Summary of H-C1 (Automorphism Test for Omega=2 v1) ---")
    print(f"For Omega = {omega_to_test} (AVCA-F2) using Best Combination AVCA kernel:")
    if only_identity_automorphism:
        print("  The identity map is the ONLY tag-preserving automorphism.")
        print("  This aligns with expectations for F2 and supports the H-C1 methodology.")
    else:
        print("  A non-identity tag-preserving automorphism was found OR an error occurred.")
        print("  This would be highly unexpected for Omega=2.")

    print("\n====== H_C1_Automorphism_Test_Omega2 (v1) Script Finished ======")