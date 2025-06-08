# H_C1_Automorphism_Test.py (v4)
# SMT Test for part of H-C1: For AVCA-Ω (Best Combo), is the identity map
# the only "tag-preserving" automorphism for Ω=3?
# "Tag-preserving" here means:
#   - ZU_obj maps to ZU_obj (aspect preserved for Unio).
#   - AU_obj maps to AU_obj (aspect preserved for Unio).
#   - The set of DFI elements maps bijectively to the set of DFI elements.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Global Omega ---
_Omega_py_H_C1: int = 0

# --- Symbolic AVCA Value Representation ---
def create_symbolic_avc_val_C1(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero_C1", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo_C1", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite_C1", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_C1", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints_C1(avc_repr: Dict[str, FNode], omega_smt_node: FNode, omega_py_val_for_check: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] >= Int(1), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], Int(0)))
    ]
    if omega_py_val_for_check > 0 and omega_py_val_for_check == 1 :
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_deep_equals_smt_C1(s1: Dict[str, FNode], s2: Dict[str, FNode]) -> FNode:
    return And(Iff(s1["is_zero"], s2["is_zero"]),
               Iff(s1["is_areo"], s2["is_areo"]),
               Iff(s1["is_finite"], s2["is_finite"]),
               Equals(s1["val"], s2["val"]))

def IsUnioSMT_C1(s: Dict[str, FNode]) -> FNode:
    return Or(s["is_zero"], s["is_areo"])

# --- "Best Combination" SMT Logic Builders ---
def avc_add_bc_smt_logic_C1(a: Dict[str, FNode], b: Dict[str, FNode],
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_a = avc_deep_equals_smt_C1(res, a)
    res_is_b = avc_deep_equals_smt_C1(res, b)
    case1_a_is_unio = Implies(IsUnioSMT_C1(a), res_is_b)
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], IsUnioSMT_C1(b)), res_is_a)
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

def avc_mul_bc_smt_logic_C1(a: Dict[str, FNode], b: Dict[str, FNode],
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_zero_unio_state = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    res_is_areo_unio_state = And(res["is_areo"], Not(res["is_zero"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    cond_any_operand_is_unio = Or(IsUnioSMT_C1(a), IsUnioSMT_C1(b))
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
def get_symbolic_avca_constant_C1(aspect: Literal["zero", "areo", "dfi"], val: int, omega: int, name_prefix: str) -> Tuple[Dict[str, FNode], FNode]:
    s = create_symbolic_avc_val_C1(name_prefix)
    constraints_list = get_base_avc_constraints_C1(s, Int(omega), omega)
    if aspect == "zero":
        constraints_list.append(s["is_zero"])
    elif aspect == "areo":
        constraints_list.append(s["is_areo"])
    elif aspect == "dfi":
        constraints_list.append(s["is_finite"])
        constraints_list.append(Equals(s["val"], Int(val)))
    return s, And(constraints_list)


# --- SMT Test Function for H-C1 (Automorphism part) ---
def test_H_C1_automorphism(omega_py: int):
    global _Omega_py_H_C1
    _Omega_py_H_C1 = omega_py
    omega_smt = Int(omega_py)

    print(f"\n--- Testing H-C1 (Simplified): Uniqueness of Tag-Preserving Automorphism for AVCA-Ω={omega_py} ---")

    if omega_py != 3:
        print(f"  FATAL SCRIPT ERROR: This script version is hardcoded for Omega=3 for explicit element iteration and h definition.")
        print(f"  Cannot run for Omega={omega_py}. Exiting test.")
        return False

    s_omega_elements_sym: List[Dict[str,FNode]] = []
    s_omega_constraints_sym_list: List[FNode] = [] # Corrected: removed extra ']'

    zu_const_sym, zu_constr = get_symbolic_avca_constant_C1("zero", 0, omega_py, "ZUc")
    s_omega_elements_sym.append(zu_const_sym); s_omega_constraints_sym_list.append(zu_constr)

    au_const_sym, au_constr = get_symbolic_avca_constant_C1("areo", 0, omega_py, "AUc")
    s_omega_elements_sym.append(au_const_sym); s_omega_constraints_sym_list.append(au_constr)

    fp1_const_sym, fp1_constr = get_symbolic_avca_constant_C1("dfi", 1, omega_py, "DFI1c")
    s_omega_elements_sym.append(fp1_const_sym); s_omega_constraints_sym_list.append(fp1_constr)

    fp2_const_sym, fp2_constr = get_symbolic_avca_constant_C1("dfi", 2, omega_py, "DFI2c")
    s_omega_elements_sym.append(fp2_const_sym); s_omega_constraints_sym_list.append(fp2_constr)

    solver = Solver(name="z3")
    for constr in s_omega_constraints_sym_list:
        solver.add_assertion(constr)

    h_map_outputs: Dict[str, Dict[str, FNode]] = {}
    h_constraints_list: List[FNode] = []

    for s_in_const in s_omega_elements_sym:
        s_out_h = create_symbolic_avc_val_C1(f"h_{s_in_const['name']}")
        h_map_outputs[s_in_const['name']] = s_out_h
        for c in get_base_avc_constraints_C1(s_out_h, omega_smt, omega_py):
            h_constraints_list.append(c)

    h_constraints_list.append(avc_deep_equals_smt_C1(h_map_outputs[zu_const_sym['name']], zu_const_sym))
    h_constraints_list.append(avc_deep_equals_smt_C1(h_map_outputs[au_const_sym['name']], au_const_sym))

    h_fp1_out = h_map_outputs[fp1_const_sym['name']]
    h_fp2_out = h_map_outputs[fp2_const_sym['name']]

    h_constraints_list.append(h_fp1_out['is_finite'])
    h_constraints_list.append(Or(Equals(h_fp1_out['val'], Int(1)), Equals(h_fp1_out['val'], Int(2))))
    h_constraints_list.append(h_fp2_out['is_finite'])
    h_constraints_list.append(Or(Equals(h_fp2_out['val'], Int(1)), Equals(h_fp2_out['val'], Int(2))))
    h_constraints_list.append(Not(Equals(h_fp1_out['val'], h_fp2_out['val'])))

    for c in h_constraints_list: solver.add_assertion(c)

    hom_constraints_list: List[FNode] = []
    for x_sym_const in s_omega_elements_sym:
        for y_sym_const in s_omega_elements_sym:
            # --- Addition Homomorphism ---
            res_avca_add_sym = create_symbolic_avc_val_C1(f"res_add_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1(res_avca_add_sym, omega_smt, omega_py): solver.add_assertion(c)
            solver.add_assertion(avc_add_bc_smt_logic_C1(x_sym_const, y_sym_const, res_avca_add_sym, omega_smt))

            h_of_res_avca_add_sym = create_symbolic_avc_val_C1(f"h_res_add_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1(h_of_res_avca_add_sym, omega_smt, omega_py): solver.add_assertion(c)

            def_h_of_res_add = Ite(avc_deep_equals_smt_C1(res_avca_add_sym, zu_const_sym),
                                   avc_deep_equals_smt_C1(h_of_res_avca_add_sym, h_map_outputs[zu_const_sym['name']]),
                               Ite(avc_deep_equals_smt_C1(res_avca_add_sym, au_const_sym),
                                   avc_deep_equals_smt_C1(h_of_res_avca_add_sym, h_map_outputs[au_const_sym['name']]),
                               Ite(avc_deep_equals_smt_C1(res_avca_add_sym, fp1_const_sym),
                                   avc_deep_equals_smt_C1(h_of_res_avca_add_sym, h_map_outputs[fp1_const_sym['name']]),
                               Ite(avc_deep_equals_smt_C1(res_avca_add_sym, fp2_const_sym),
                                   avc_deep_equals_smt_C1(h_of_res_avca_add_sym, h_map_outputs[fp2_const_sym['name']]),
                                   FALSE() 
                                  ))))
            solver.add_assertion(def_h_of_res_add)

            h_of_x = h_map_outputs[x_sym_const['name']]
            h_of_y = h_map_outputs[y_sym_const['name']]
            res_op_h_inputs_add_sym = create_symbolic_avc_val_C1(f"res_hoph_add_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1(res_op_h_inputs_add_sym, omega_smt, omega_py): solver.add_assertion(c)
            solver.add_assertion(avc_add_bc_smt_logic_C1(h_of_x, h_of_y, res_op_h_inputs_add_sym, omega_smt))
            hom_constraints_list.append(avc_deep_equals_smt_C1(h_of_res_avca_add_sym, res_op_h_inputs_add_sym))

            # --- Multiplication Homomorphism ---
            res_avca_mul_sym = create_symbolic_avc_val_C1(f"res_mul_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1(res_avca_mul_sym, omega_smt, omega_py): solver.add_assertion(c)
            solver.add_assertion(avc_mul_bc_smt_logic_C1(x_sym_const, y_sym_const, res_avca_mul_sym, omega_smt))

            h_of_res_avca_mul_sym = create_symbolic_avc_val_C1(f"h_res_mul_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1(h_of_res_avca_mul_sym, omega_smt, omega_py): solver.add_assertion(c)

            def_h_of_res_mul = Ite(avc_deep_equals_smt_C1(res_avca_mul_sym, zu_const_sym),
                                   avc_deep_equals_smt_C1(h_of_res_avca_mul_sym, h_map_outputs[zu_const_sym['name']]),
                               Ite(avc_deep_equals_smt_C1(res_avca_mul_sym, au_const_sym),
                                   avc_deep_equals_smt_C1(h_of_res_avca_mul_sym, h_map_outputs[au_const_sym['name']]),
                               Ite(avc_deep_equals_smt_C1(res_avca_mul_sym, fp1_const_sym),
                                   avc_deep_equals_smt_C1(h_of_res_avca_mul_sym, h_map_outputs[fp1_const_sym['name']]),
                               Ite(avc_deep_equals_smt_C1(res_avca_mul_sym, fp2_const_sym),
                                   avc_deep_equals_smt_C1(h_of_res_avca_mul_sym, h_map_outputs[fp2_const_sym['name']]),
                                   FALSE()
                                  ))))
            solver.add_assertion(def_h_of_res_mul)

            res_op_h_inputs_mul_sym = create_symbolic_avc_val_C1(f"res_hoph_mul_{x_sym_const['name']}_{y_sym_const['name']}")
            for c in get_base_avc_constraints_C1(res_op_h_inputs_mul_sym, omega_smt, omega_py): solver.add_assertion(c)
            solver.add_assertion(avc_mul_bc_smt_logic_C1(h_of_x, h_of_y, res_op_h_inputs_mul_sym, omega_smt))
            hom_constraints_list.append(avc_deep_equals_smt_C1(h_of_res_avca_mul_sym, res_op_h_inputs_mul_sym))

    for hc in hom_constraints_list: solver.add_assertion(hc)

    h_fp1_is_fp1 = avc_deep_equals_smt_C1(h_map_outputs[fp1_const_sym['name']], fp1_const_sym)
    h_fp2_is_fp2 = avc_deep_equals_smt_C1(h_map_outputs[fp2_const_sym['name']], fp2_const_sym)
    is_identity_map_on_dfi = And(h_fp1_is_fp1, h_fp2_is_fp2)

    solver.add_assertion(Not(is_identity_map_on_dfi))

    print("  Solving for a non-identity, tag-preserving automorphism...")
    property_holds = False
    if not solver.solve():
        print("  RESULT: UNSAT. The only tag-preserving automorphism is the identity map.")
        property_holds = True
    else:
        print("  RESULT: SAT. A non-identity, tag-preserving automorphism was found:")
        model = solver.get_model()
        def pval_c1(s_sym_dict_val, name_s_val):
            aspect = "A" if model.get_value(s_sym_dict_val["is_areo"]).is_true() else \
                     "Z" if model.get_value(s_sym_dict_val["is_zero"]).is_true() else "F"
            val = model.get_value(s_sym_dict_val["val"])
            return f"{name_s_val}: Aspect={aspect}, Val={val}"

        print("    Map h:")
        for s_in_const_map in s_omega_elements_sym:
            h_s_in = h_map_outputs[s_in_const_map['name']]
            s_in_aspect = "A" if model.get_value(s_in_const_map["is_areo"]).is_true() else \
                          "Z" if model.get_value(s_in_const_map["is_zero"]).is_true() else "F"
            s_in_val = model.get_value(s_in_const_map["val"])
            s_in_print_name = f"{s_in_const_map['name']}(Aspect={s_in_aspect},Val={s_in_val})" # Modified print
            print(f"      h({s_in_print_name}) -> {pval_c1(h_s_in, h_s_in['name'])}")
        property_holds = False

    return property_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_C1_Automorphism_Test (v4): ======")

    omega_to_test = 3
    print(f"\nSetting Python-side _Omega_py_H_C1 = {omega_to_test}")

    only_identity_automorphism = test_H_C1_automorphism(omega_to_test)

    print("\n--- Summary of H-C1 (Simplified Automorphism Test v4) ---")
    print(f"For Omega = {omega_to_test} using Best Combination AVCA kernel:")
    if only_identity_automorphism:
        print("  The identity map is the ONLY tag-preserving (aspect-preserving Unio, DFI-permuting) automorphism.")
        print("  This is a necessary condition for AVCA-Ω to be an initial object if other 'collapse rings' are isomorphic to AVCA-Ω.")
    else:
        print("  A non-identity tag-preserving automorphism exists OR an error/timeout occurred OR test setup issue.")
        print("  This would challenge H-C1's claim of a *unique* map if other algebras are just AVCA itself (and are automorphic).")

    print("\n====== H_C1_Automorphism_Test (v4) Script Finished ======")