# H_O1_Lattice_Test.py
# SMT Test for Hypothesis H-O1: AVCA-Ω carries a canonical complete lattice order
# where ⊗ is meet and ⊕ is join, using the "Best Combination" kernel.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite, # Added Ite
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Global Omega for AVCA operations (Python side for setup) ---
_Omega_py_H_O1: int = 0

# --- Symbolic AVCA Value Representation (from Appendix B / GIT.2b) ---
def create_symbolic_avc_val(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], omega_smt_node: FNode, omega_py_val_for_check: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] >= Int(1), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], Int(0)))
    ]
    if omega_py_val_for_check == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_deep_equals_smt(s1: Dict[str, FNode], s2: Dict[str, FNode]) -> FNode:
    """Checks if two symbolic AVCA values are identical, including aspect for Unio."""
    return And(Iff(s1["is_zero"], s2["is_zero"]),
               Iff(s1["is_areo"], s2["is_areo"]),
               Iff(s1["is_finite"], s2["is_finite"]),
               Equals(s1["val"], s2["val"]))

def IsUnioSMT(s: Dict[str, FNode]) -> FNode:
    return Or(s["is_zero"], s["is_areo"])

# --- "Best Combination" SMT Logic Builders ---
def avc_add_bc_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                         res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_a = avc_deep_equals_smt(res, a)
    res_is_b = avc_deep_equals_smt(res, b)

    case1_a_is_unio = Implies(IsUnioSMT(a), res_is_b)
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], IsUnioSMT(b)), res_is_a)

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

def avc_mul_bc_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                         res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_zero_unio_state = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    res_is_areo_unio_state = And(res["is_areo"], Not(res["is_zero"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))

    cond_any_operand_is_unio = Or(IsUnioSMT(a), IsUnioSMT(b))
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


# --- H-O1 Candidate Order Definition ---
def is_le_H_O1_smt(s1: Dict[str, FNode], s2: Dict[str, FNode]) -> FNode:
    """
    SMT predicate for s1 <= s2 based on H-O1 interpretation:
    DFI_i < DFI_j if val_i < val_j.
    Any DFI < ZU.
    Any DFI < AU.
    ZU < AU.
    Elements are <= themselves (reflexivity).
    """
    cond_refl = avc_deep_equals_smt(s1, s2)

    cond_s1dfi_s2dfi_le = And(s1["is_finite"], s2["is_finite"], s1["val"] <= s2["val"]) # Corrected to <= for DFI comparison

    cond_s1dfi_s2zu = And(s1["is_finite"], s2["is_zero"])
    cond_s1dfi_s2au = And(s1["is_finite"], s2["is_areo"])

    cond_s1zu_s2au = And(s1["is_zero"], s2["is_areo"])

    return Or(cond_refl,
              cond_s1dfi_s2dfi_le,
              cond_s1dfi_s2zu,
              cond_s1dfi_s2au,
              cond_s1zu_s2au)

# --- SMT Test Functions for Lattice Properties ---
def common_setup_lattice_test(omega_py: int, num_vars: int = 2) -> Tuple[Solver, FNode, List[Dict[str, FNode]]]:
    global _Omega_py_H_O1
    _Omega_py_H_O1 = omega_py
    omega_smt = Int(omega_py)

    solver = Solver(name="z3")

    elements = []
    base_constraints_all = []
    if num_vars >= 1:
        x = create_symbolic_avc_val("x_lat")
        elements.append(x)
        base_constraints_all.extend(get_base_avc_constraints(x, omega_smt, omega_py))
    if num_vars >= 2:
        y = create_symbolic_avc_val("y_lat")
        elements.append(y)
        base_constraints_all.extend(get_base_avc_constraints(y, omega_smt, omega_py))
    if num_vars >= 3:
        z = create_symbolic_avc_val("z_lat")
        elements.append(z)
        base_constraints_all.extend(get_base_avc_constraints(z, omega_smt, omega_py))

    for constraint in base_constraints_all:
        solver.add_assertion(constraint)

    return solver, omega_smt, elements

def test_mul_is_meet(omega_py: int):
    print(f"\n--- Testing H-O1: avc_mul_bc_smt is Meet (GLB) for Omega={omega_py} ---")
    solver, omega_smt, elements_list = common_setup_lattice_test(omega_py, num_vars=3)
    x, y, z = elements_list[0], elements_list[1], elements_list[2]

    op_res_xy = create_symbolic_avc_val("res_mul_xy")
    for c_constraint in get_base_avc_constraints(op_res_xy, omega_smt, omega_py): solver.add_assertion(c_constraint) # Renamed c
    solver.add_assertion(avc_mul_bc_smt_logic(x, y, op_res_xy, omega_smt))

    prop1 = is_le_H_O1_smt(op_res_xy, x)
    prop2 = is_le_H_O1_smt(op_res_xy, y)
    prop3_premise = And(is_le_H_O1_smt(z, x), is_le_H_O1_smt(z, y))
    prop3_consequent = is_le_H_O1_smt(z, op_res_xy)
    prop3 = Implies(prop3_premise, prop3_consequent)

    full_property_meet = And(prop1, prop2, prop3)

    property_holds = False
    solver.push()
    solver.add_assertion(Not(full_property_meet))
    if not solver.solve():
        property_holds = True
        print("  RESULT: avc_mul_bc_smt IS meet. (No counterexample found for this Omega).")
    else:
        print("  RESULT: avc_mul_bc_smt is NOT meet. Counterexample found by SMT.")
        model = solver.get_model()
        print(f"    x: F={model.get_value(x['is_finite'])}, Z={model.get_value(x['is_zero'])}, A={model.get_value(x['is_areo'])}, val={model.get_value(x['val'])}")
        print(f"    y: F={model.get_value(y['is_finite'])}, Z={model.get_value(y['is_zero'])}, A={model.get_value(y['is_areo'])}, val={model.get_value(y['val'])}")
        print(f"    z: F={model.get_value(z['is_finite'])}, Z={model.get_value(z['is_zero'])}, A={model.get_value(z['is_areo'])}, val={model.get_value(z['val'])}")
        print(f"    x*y: F={model.get_value(op_res_xy['is_finite'])}, Z={model.get_value(op_res_xy['is_zero'])}, A={model.get_value(op_res_xy['is_areo'])}, val={model.get_value(op_res_xy['val'])}")

        val_prop1 = model.get_value(prop1)
        val_prop2 = model.get_value(prop2)

        if not val_prop1.is_true(): print("    Failed: x*y <= x")
        if not val_prop2.is_true(): print("    Failed: x*y <= y")
        if model.get_value(prop3_premise).is_true() and not model.get_value(prop3_consequent).is_true():
             print("    Failed: (z<=x ^ z<=y) => z <= x*y")
    solver.pop()
    return property_holds


def test_add_is_join(omega_py: int):
    print(f"\n--- Testing H-O1: avc_add_bc_smt is Join (LUB) for Omega={omega_py} ---")
    solver, omega_smt, elements_list = common_setup_lattice_test(omega_py, num_vars=3)
    x, y, z = elements_list[0], elements_list[1], elements_list[2]

    op_res_xy = create_symbolic_avc_val("res_add_xy")
    for c_constraint in get_base_avc_constraints(op_res_xy, omega_smt, omega_py): solver.add_assertion(c_constraint) # Renamed c
    solver.add_assertion(avc_add_bc_smt_logic(x, y, op_res_xy, omega_smt))

    prop1 = is_le_H_O1_smt(x, op_res_xy)
    prop2 = is_le_H_O1_smt(y, op_res_xy)
    prop3_premise = And(is_le_H_O1_smt(x, z), is_le_H_O1_smt(y, z))
    prop3_consequent = is_le_H_O1_smt(op_res_xy, z)
    prop3 = Implies(prop3_premise, prop3_consequent)

    full_property_join = And(prop1, prop2, prop3)

    property_holds = False
    solver.push()
    solver.add_assertion(Not(full_property_join))
    if not solver.solve():
        property_holds = True
        print("  RESULT: avc_add_bc_smt IS join. (No counterexample found for this Omega).")
    else:
        print("  RESULT: avc_add_bc_smt is NOT join. Counterexample found by SMT.")
        model = solver.get_model()
        print(f"    x: F={model.get_value(x['is_finite'])}, Z={model.get_value(x['is_zero'])}, A={model.get_value(x['is_areo'])}, val={model.get_value(x['val'])}")
        print(f"    y: F={model.get_value(y['is_finite'])}, Z={model.get_value(y['is_zero'])}, A={model.get_value(y['is_areo'])}, val={model.get_value(y['val'])}")
        print(f"    z: F={model.get_value(z['is_finite'])}, Z={model.get_value(z['is_zero'])}, A={model.get_value(z['is_areo'])}, val={model.get_value(z['val'])}")
        print(f"    x+y: F={model.get_value(op_res_xy['is_finite'])}, Z={model.get_value(op_res_xy['is_zero'])}, A={model.get_value(op_res_xy['is_areo'])}, val={model.get_value(op_res_xy['val'])}")

        val_prop1 = model.get_value(prop1)
        val_prop2 = model.get_value(prop2)

        if not val_prop1.is_true(): print("    Failed: x <= x+y")
        if not val_prop2.is_true(): print("    Failed: y <= x+y")
        if model.get_value(prop3_premise).is_true() and not model.get_value(prop3_consequent).is_true():
             print("    Failed: (x<=z ^ y<=z) => x+y <= z")
    solver.pop()
    return property_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_O1_Lattice_Test: Testing Lattice Properties for AVCA-Ω ======")
    print("Order Relation (is_le_H_O1_smt): DFI_i < DFI_j if val_i < val_j; Any DFI < ZU; Any DFI < AU; ZU < AU.")
    print("AVCA Operations: Best Combination (add_v1.1, mul_v1.2)")
    print("Unio SMT val convention: ZU val=0,is_zero=T; AU val=0,is_areo=T.") # Corrected print

    omega_to_test = 3
    print(f"\nSetting Python-side Omega_py_H_O1 = {omega_to_test} for base constraints context.")

    mul_is_meet_result = test_mul_is_meet(omega_to_test)
    add_is_join_result = test_add_is_join(omega_to_test)

    print("\n--- Summary of H-O1 Test ---")
    print(f"For Omega = {omega_to_test} with the defined order (DFIs < ZU_obj < AU_obj):")
    print(f"  Is avc_mul_bc_smt a meet operation? {'Yes' if mul_is_meet_result else 'No'}")
    print(f"  Is avc_add_bc_smt a join operation?  {'Yes' if add_is_join_result else 'No'}")

    if mul_is_meet_result and add_is_join_result:
        print("\nConclusion: For this Omega and the interpreted order, AVCA ops appear to be meet/join.")
        print("This provides PARTIAL support for H-O1. Further analysis of the order and 'completeness' needed.")
    else:
        print("\nConclusion: For this Omega and the interpreted order, AVCA ops DO NOT fully satisfy meet/join properties.")
        print("This suggests either the order definition for H-O1 needs refinement/clarification,")
        print("or the hypothesis that these specific AVCA ops are meet/join under this order is falsified for this Omega.")

    print("\n====== H_O1_Lattice_Test Script Finished ======")