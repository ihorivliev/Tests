# H_O1_Lattice_Test_V2.py
# SMT Test for Hypothesis H-O1, revised approach.
# Order: Algebraic Unio (U_alg) is bottom (⊥), DFI elements ordered by magnitude.
# AVCA Operations: "Best Combination" kernel (aspect-aware for results).
# Comparison for order relation uses algebraic values.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Global Omega for AVCA operations (Python side for setup) ---
_Omega_py_H_O1_V2: int = 0

# --- Symbolic AVCA Value Representation (full structure with aspects) ---
def create_symbolic_avc_val_V2(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero_v2", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo_v2", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite_v2", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_v2", SMT_INT_TYPE), # DFI value, or 0 for Unio convention
        "name": name_prefix
    }

def get_base_avc_constraints_V2(avc_repr: Dict[str, FNode], omega_smt_node: FNode, omega_py_val_for_check: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] >= Int(1), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], Int(0))) # Both aspects map to algebraic Unio value 0
    ]
    if omega_py_val_for_check == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_deep_equals_smt_V2(s1: Dict[str, FNode], s2: Dict[str, FNode]) -> FNode:
    """Checks if two symbolic AVCA values are identical, including aspect for Unio."""
    return And(Iff(s1["is_zero"], s2["is_zero"]),
               Iff(s1["is_areo"], s2["is_areo"]),
               Iff(s1["is_finite"], s2["is_finite"]),
               Equals(s1["val"], s2["val"])) # val equality here means DFI val, or both Unio val=0

def IsUnioSMT_V2(s: Dict[str, FNode]) -> FNode:
    return Or(s["is_zero"], s["is_areo"])

# --- "Best Combination" SMT Logic Builders (output full symbolic structure) ---
def avc_add_bc_smt_logic_V2(a: Dict[str, FNode], b: Dict[str, FNode],
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_a = avc_deep_equals_smt_V2(res, a)
    res_is_b = avc_deep_equals_smt_V2(res, b)

    case1_a_is_unio = Implies(IsUnioSMT_V2(a), res_is_b)
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], IsUnioSMT_V2(b)), res_is_a)

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

def avc_mul_bc_smt_logic_V2(a: Dict[str, FNode], b: Dict[str, FNode],
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_zero_unio_state = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    res_is_areo_unio_state = And(res["is_areo"], Not(res["is_zero"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))

    cond_any_operand_is_unio = Or(IsUnioSMT_V2(a), IsUnioSMT_V2(b))
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

# --- Algebraic Order Definition (U_alg is bottom) ---
def get_algebraic_smt_val(s_sym: Dict[str, FNode]) -> FNode:
    """Converts a full symbolic AVCA structure to its algebraic SMT integer value."""
    return Ite(IsUnioSMT_V2(s_sym), Int(0), s_sym["val"])

def is_le_algebraic_smt(s1_sym: Dict[str, FNode], s2_sym: Dict[str, FNode]) -> FNode:
    """
    SMT predicate for s1 <= s2 based on algebraic values:
    U_alg (0) is bottom. DFI_k are ordered by their integer values.
    """
    v1_alg = get_algebraic_smt_val(s1_sym)
    v2_alg = get_algebraic_smt_val(s2_sym)

    # True if v1_alg = v2_alg
    # OR if v1_alg = 0 (U_alg is bottom, so 0 <= anything)
    # OR if (v1_alg != 0 AND v2_alg != 0 AND v1_alg <= v2_alg) (both DFI, compare magnitudes)
    return Or(
        Equals(v1_alg, v2_alg),
        Equals(v1_alg, Int(0)), # U_alg <= y is always true
        And(v1_alg > Int(0), v2_alg > Int(0), v1_alg <= v2_alg) # Both DFI, v1_val <= v2_val
    )

# --- SMT Test Functions for Lattice Properties ---
def common_setup_lattice_test_V2(omega_py: int, num_vars: int = 2) -> Tuple[Solver, FNode, List[Dict[str, FNode]]]:
    global _Omega_py_H_O1_V2
    _Omega_py_H_O1_V2 = omega_py
    omega_smt = Int(omega_py)
    solver = Solver(name="z3")
    elements = []
    base_constraints_all = []
    var_names = ["x_lat_v2", "y_lat_v2", "z_lat_v2"]
    for i in range(num_vars):
        elem = create_symbolic_avc_val_V2(var_names[i])
        elements.append(elem)
        base_constraints_all.extend(get_base_avc_constraints_V2(elem, omega_smt, omega_py))
    for constraint in base_constraints_all:
        solver.add_assertion(constraint)
    return solver, omega_smt, elements

def test_op_is_meet_V2(op_logic_func: Callable, op_name: str, omega_py: int):
    print(f"\n--- Testing H-O1 (Algebraic Order): {op_name} is Meet (GLB) for Omega={omega_py} ---")
    solver, omega_smt, elements_list = common_setup_lattice_test_V2(omega_py, num_vars=3)
    x, y, z = elements_list[0], elements_list[1], elements_list[2]

    op_res_xy = create_symbolic_avc_val_V2(f"res_{op_name}_xy")
    for c in get_base_avc_constraints_V2(op_res_xy, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(op_logic_func(x, y, op_res_xy, omega_smt))

    prop1 = is_le_algebraic_smt(op_res_xy, x)
    prop2 = is_le_algebraic_smt(op_res_xy, y)
    prop3_premise = And(is_le_algebraic_smt(z, x), is_le_algebraic_smt(z, y))
    prop3_consequent = is_le_algebraic_smt(z, op_res_xy)
    prop3 = Implies(prop3_premise, prop3_consequent)
    full_property_meet = And(prop1, prop2, prop3)

    property_holds = False
    solver.push()
    solver.add_assertion(Not(full_property_meet))
    if not solver.solve():
        property_holds = True
        print(f"  RESULT: {op_name} IS meet. (No counterexample found).")
    else:
        print(f"  RESULT: {op_name} is NOT meet. Counterexample found:")
        model = solver.get_model()
        # Helper to print symbolic AVCA value
        def pval(s_sym):
            aspect = "Z" if model.get_value(s_sym["is_zero"]).is_true() else \
                     "A" if model.get_value(s_sym["is_areo"]).is_true() else "F"
            val = model.get_value(s_sym["val"])
            alg_val = 0 if aspect != "F" else val
            return f"{s_sym['name']}: Aspect={aspect}, DFIVal={val}, AlgVal={alg_val}"
        print(f"    {pval(x)}")
        print(f"    {pval(y)}")
        print(f"    {pval(z)}")
        print(f"    {op_name}(x,y): {pval(op_res_xy)}")
        if not model.get_value(prop1).is_true(): print(f"    Failed: {op_name}(x,y) <= x")
        if not model.get_value(prop2).is_true(): print(f"    Failed: {op_name}(x,y) <= y")
        if model.get_value(prop3_premise).is_true() and \
           not model.get_value(prop3_consequent).is_true():
            print(f"    Failed: (z<=x ^ z<=y) => z <= {op_name}(x,y)")
    solver.pop()
    return property_holds

def test_op_is_join_V2(op_logic_func: Callable, op_name: str, omega_py: int):
    print(f"\n--- Testing H-O1 (Algebraic Order): {op_name} is Join (LUB) for Omega={omega_py} ---")
    solver, omega_smt, elements_list = common_setup_lattice_test_V2(omega_py, num_vars=3)
    x, y, z = elements_list[0], elements_list[1], elements_list[2]

    op_res_xy = create_symbolic_avc_val_V2(f"res_{op_name}_xy")
    for c in get_base_avc_constraints_V2(op_res_xy, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(op_logic_func(x, y, op_res_xy, omega_smt))

    prop1 = is_le_algebraic_smt(x, op_res_xy)
    prop2 = is_le_algebraic_smt(y, op_res_xy)
    prop3_premise = And(is_le_algebraic_smt(x, z), is_le_algebraic_smt(y, z))
    prop3_consequent = is_le_algebraic_smt(op_res_xy, z)
    prop3 = Implies(prop3_premise, prop3_consequent)
    full_property_join = And(prop1, prop2, prop3)

    property_holds = False
    solver.push()
    solver.add_assertion(Not(full_property_join))
    if not solver.solve():
        property_holds = True
        print(f"  RESULT: {op_name} IS join. (No counterexample found).")
    else:
        print(f"  RESULT: {op_name} is NOT join. Counterexample found:")
        model = solver.get_model()
        def pval(s_sym): # Identical pval helper as above
            aspect = "Z" if model.get_value(s_sym["is_zero"]).is_true() else \
                     "A" if model.get_value(s_sym["is_areo"]).is_true() else "F"
            val = model.get_value(s_sym["val"])
            alg_val = 0 if aspect != "F" else val
            return f"{s_sym['name']}: Aspect={aspect}, DFIVal={val}, AlgVal={alg_val}"
        print(f"    {pval(x)}")
        print(f"    {pval(y)}")
        print(f"    {pval(z)}")
        print(f"    {op_name}(x,y): {pval(op_res_xy)}")
        if not model.get_value(prop1).is_true(): print(f"    Failed: x <= {op_name}(x,y)")
        if not model.get_value(prop2).is_true(): print(f"    Failed: y <= {op_name}(x,y)")
        if model.get_value(prop3_premise).is_true() and \
           not model.get_value(prop3_consequent).is_true():
            print(f"    Failed: (x<=z ^ y<=z) => {op_name}(x,y) <= z")
    solver.pop()
    return property_holds

def test_distributivity_V2(omega_py: int, mul_is_meet: bool, add_is_join: bool):
    if not (mul_is_meet and add_is_join):
        print(f"\n--- Skipping Distributivity Tests for Omega={omega_py} as ops are not both meet/join ---")
        return

    print(f"\n--- Testing H-O1 (Algebraic Order): Distributivity for Omega={omega_py} ---")
    solver, omega_smt, elements_list = common_setup_lattice_test_V2(omega_py, num_vars=3)
    x, y, z = elements_list[0], elements_list[1], elements_list[2]

    # Test x ⊗ (y ⊕ z) == (x ⊗ y) ⊕ (x ⊗ z) using deep symbolic equality
    # LHS: x ⊗ (y ⊕ z)
    y_add_z = create_symbolic_avc_val_V2("y_add_z")
    for c in get_base_avc_constraints_V2(y_add_z, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_add_bc_smt_logic_V2(y, z, y_add_z, omega_smt))
    lhs = create_symbolic_avc_val_V2("lhs_dist1")
    for c in get_base_avc_constraints_V2(lhs, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_mul_bc_smt_logic_V2(x, y_add_z, lhs, omega_smt))

    # RHS: (x ⊗ y) ⊕ (x ⊗ z)
    x_mul_y = create_symbolic_avc_val_V2("x_mul_y")
    for c in get_base_avc_constraints_V2(x_mul_y, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_mul_bc_smt_logic_V2(x, y, x_mul_y, omega_smt))
    x_mul_z = create_symbolic_avc_val_V2("x_mul_z")
    for c in get_base_avc_constraints_V2(x_mul_z, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_mul_bc_smt_logic_V2(x, z, x_mul_z, omega_smt))
    rhs = create_symbolic_avc_val_V2("rhs_dist1")
    for c in get_base_avc_constraints_V2(rhs, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_add_bc_smt_logic_V2(x_mul_y, x_mul_z, rhs, omega_smt))

    dist_mul_over_add_holds = False
    solver.push()
    solver.add_assertion(Not(avc_deep_equals_smt_V2(lhs, rhs))) # Test for deep equality
    if not solver.solve():
        dist_mul_over_add_holds = True
        print("  RESULT: Mul over Add Distributivity (deep equality) IS SATISFIED.")
    else:
        print("  RESULT: Mul over Add Distributivity (deep equality) IS NOT SATISFIED. Counterexample:")
        # (Printing model details similar to above can be added here if needed)
    solver.pop()
    # (Could add test for Add over Mul distributivity if desired)
    return dist_mul_over_add_holds


# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_O1_Lattice_Test_V2: Testing Lattice Properties (Algebraic Order) ======")
    print("Order Relation (is_le_algebraic_smt): Algebraic Unio (0) is bottom; DFI_k ordered by value.")
    print("AVCA Operations: Best Combination (add_v1.1, mul_v1.2) - results are full symbolic structures.")
    
    omega_to_test = 3
    print(f"\nSetting Python-side _Omega_py_H_O1_V2 = {omega_to_test} for base constraints context.")

    mul_is_meet = test_op_is_meet_V2(avc_mul_bc_smt_logic_V2, "Mul", omega_to_test)
    add_is_join = test_op_is_join_V2(avc_add_bc_smt_logic_V2, "Add", omega_to_test)
    
    distributive_result = "N/A"
    if mul_is_meet and add_is_join:
        print(f"\nProceeding to test distributivity for Omega={omega_to_test} as it's a lattice.")
        dist_holds = test_distributivity_V2(omega_to_test, mul_is_meet, add_is_join)
        distributive_result = "Yes" if dist_holds else "No"
    else:
         print(f"\nSkipping distributivity test for Omega={omega_to_test} as it's not confirmed to be a lattice.")


    print("\n\n--- Overall Summary of H-O1 Test (Algebraic Order, V2) ---")
    print(f"For Omega = {omega_to_test}:")
    print(f"  Order Tested: Algebraic Unio (0) is ⊥, DFI_k ordered by magnitude.")
    print(f"  Is AVCA Best-Combo Mul (⊗) a meet operation? {'Yes' if mul_is_meet else 'No'}")
    print(f"  Is AVCA Best-Combo Add (⊕) a join operation?  {'Yes' if add_is_join else 'No'}")
    if mul_is_meet and add_is_join:
        print(f"  Does ⊗ distribute over ⊕ (deep equality)?    {distributive_result}")

    print("\n====== H_O1_Lattice_Test_V2 Script Finished ======")