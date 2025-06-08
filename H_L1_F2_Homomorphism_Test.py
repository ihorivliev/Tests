# H_L1_F2_Homomorphism_Test.py
# SMT Test for Hypothesis H-L1: AVCA-Ω (Best Combo) collapses to an F2-like Boolean ring
# under the mapping phi_B (AU -> 1_B, ZU/DFI -> 0_B).

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Global Omega for AVCA operations (Python side for setup) ---
_Omega_py_H_L1: int = 0

# --- Symbolic AVCA Value Representation (full structure with aspects) ---
# Reusing from H_O1_Lattice_Test_V2.py (renamed with _L1 suffix for clarity)
def create_symbolic_avc_val_L1(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero_L1", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo_L1", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite_L1", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_L1", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints_L1(avc_repr: Dict[str, FNode], omega_smt_node: FNode, omega_py_val_for_check: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] >= Int(1), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], Int(0)))
    ]
    if omega_py_val_for_check == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_deep_equals_smt_L1(s1: Dict[str, FNode], s2: Dict[str, FNode]) -> FNode:
    return And(Iff(s1["is_zero"], s2["is_zero"]),
               Iff(s1["is_areo"], s2["is_areo"]),
               Iff(s1["is_finite"], s2["is_finite"]),
               Equals(s1["val"], s2["val"]))

def IsUnioSMT_L1(s: Dict[str, FNode]) -> FNode:
    return Or(s["is_zero"], s["is_areo"])

# --- "Best Combination" SMT Logic Builders (from H_O1_Lattice_Test_V2.py) ---
def avc_add_bc_smt_logic_L1(a: Dict[str, FNode], b: Dict[str, FNode],
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_a = avc_deep_equals_smt_L1(res, a)
    res_is_b = avc_deep_equals_smt_L1(res, b)
    case1_a_is_unio = Implies(IsUnioSMT_L1(a), res_is_b)
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], IsUnioSMT_L1(b)), res_is_a)
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

def avc_mul_bc_smt_logic_L1(a: Dict[str, FNode], b: Dict[str, FNode],
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_zero_unio_state = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    res_is_areo_unio_state = And(res["is_areo"], Not(res["is_zero"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    cond_any_operand_is_unio = Or(IsUnioSMT_L1(a), IsUnioSMT_L1(b))
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

# --- Mapping to Boolean {0, 1} and F2 Operations ---
def phi_B_smt(s_avca_sym: Dict[str, FNode]) -> FNode:
    """Maps symbolic AVCA value to SMT Int(0) or Int(1) for F2."""
    # AU_obj maps to 1_B, ZU_obj/DFI maps to 0_B
    return Ite(s_avca_sym["is_areo"], Int(1), Int(0))

def add_F2_smt(b1_smt_int: FNode, b2_smt_int: FNode) -> FNode:
    """F2 addition (XOR): 0+0=0, 0+1=1, 1+0=1, 1+1=0."""
    # (b1 + b2) % 2, or b1 != b2
    return Ite(Equals(b1_smt_int, b2_smt_int), Int(0), Int(1))

def mul_F2_smt(b1_smt_int: FNode, b2_smt_int: FNode) -> FNode:
    """F2 multiplication (AND): 1*1=1, else 0."""
    return Ite(And(Equals(b1_smt_int, Int(1)), Equals(b2_smt_int, Int(1))), Int(1), Int(0))

# --- SMT Test Function for Homomorphism ---
def test_H_L1_homomorphism(omega_py: int):
    global _Omega_py_H_L1
    _Omega_py_H_L1 = omega_py
    omega_smt = Int(omega_py)

    print(f"\n--- Testing H-L1: AVCA-Ω={omega_py} to F2 Homomorphism ---")

    x_sym = create_symbolic_avc_val_L1("x_hom")
    y_sym = create_symbolic_avc_val_L1("y_hom")

    solver = Solver(name="z3")
    for c in get_base_avc_constraints_L1(x_sym, omega_smt, omega_py): solver.add_assertion(c)
    for c in get_base_avc_constraints_L1(y_sym, omega_smt, omega_py): solver.add_assertion(c)

    # Test Additive Homomorphism: phi_B(x ⊕_BC y) == phi_B(x) ⊕_F2 phi_B(y)
    res_add_avca_sym = create_symbolic_avc_val_L1("res_add_avca")
    for c in get_base_avc_constraints_L1(res_add_avca_sym, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_add_bc_smt_logic_L1(x_sym, y_sym, res_add_avca_sym, omega_smt))

    lhs_add_hom = phi_B_smt(res_add_avca_sym)
    rhs_add_hom = add_F2_smt(phi_B_smt(x_sym), phi_B_smt(y_sym))
    add_hom_property = Equals(lhs_add_hom, rhs_add_hom)

    add_hom_holds = False
    solver.push()
    solver.add_assertion(Not(add_hom_property))
    if not solver.solve():
        add_hom_holds = True
        print("  RESULT (Additive Homomorphism): Holds. (No counterexample found).")
    else:
        print("  RESULT (Additive Homomorphism): FAILS. Counterexample found:")
        model = solver.get_model()
        def pval_hom(s_sym_arg, name): # Adjusted pval for homomorphism context
            aspect = "A" if model.get_value(s_sym_arg["is_areo"]).is_true() else \
                     "Z" if model.get_value(s_sym_arg["is_zero"]).is_true() else "F"
            val = model.get_value(s_sym_arg["val"])
            phi_val = model.get_value(phi_B_smt(s_sym_arg))
            return f"{name}: Aspect={aspect}, DFIVal={val} -> phi_B={phi_val}"
        print(f"    {pval_hom(x_sym, 'x')}")
        print(f"    {pval_hom(y_sym, 'y')}")
        print(f"    x ⊕_BC y: {pval_hom(res_add_avca_sym, 'x⊕y')}")
        print(f"    LHS = phi_B(x ⊕_BC y) = {model.get_value(lhs_add_hom)}")
        print(f"    RHS = phi_B(x) ⊕_F2 phi_B(y) = {model.get_value(rhs_add_hom)}")
    solver.pop()

    # Test Multiplicative Homomorphism: phi_B(x ⊗_BC y) == phi_B(x) ⊗_F2 phi_B(y)
    res_mul_avca_sym = create_symbolic_avc_val_L1("res_mul_avca")
    for c in get_base_avc_constraints_L1(res_mul_avca_sym, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_mul_bc_smt_logic_L1(x_sym, y_sym, res_mul_avca_sym, omega_smt))

    lhs_mul_hom = phi_B_smt(res_mul_avca_sym)
    rhs_mul_hom = mul_F2_smt(phi_B_smt(x_sym), phi_B_smt(y_sym))
    mul_hom_property = Equals(lhs_mul_hom, rhs_mul_hom)

    mul_hom_holds = False
    solver.push()
    solver.add_assertion(Not(mul_hom_property))
    if not solver.solve():
        mul_hom_holds = True
        print("  RESULT (Multiplicative Homomorphism): Holds. (No counterexample found).")
    else:
        print("  RESULT (Multiplicative Homomorphism): FAILS. Counterexample found:")
        model = solver.get_model()
        def pval_hom(s_sym_arg, name): # Re-define for this scope if needed, or ensure it's outer scope
            aspect = "A" if model.get_value(s_sym_arg["is_areo"]).is_true() else \
                     "Z" if model.get_value(s_sym_arg["is_zero"]).is_true() else "F"
            val = model.get_value(s_sym_arg["val"])
            phi_val = model.get_value(phi_B_smt(s_sym_arg))
            return f"{name}: Aspect={aspect}, DFIVal={val} -> phi_B={phi_val}"
        print(f"    {pval_hom(x_sym, 'x')}")
        print(f"    {pval_hom(y_sym, 'y')}")
        print(f"    x ⊗_BC y: {pval_hom(res_mul_avca_sym, 'x⊗y')}")
        print(f"    LHS = phi_B(x ⊗_BC y) = {model.get_value(lhs_mul_hom)}")
        print(f"    RHS = phi_B(x) ⊗_F2 phi_B(y) = {model.get_value(rhs_mul_hom)}")
    solver.pop()
    
    return add_hom_holds, mul_hom_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_L1_F2_Homomorphism_Test: Testing AVCA-Ω to F2 Homomorphism ======")
    print("Mapping phi_B: AREO_UNIO_obj -> 1_B; ZERO_UNIO_obj/DFI -> 0_B.")
    print("AVCA Operations: Best Combination (add_v1.1, mul_v1.2).")
    
    omega_to_test = 3
    print(f"\nSetting Python-side _Omega_py_H_L1 = {omega_to_test} for base constraints context.")

    add_hom_result, mul_hom_result = test_H_L1_homomorphism(omega_to_test)

    print("\n--- Summary of H-L1 Test ---")
    print(f"For Omega = {omega_to_test}:")
    print(f"  Is phi_B an additive homomorphism (AVCA ⊕_BC to F2 ⊕_F2)? {'Yes' if add_hom_result else 'No'}")
    print(f"  Is phi_B a multiplicative homomorphism (AVCA ⊗_BC to F2 ⊗_F2)? {'Yes' if mul_hom_result else 'No'}")

    if add_hom_result and mul_hom_result:
        print("\nConclusion: H-L1 appears to HOLD for this Omega. AVCA-Ω with Best Combo ops,")
        print("            under the phi_B mapping, acts like an F2 Boolean ring.")
    else:
        print("\nConclusion: H-L1 FAILED for this Omega for one or both operations.")
        print("            The quotienting by 'is_areo?' does not yield a simple F2 structure homomorphically.")

    print("\n====== H_L1_F2_Homomorphism_Test Script Finished ======")