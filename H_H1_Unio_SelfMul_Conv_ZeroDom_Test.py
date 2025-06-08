# H_H1_Unio_SelfMul_Conv_ZeroDom_Test.py
# SMT Test for Hypothesis H-H1: "Repeated self-multiplication of any Unio 
# converges to AU in <=2 steps (absorbing state)"
# This test uses an ALTERNATIVE multiplication rule: Mul_ZeroDomMixed.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Global Omega ---
_Omega_py_H_H1_ZD: int = 0 

# --- Symbolic AVCA Value Representation ---
def create_symbolic_avc_val_H1_ZD(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero_H1ZD", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo_H1ZD", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite_H1ZD", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_H1ZD", SMT_INT_TYPE), 
        "name": name_prefix
    }

def get_base_avc_constraints_H1_ZD(avc_repr: Dict[str, FNode], omega_smt_node: FNode, omega_py_val_for_check: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] >= Int(1), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], Int(0))) 
    ]
    if omega_py_val_for_check > 0 and omega_py_val_for_check == 1 :
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def IsUnioSMT_H1_ZD(s: Dict[str, FNode]) -> FNode:
    return Or(s["is_zero"], s["is_areo"])

# --- SMT Logic Builder for Mul_ZeroDomMixed ---
def avc_mul_ZeroDomMixed_smt_logic_H1_ZD(a: Dict[str, FNode], b: Dict[str, FNode],
                                        res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_zero_unio_state = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    res_is_areo_unio_state = And(res["is_areo"], Not(res["is_zero"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))

    cond_any_operand_is_unio = Or(IsUnioSMT_H1_ZD(a), IsUnioSMT_H1_ZD(b))
    
    # Mul_ZeroDomMixed logic for Unio-involved:
    # "If ZU aspect present in any Unio operand, result ZU_obj; 
    #  else (if Unios involved all AU_obj, or AU with DFI) result AU_obj."
    cond_any_unio_operand_is_zero = Or(a["is_zero"], b["is_zero"]) # If a is_zero, it's Unio. If b is_zero, it's Unio.

    unio_case_behavior = Ite(cond_any_unio_operand_is_zero,
                             res_is_zero_unio_state, # Zero dominates
                             res_is_areo_unio_state  # Else (must be AU-AU or AU-DFI if Unio involved)
                            )

    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    symbolic_prod_val = Times(a["val"], b["val"])
    res_is_dfi_prod_state = And(res["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]),
                                Equals(res["val"], symbolic_prod_val))
    # DFI overflow rule is consistently to AREO_UNIO for semantic reasons across system
    dfi_overflow_to_areo = res_is_areo_unio_state 
    
    dfi_case_behavior = Ite(And(symbolic_prod_val >= Int(1), symbolic_prod_val < omega_smt_node),
                            res_is_dfi_prod_state,
                            dfi_overflow_to_areo) 
                            
    return Ite(cond_any_operand_is_unio, unio_case_behavior, dfi_case_behavior)

# --- SMT Test Function for H-H1 with alternative multiplication ---
def test_H_H1_unio_convergence_alt_mul(omega_py: int, 
                                       mul_logic_func: Callable, 
                                       mul_rule_name: str):
    global _Omega_py_H_H1_ZD
    _Omega_py_H_H1_ZD = omega_py
    omega_smt = Int(omega_py)

    print(f"\n--- Testing H-H1: Unio Self-Multiplication Convergence to AU for Omega={omega_py} ---")
    print(f"    Using multiplication rule: {mul_rule_name}")

    U_initial_sym = create_symbolic_avc_val_H1_ZD("U_initial_alt")
    U_step1_sym = create_symbolic_avc_val_H1_ZD("U_step1_alt")
    U_step2_sym = create_symbolic_avc_val_H1_ZD("U_step2_alt")

    solver = Solver(name="z3")

    for c in get_base_avc_constraints_H1_ZD(U_initial_sym, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(IsUnioSMT_H1_ZD(U_initial_sym)) 

    for c in get_base_avc_constraints_H1_ZD(U_step1_sym, omega_smt, omega_py): solver.add_assertion(c)
    for c in get_base_avc_constraints_H1_ZD(U_step2_sym, omega_smt, omega_py): solver.add_assertion(c)

    solver.add_assertion(mul_logic_func(U_initial_sym, U_initial_sym, U_step1_sym, omega_smt))
    solver.add_assertion(mul_logic_func(U_step1_sym, U_step1_sym, U_step2_sym, omega_smt))

    property_P = Or(U_step1_sym["is_areo"], U_step2_sym["is_areo"])
    solver.add_assertion(Not(property_P))

    print(f"  Solving for a counterexample to H-H1 (initial Unio not converging to AU in <=2 steps with {mul_rule_name})...")
    property_holds_for_all_unio = False
    if not solver.solve(): 
        property_holds_for_all_unio = True
        print(f"  RESULT: H-H1 (any Unio converges to AU in <=2 steps) HOLDS for '{mul_rule_name}'.")
    else: 
        print(f"  RESULT: H-H1 (any Unio converges to AU in <=2 steps) is FALSE for '{mul_rule_name}'. Counterexample:")
        model = solver.get_model()
        def pval_h1_alt(s_sym):
            aspect = "A" if model.get_value(s_sym["is_areo"]).is_true() else \
                     "Z" if model.get_value(s_sym["is_zero"]).is_true() else "F"
            val = model.get_value(s_sym["val"])
            return f"{s_sym['name']}: Aspect={aspect}, Val={val}"
        
        print(f"    {pval_h1_alt(U_initial_sym)}")
        print(f"    {pval_h1_alt(U_step1_sym)}    (U_initial ⊗ U_initial)")
        print(f"    {pval_h1_alt(U_step2_sym)}    (U_step1 ⊗ U_step1)")
        print(f"    Property (U_step1 is AU or U_step2 is AU) evaluated to: {model.get_value(property_P)}")
        property_holds_for_all_unio = False
    
    return property_holds_for_all_unio

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_H1_Unio_SelfMul_Conv_ZeroDom_Test: ======")
    
    omega_to_test = 3 
    print(f"\nSetting Python-side _Omega_py_H_H1_ZD = {omega_to_test}")

    # Test with Mul_ZeroDomMixed
    h_h1_holds_zerodom = test_H_H1_unio_convergence_alt_mul(
        omega_to_test, 
        avc_mul_ZeroDomMixed_smt_logic_H1_ZD,
        "Mul_ZeroDomMixed"
    )

    print("\n--- Summary of H-H1 Test with Mul_ZeroDomMixed ---")
    print(f"For Omega = {omega_to_test} using 'Mul_ZeroDomMixed':")
    print(f"  Hypothesis H-H1 (Any Unio self-multiplied converges to AREO_UNIO_obj in <=2 steps): {'Holds' if h_h1_holds_zerodom else 'Does NOT Hold'}")

    if not h_h1_holds_zerodom:
        print("\n  Interpretation (ZeroDomMixed): The property 'any Unio converges to AU in <=2 steps' is falsified")
        print("  because ZERO_UNIO self-multiplies to ZERO_UNIO under this rule as well.")
    
    print("\nComparison with 'Areo Dominates' (mul_v1.2 from previous test):")
    print("  For 'Areo Dominates', the property also 'Does NOT Hold' for the same reason (ZU stays ZU).")
    print("  This suggests the 'iff AreoDom' part of H-H1's original sketch needs careful reconsideration,")
    print("  as the property (convergence of *any* Unio to AU) appears false for both rules.")

    print("\n====== H_H1_Unio_SelfMul_Conv_ZeroDom_Test Script Finished ======")