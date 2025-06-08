# H_H1_Unio_SelfMul_Convergence_Test.py
# SMT Test for Hypothesis H-H1: "Repeated self-multiplication of any Unio 
# converges to AU in <=2 steps (absorbing state)"
# This test uses the "Best Combination" kernel's multiplication rule: avc_mul_v1.2 ("Areo Dominates").

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Global Omega for AVCA operations (Python side for setup) ---
# Omega value doesn't strictly affect Unio-Unio operations but is needed for constraints.
_Omega_py_H_H1: int = 0 

# --- Symbolic AVCA Value Representation (full structure with aspects) ---
# Reusing from previous scripts (renamed with _H1 suffix for clarity)
def create_symbolic_avc_val_H1(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero_H1", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo_H1", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite_H1", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_H1", SMT_INT_TYPE), 
        "name": name_prefix
    }

def get_base_avc_constraints_H1(avc_repr: Dict[str, FNode], omega_smt_node: FNode, omega_py_val_for_check: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] >= Int(1), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], Int(0))) 
    ]
    if omega_py_val_for_check == 1: # Should not happen if we test for Omega >=1 for DFI
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def IsUnioSMT_H1(s: Dict[str, FNode]) -> FNode:
    return Or(s["is_zero"], s["is_areo"])

# --- "Best Combination" SMT Logic Builder for Multiplication (avc_mul_v1.2) ---
def avc_mul_bc_smt_logic_H1(a: Dict[str, FNode], b: Dict[str, FNode],
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_zero_unio_state = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    res_is_areo_unio_state = And(res["is_areo"], Not(res["is_zero"]), Not(res["is_finite"]),
                                 Equals(res["val"], Int(0)))
    cond_any_operand_is_unio = Or(IsUnioSMT_H1(a), IsUnioSMT_H1(b))
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

# --- SMT Test Function for H-H1 ---
def test_H_H1_unio_convergence(omega_py: int):
    global _Omega_py_H_H1
    _Omega_py_H_H1 = omega_py
    omega_smt = Int(omega_py)

    print(f"\n--- Testing H-H1: Unio Self-Multiplication Convergence to AU for Omega={omega_py} ---")
    print("    Using Best Combination mul_v1.2 ('Areo Dominates')")

    U_initial_sym = create_symbolic_avc_val_H1("U_initial")
    U_step1_sym = create_symbolic_avc_val_H1("U_step1")
    U_step2_sym = create_symbolic_avc_val_H1("U_step2")

    solver = Solver(name="z3")

    # Constraints for U_initial_sym
    for c in get_base_avc_constraints_H1(U_initial_sym, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(IsUnioSMT_H1(U_initial_sym)) # Constrain U_initial to be Unio (ZU or AU)

    # Constraints for U_step1_sym and U_step2_sym (they must be valid AVCA values)
    for c in get_base_avc_constraints_H1(U_step1_sym, omega_smt, omega_py): solver.add_assertion(c)
    for c in get_base_avc_constraints_H1(U_step2_sym, omega_smt, omega_py): solver.add_assertion(c)

    # Define the operations
    # U_step1 = U_initial ⊗ U_initial
    solver.add_assertion(avc_mul_bc_smt_logic_H1(U_initial_sym, U_initial_sym, U_step1_sym, omega_smt))
    # U_step2 = U_step1 ⊗ U_step1
    solver.add_assertion(avc_mul_bc_smt_logic_H1(U_step1_sym, U_step1_sym, U_step2_sym, omega_smt))

    # Property P: U_step1 is AREO_UNIO_obj OR U_step2 is AREO_UNIO_obj
    # The ["is_areo"] flag being true means it's AREO_UNIO_obj
    property_P = Or(U_step1_sym["is_areo"], U_step2_sym["is_areo"])

    # We want to prove P holds for ALL Unio U_initial_sym.
    # So, we assert NOT P and check if it's SAT (meaning counterexample found) or UNSAT (meaning P holds).
    solver.add_assertion(Not(property_P))

    print("  Solving for a counterexample to H-H1 (i.e., an initial Unio that does not converge to AU in <=2 steps)...")
    if solver.solve(): # If SAT, then NOT P is true, so P is false (counterexample exists)
        print("  RESULT: H-H1 is FALSE for 'Areo Dominates' multiplication. Counterexample found:")
        model = solver.get_model()
        def pval_h1(s_sym):
            aspect = "A" if model.get_value(s_sym["is_areo"]).is_true() else \
                     "Z" if model.get_value(s_sym["is_zero"]).is_true() else "F" # Should be Z or A
            val = model.get_value(s_sym["val"]) # Should be 0 for Unio
            return f"{s_sym['name']}: Aspect={aspect}, Val={val}"
        
        print(f"    {pval_h1(U_initial_sym)}")
        print(f"    {pval_h1(U_step1_sym)}    (U_initial ⊗ U_initial)")
        print(f"    {pval_h1(U_step2_sym)}    (U_step1 ⊗ U_step1)")
        print(f"    Property (U_step1 is AU or U_step2 is AU) evaluated to: {model.get_value(property_P)}")
        property_holds = False
    else: # If UNSAT, then NOT P is false, so P is true
        print("  RESULT: H-H1 HOLDS for 'Areo Dominates' multiplication. (No counterexample found).")
        property_holds = True
    
    return property_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_H1_Unio_SelfMul_Convergence_Test: ======")
    
    # Omega value mostly for context of base constraints, Unio-Unio ops are usually Omega-independent
    omega_to_test = 3 
    print(f"\nSetting Python-side _Omega_py_H_H1 = {omega_to_test}")

    h_h1_holds = test_H_H1_unio_convergence(omega_to_test)

    print("\n--- Summary of H-H1 Test ---")
    print(f"For Omega = {omega_to_test} using 'Areo Dominates' multiplication (avc_mul_v1.2):")
    print(f"  Hypothesis H-H1 (Any Unio self-multiplied converges to AREO_UNIO_obj in <=2 steps): {'Holds' if h_h1_holds else 'Does NOT Hold'}")

    if not h_h1_holds:
        print("\n  Interpretation: The hypothesis, as stated, is falsified for the 'Areo Dominates'")
        print("  multiplication rule because ZERO_UNIO self-multiplies to ZERO_UNIO.")
    else:
        print("\n  Interpretation: The hypothesis appears to hold. This would mean even ZERO_UNIO converges to AREO_UNIO.")
        print("  (This would be surprising based on manual trace - re-check SMT logic if this occurs).")


    print("\n====== H_H1_Unio_SelfMul_Convergence_Test Script Finished ======")