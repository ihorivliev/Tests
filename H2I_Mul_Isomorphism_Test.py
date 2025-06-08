# Script H2I_Mul_Isomorphism_Test.py
# Purpose: To test if Kernel_AD (with Areo-dominant multiplication) and
#          Kernel_ZD (with ZeroDomMixed multiplication) are isomorphic
#          with respect to their multiplication operation (⊗) under an
#          aspect-swapping map φ for a given Omega.
# Test: φ(x ⊗_AD y) = φ(x) ⊗_ZD φ(y)

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal
import math

# --- Global Omega Parameter & Test Results ---
# Omega_H2I: int = 0 # Global not strictly needed if passed everywhere, but can be used for set_avca_omega_h2i
smt_test_results_summary_H2I: Dict[int, Dict[str, int]] = {}
smt_test_failures_details_H2I: List[Dict[str, Any]] = []

# --- Unio Class Definition (for Python-side reference if needed, SMT uses symbolic) ---
class Unio_H2I: # Renamed to avoid conflict if other scripts are imported
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_H2I aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_H2I)
    def __hash__(self) -> int:
        return hash(type(self))
    def __repr__(self) -> str:
        return f"Unio_H2I('{self.aspect}')"

ZERO_UNIO_H2I = Unio_H2I("zero")
AREO_UNIO_H2I = Unio_H2I("areo")
AVCVal_H2I = Union[int, Unio_H2I] # Using the renamed Unio

# This function sets a global, but the script will primarily pass omega_py as a parameter
_Omega_H2I_Global_Context: int = 0
def set_avca_omega_h2i(omega_value: int, verbose: bool = False):
    global _Omega_H2I_Global_Context
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_H2I parameter must be an integer >= 1.")
    _Omega_H2I_Global_Context = omega_value
    if verbose:
        print(f"H2I Isomorphism Test: Global Context Omega_H2I set to {_Omega_H2I_Global_Context}")

# --- SMT Symbolic Representation and Base Constraints ---
def create_symbolic_avc_val_h2i(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_ZA_h2i", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_AA_h2i", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_DFI_h2i", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_h2i", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints_h2i(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    # current_omega_py is the Python integer value of Omega for this context
    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], Int(0)))
    ]
    if current_omega_py == 1: # Use the passed Python integer Omega for this check
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_deep_equals_smt_h2i(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    return And(
        Iff(avc1["is_zero_aspect"], avc2["is_zero_aspect"]),
        Iff(avc1["is_areo_aspect"], avc2["is_areo_aspect"]),
        Iff(avc1["is_finite"], avc2["is_finite"]),
        Implies(avc1["is_finite"], Equals(avc1["val"], avc2["val"]))
    )

# --- SMT Logic Builders for Multiplication Variants ---
def _smt_logic_mul_dfi_dfi_h2i(a: Dict[str, FNode], b: Dict[str, FNode],
                               res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    prod_val = Times(a["val"], b["val"])
    res_is_FP_prod_formula = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), Equals(res["val"], prod_val))
    res_is_AU_formula = And(res["is_areo_aspect"], Not(res["is_zero_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    return Ite(And(prod_val >= Int(1), prod_val < omega_smt_node),
               res_is_FP_prod_formula,
               res_is_AU_formula)

def avc_mul_smt_logic_AreoDom_H2I(a: Dict[str, FNode], b: Dict[str, FNode],
                                  res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    cond_any_operand_is_unio = Or(a_is_unio, b_is_unio)
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(res["is_areo_aspect"], Not(res["is_zero_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    cond_any_unio_operand_is_areo = Or(a["is_areo_aspect"], b["is_areo_aspect"])
    unio_case_behavior = Ite(cond_any_unio_operand_is_areo, res_is_AU_formula, res_is_ZU_formula)
    dfi_case_behavior = _smt_logic_mul_dfi_dfi_h2i(a, b, res, omega_smt_node)
    return Ite(cond_any_operand_is_unio, unio_case_behavior, dfi_case_behavior)

def avc_mul_smt_logic_ZeroDom_H2I(a: Dict[str, FNode], b: Dict[str, FNode],
                                   res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    cond_any_operand_is_unio = Or(a_is_unio, b_is_unio)
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(res["is_areo_aspect"], Not(res["is_zero_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    cond_any_unio_operand_is_zero = Or(a["is_zero_aspect"], b["is_zero_aspect"])
    cond_any_unio_operand_is_areo = Or(a["is_areo_aspect"], b["is_areo_aspect"])
    unio_case_behavior = Ite(cond_any_unio_operand_is_zero,
                             res_is_ZU_formula,
                             Ite(cond_any_unio_operand_is_areo, res_is_AU_formula, res_is_ZU_formula) 
                            )
    dfi_case_behavior = _smt_logic_mul_dfi_dfi_h2i(a, b, res, omega_smt_node)
    return Ite(cond_any_operand_is_unio, unio_case_behavior, dfi_case_behavior)

# --- SMT Logic for φ (Phi) Map ---
def apply_phi_map_smt_h2i(input_avc: Dict[str, FNode], output_avc: Dict[str, FNode]) -> FNode:
    dfi_case = Implies(input_avc["is_finite"],
                       And(output_avc["is_finite"],
                           Not(output_avc["is_zero_aspect"]), Not(output_avc["is_areo_aspect"]),
                           Equals(output_avc["val"], input_avc["val"])))
    zu_case = Implies(input_avc["is_zero_aspect"],
                      And(output_avc["is_areo_aspect"],
                          Not(output_avc["is_zero_aspect"]), Not(output_avc["is_finite"]),
                          Equals(output_avc["val"], Int(0))))
    au_case = Implies(input_avc["is_areo_aspect"],
                      And(output_avc["is_zero_aspect"],
                          Not(output_avc["is_areo_aspect"]), Not(output_avc["is_finite"]),
                          Equals(output_avc["val"], Int(0))))
    return And(dfi_case, zu_case, au_case)

# --- SMT Prover Function ---
def initialize_smt_omega_results_h2i(current_omega_py: int): # Takes current_omega_py
    if current_omega_py not in smt_test_results_summary_H2I:
        smt_test_results_summary_H2I[current_omega_py] = {"passed": 0, "failed": 0, "skipped": 0}

def prove_or_find_counterexample_smt_h2i(
    property_name: str, current_omega_py: int, # Takes current_omega_py
    setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    
    initialize_smt_omega_results_h2i(current_omega_py) # Uses parameter current_omega_py
    property_holds_observed = False
    counterexample_witness_str = None
    
    with Solver(name="z3", logic="LIA") as s:
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)
        
        target_assertion = property_to_verify if is_existential else Not(property_to_verify)
        s.add_assertion(target_assertion)
        solve_result = s.solve()

        if is_existential: property_holds_observed = solve_result
        else: property_holds_observed = not solve_result

        if solve_result and ( (not property_holds_observed and not is_existential) or \
                              (property_holds_observed and is_existential and not expect_property_to_hold) or \
                              (not property_holds_observed and not is_existential and not expect_property_to_hold) or # For showing CE when P fails as expected
                              (property_holds_observed and is_existential and expect_property_to_hold) ): # For showing witness when P holds as expected
            model = s.get_model(); ce_parts = []
            for repr_dict in inputs_reprs:
                name = repr_dict['name']
                try:
                    is_z = model.get_value(repr_dict['is_zero_aspect']).is_true()
                    is_a = model.get_value(repr_dict['is_areo_aspect']).is_true()
                    # is_f = model.get_value(repr_dict['is_finite']).is_true() # Already implied by not is_z and not is_a
                    val_smt = model.get_value(repr_dict['val'])
                    state_str = "ZU" if is_z else ("AU" if is_a else (f"Fp({val_smt})"))
                    ce_parts.append(f"{name}={state_str}")
                except Exception: ce_parts.append(f"{name}=?")
            counterexample_witness_str = "; ".join(ce_parts)

    success_for_summary = (property_holds_observed == expect_property_to_hold)
    status_emoji = "✅" if success_for_summary else "❌"; final_message = ""

    if is_existential:
        if expect_property_to_hold: final_message = "Existence PROVED." if property_holds_observed else "Existence FAILED (expected)."
        else: final_message = "Non-existence CONFIRMED." if not property_holds_observed else "Non-existence FAILED (unexpected witness)."
    else: # Universal
        if expect_property_to_hold: final_message = "Property PROVED universally." if property_holds_observed else "Property FAILED (counterexample found)."
        else: final_message = "Property NON-UNIVERSALITY confirmed." if not property_holds_observed else "Property INCORRECTLY held universally."

    if success_for_summary: smt_test_results_summary_H2I[current_omega_py]["passed"] += 1 # Uses parameter
    else:
        smt_test_results_summary_H2I[current_omega_py]["failed"] += 1 # Uses parameter
        smt_test_failures_details_H2I.append({
            "property": property_name, "omega": current_omega_py, # Uses parameter
            "expectation_met": success_for_summary,
            "observed_holds": property_holds_observed,
            "expected_to_hold": expect_property_to_hold,
            "message": final_message,
            "counterexample_witness": counterexample_witness_str
        })

    print(f"{status_emoji} Ω={current_omega_py}: {property_name} (Expect Isomorphism: {expect_property_to_hold}) - {final_message}") # Uses parameter
    if counterexample_witness_str:
        label = "Witness" if is_existential and property_holds_observed and expect_property_to_hold else "Counterexample"
        print(f"    {label}: {counterexample_witness_str}")


def check_isomorphism_for_op_H2I(
    op_name_str: str, current_omega_py: int, # Renamed parameter for clarity
    op_AD_smt_logic: Callable, op_ZD_smt_logic: Callable ):
    
    # No global Omega_H2I needed here if current_omega_py is used consistently
    test_name = f"H2I: Isomorphism φ(x {op_name_str}_AD y) = φ(x) {op_name_str}_ZD φ(y) for Ω={current_omega_py}"
    initialize_smt_omega_results_h2i(current_omega_py) # Pass current_omega_py

    omega_smt_node = Int(current_omega_py) # Use current_omega_py
    x = create_symbolic_avc_val_h2i("x_iso")
    y = create_symbolic_avc_val_h2i("y_iso")
    res_AD_internal = create_symbolic_avc_val_h2i("res_AD_internal")
    lhs_mapped = create_symbolic_avc_val_h2i("lhs_mapped")
    phi_x = create_symbolic_avc_val_h2i("phi_x")
    phi_y = create_symbolic_avc_val_h2i("phi_y")
    rhs_direct = create_symbolic_avc_val_h2i("rhs_direct")

    setup = (get_base_avc_constraints_h2i(x, omega_smt_node, current_omega_py) + # Pass current_omega_py
             get_base_avc_constraints_h2i(y, omega_smt_node, current_omega_py) + # Pass current_omega_py
             get_base_avc_constraints_h2i(res_AD_internal, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i(lhs_mapped, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i(phi_x, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i(phi_y, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i(rhs_direct, omega_smt_node, current_omega_py)
            )

    setup.append(op_AD_smt_logic(x, y, res_AD_internal, omega_smt_node))
    setup.append(apply_phi_map_smt_h2i(res_AD_internal, lhs_mapped))
    setup.append(apply_phi_map_smt_h2i(x, phi_x))
    setup.append(apply_phi_map_smt_h2i(y, phi_y))
    setup.append(op_ZD_smt_logic(phi_x, phi_y, rhs_direct, omega_smt_node))

    property_formula = avc_deep_equals_smt_h2i(lhs_mapped, rhs_direct)
    
    prove_or_find_counterexample_smt_h2i(
        test_name, 
        current_omega_py, # Pass current_omega_py
        setup, 
        property_formula, 
        [x, y, res_AD_internal, lhs_mapped, phi_x, phi_y, rhs_direct], 
        expect_property_to_hold=True, # Expecting isomorphism to hold
        is_existential=False
    )

# --- Main Execution ---
if __name__ == "__main__":
    omega_to_test_h2i = 3
    set_avca_omega_h2i(omega_to_test_h2i, verbose=True) # Sets global for reference, but functions use passed param

    current_test_run_name_h2i = f"H2I: Multiplication Isomorphism (Ω={omega_to_test_h2i})"
    print(f"\n{'='*30} SMT Test for {current_test_run_name_h2i} {'='*30}")
    
    check_isomorphism_for_op_H2I(
        op_name_str="⊗",
        current_omega_py=omega_to_test_h2i, # Pass the python int omega
        op_AD_smt_logic=avc_mul_smt_logic_AreoDom_H2I,
        op_ZD_smt_logic=avc_mul_smt_logic_ZeroDom_H2I
    )

    # --- Summarize ---
    if omega_to_test_h2i in smt_test_results_summary_H2I:
        passed = smt_test_results_summary_H2I[omega_to_test_h2i].get('passed', 0)
        failed = smt_test_results_summary_H2I[omega_to_test_h2i].get('failed', 0)
        print(f"\nSMT Summary for {current_test_run_name_h2i}: Passed={passed}, Failed={failed}")
    else:
        print(f"\nSMT Summary for {current_test_run_name_h2i}: No results.")
    print(f"{'='*70}")

    total_passed_overall = sum(d.get('passed',0) for d in smt_test_results_summary_H2I.values())
    total_failed_overall = sum(d.get('failed',0) for d in smt_test_results_summary_H2I.values())

    if total_failed_overall == 0 and total_passed_overall > 0:
        print("\n🎉🎉🎉 H2I Isomorphism Test (for multiplication) suggests structure IS PRESERVED under aspect swap! 🎉🎉🎉")
    elif total_failed_overall > 0:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ H2I Isomorphism Test (for multiplication) FAILED. Structures are different. ⚠️⚠️⚠️")
        if smt_test_failures_details_H2I:
             print("\n--- H2I Isomorphism Test DETAILED FAILURES ---")
             for failure in smt_test_failures_details_H2I:
                 print(f"  Ω={failure['omega']}: FAILED Property '{failure['property']}' (Expected: {failure['expected_to_hold']})")
                 print(f"    Observed: {failure['observed_holds']}, Message: {failure['message']}")
                 if failure['counterexample_witness']:
                     print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    else:
        print("\n🤷🤷🤷 No H2I tests were run or results meaningfully processed. Check script and output. 🤷🤷🤷")