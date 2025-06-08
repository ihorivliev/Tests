# Script H2I_Add_Isomorphism_Test.py
# Purpose: To test if the common addition operation (avc_add_v1.1)
#          is isomorphic with itself under an aspect-swapping map φ
#          for a given Omega. This tests if the semantic system is invariant
#          to a simple relabeling of ZU <-> AU, given fixed aspect outputs
#          like DFI additive overflow to AREO_UNIO.
# Test: φ(x ⊕_common y) = φ(x) ⊕_common φ(y)
# Expected: FAIL for Ω>=3 due to fixed AREO_UNIO overflow.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal
import math

# --- Global Omega Parameter & Test Results ---
_Omega_H2I_Add_Global_Context: int = 0 # Global for set_avca_omega, but functions will use passed param
smt_test_results_summary_H2I_Add: Dict[int, Dict[str, int]] = {}
smt_test_failures_details_H2I_Add: List[Dict[str, Any]] = []

# --- Unio Class Definition (Consistent with other H2I scripts) ---
class Unio_H2I_Add:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_H2I_Add aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_H2I_Add)
    def __hash__(self) -> int:
        return hash(type(self))
    def __repr__(self) -> str:
        return f"Unio_H2I_Add('{self.aspect}')"

ZERO_UNIO_H2I_Add = Unio_H2I_Add("zero")
AREO_UNIO_H2I_Add = Unio_H2I_Add("areo")
AVCVal_H2I_Add = Union[int, Unio_H2I_Add]

def set_avca_omega_h2i_add(omega_value: int, verbose: bool = False):
    global _Omega_H2I_Add_Global_Context
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_H2I_Add parameter must be an integer >= 1.")
    _Omega_H2I_Add_Global_Context = omega_value
    if verbose:
        print(f"H2I Add Isomorphism Test: Global Context Omega_H2I_Add set to {_Omega_H2I_Add_Global_Context}")

# --- SMT Symbolic Representation and Base Constraints (Consistent) ---
def create_symbolic_avc_val_h2i_add(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_ZA_h2ia", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_AA_h2ia", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_DFI_h2ia", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_h2ia", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints_h2i_add(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], Int(0)))
    ]
    if current_omega_py == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_deep_equals_smt_h2i_add(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    return And(
        Iff(avc1["is_zero_aspect"], avc2["is_zero_aspect"]),
        Iff(avc1["is_areo_aspect"], avc2["is_areo_aspect"]),
        Iff(avc1["is_finite"], avc2["is_finite"]),
        Implies(avc1["is_finite"], Equals(avc1["val"], avc2["val"]))
    )

# --- SMT Logic Builder for Addition (avc_add_v1.1 logic) ---
def avc_add_smt_logic_v11_H2I_Add(a: Dict[str, FNode], b: Dict[str, FNode],
                                  res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # This is the standard avc_add_v1.1 SMT logic
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])

    res_becomes_a_state = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), 
                              Iff(res["is_areo_aspect"], a["is_areo_aspect"]), 
                              Iff(res["is_finite"], a["is_finite"]), 
                              Equals(res["val"], a["val"])) # val only matters if DFI, but for U it's 0
    
    res_becomes_b_state = And(Iff(res["is_zero_aspect"], b["is_zero_aspect"]), 
                              Iff(res["is_areo_aspect"], b["is_areo_aspect"]), 
                              Iff(res["is_finite"], b["is_finite"]), 
                              Equals(res["val"], b["val"]))

    case1_a_is_unio = Implies(a_is_unio, res_becomes_b_state)
    case2_b_is_unio_a_is_dfi = Implies(And(Not(a_is_unio), b_is_unio), res_becomes_a_state) # a must be DFI here
    
    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    symbolic_sum_val = Plus(a["val"], b["val"])
    
    res_is_dfi_sum_state = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), Equals(res["val"], symbolic_sum_val))
    res_is_areo_unio_state = And(res["is_areo_aspect"], Not(res["is_zero_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0))) # Overflow to AU
    
    case3_dfi_dfi_logic = Implies(cond_both_are_dfi, Ite(symbolic_sum_val < omega_smt_node, res_is_dfi_sum_state, res_is_areo_unio_state))
    
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi_logic)

# --- SMT Logic for φ (Phi) Map (Consistent with H2I_Mul) ---
def apply_phi_map_smt_h2i_add(input_avc: Dict[str, FNode], output_avc: Dict[str, FNode]) -> FNode:
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

# --- SMT Prover Function (Consistent with H2I_Mul) ---
def initialize_smt_omega_results_h2i_add(current_omega_py: int):
    if current_omega_py not in smt_test_results_summary_H2I_Add:
        smt_test_results_summary_H2I_Add[current_omega_py] = {"passed": 0, "failed": 0, "skipped": 0}

def prove_or_find_counterexample_smt_h2i_add(
    property_name: str, current_omega_py: int, 
    setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    
    initialize_smt_omega_results_h2i_add(current_omega_py)
    property_holds_observed = False
    counterexample_witness_str = None
    
    with Solver(name="z3", logic="LIA") as s: # Use LIA for integer arithmetic
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)
        
        target_assertion = property_to_verify if is_existential else Not(property_to_verify)
        s.add_assertion(target_assertion)
        solve_result = s.solve()

        if is_existential: property_holds_observed = solve_result
        else: property_holds_observed = not solve_result

        if solve_result and ( (not property_holds_observed and not is_existential) or \
                              (property_holds_observed and is_existential and not expect_property_to_hold) or \
                              (not property_holds_observed and not is_existential and not expect_property_to_hold) or \
                              (property_holds_observed and is_existential and expect_property_to_hold) ):
            model = s.get_model(); ce_parts = []
            for repr_dict in inputs_reprs:
                name = repr_dict['name']
                try:
                    is_z = model.get_value(repr_dict['is_zero_aspect']).is_true()
                    is_a = model.get_value(repr_dict['is_areo_aspect']).is_true()
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
        else: final_message = "Property NON-UNIVERSALITY confirmed (counterexample found)." if not property_holds_observed else "Property INCORRECTLY held universally."

    if success_for_summary: smt_test_results_summary_H2I_Add[current_omega_py]["passed"] += 1
    else:
        smt_test_results_summary_H2I_Add[current_omega_py]["failed"] += 1
        smt_test_failures_details_H2I_Add.append({
            "property": property_name, "omega": current_omega_py,
            "expectation_met": success_for_summary,
            "observed_holds": property_holds_observed,
            "expected_to_hold": expect_property_to_hold,
            "message": final_message,
            "counterexample_witness": counterexample_witness_str
        })

    print(f"{status_emoji} Ω={current_omega_py}: {property_name} (Expect Isomorphism: {expect_property_to_hold}) - {final_message}")
    if counterexample_witness_str:
        label = "Witness" if is_existential and property_holds_observed and expect_property_to_hold else "Counterexample"
        print(f"    {label}: {counterexample_witness_str}")


def check_isomorphism_for_addition_H2I_Add(current_omega_py: int):
    op_name_str = "⊕_common(v1.1)"
    # The SMT logic for addition is the same for both "conceptual" kernels AD and ZD
    common_add_smt_logic = avc_add_smt_logic_v11_H2I_Add
    
    test_name = f"H2I: Isomorphism φ(x {op_name_str} y) = φ(x) {op_name_str} φ(y) for Ω={current_omega_py}"
    initialize_smt_omega_results_h2i_add(current_omega_py)

    omega_smt_node = Int(current_omega_py)
    x = create_symbolic_avc_val_h2i_add("x_iso_add")
    y = create_symbolic_avc_val_h2i_add("y_iso_add")

    # LHS
    res_common_internal = create_symbolic_avc_val_h2i_add("res_common_internal_add")
    lhs_mapped = create_symbolic_avc_val_h2i_add("lhs_mapped_add")

    # RHS
    phi_x = create_symbolic_avc_val_h2i_add("phi_x_add")
    phi_y = create_symbolic_avc_val_h2i_add("phi_y_add")
    rhs_direct = create_symbolic_avc_val_h2i_add("rhs_direct_add")

    setup = (get_base_avc_constraints_h2i_add(x, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i_add(y, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i_add(res_common_internal, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i_add(lhs_mapped, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i_add(phi_x, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i_add(phi_y, omega_smt_node, current_omega_py) +
             get_base_avc_constraints_h2i_add(rhs_direct, omega_smt_node, current_omega_py)
            )

    # Calculate LHS: φ(x ⊕_common y)
    setup.append(common_add_smt_logic(x, y, res_common_internal, omega_smt_node))
    setup.append(apply_phi_map_smt_h2i_add(res_common_internal, lhs_mapped))

    # Calculate RHS: φ(x) ⊕_common φ(y)
    setup.append(apply_phi_map_smt_h2i_add(x, phi_x))
    setup.append(apply_phi_map_smt_h2i_add(y, phi_y))
    setup.append(common_add_smt_logic(phi_x, phi_y, rhs_direct, omega_smt_node))

    property_formula = avc_deep_equals_smt_h2i_add(lhs_mapped, rhs_direct)
    
    # EXPECTATION: Isomorphism should FAIL for addition if Ω >= 3 due to fixed AREO_UNIO overflow.
    # For Ω <= 2, addition is associative and behavior might be simple enough for isomorphism to hold.
    # Let's test Ω=3 where we expect failure. For Ω=2, it might hold.
    expected_isomorphism_add = (current_omega_py <= 2) 
    
    prove_or_find_counterexample_smt_h2i_add(
        test_name, 
        current_omega_py, 
        setup, 
        property_formula, 
        [x, y, res_common_internal, lhs_mapped, phi_x, phi_y, rhs_direct], 
        expect_property_to_hold=expected_isomorphism_add, 
        is_existential=False
    )

# --- Main Execution ---
if __name__ == "__main__":
    omegas_to_test_h2i_add = [2, 3] # Test Ω=2 (expect hold) and Ω=3 (expect fail)
    
    for omega_val in omegas_to_test_h2i_add:
        set_avca_omega_h2i_add(omega_val, verbose=True)
        current_test_run_name_h2i_add = f"H2I: Addition Isomorphism (Ω={omega_val})"
        print(f"\n{'='*30} SMT Test for {current_test_run_name_h2i_add} {'='*30}")
        check_isomorphism_for_addition_H2I_Add(current_omega_py=omega_val)

    # --- Summarize ---
    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY (H2I Addition Isomorphism) {'='*30}")
    total_passed_overall = 0
    total_failed_overall = 0
    if not smt_test_results_summary_H2I_Add:
        print("No SMT test results recorded.")
    else:
        for ov_summary, results in smt_test_results_summary_H2I_Add.items():
            passed = results.get('passed',0)
            failed = results.get('failed',0)
            total_passed_overall += passed
            total_failed_overall += failed
            print(f"Omega={ov_summary}: Passed={passed}, Failed={failed}")
    
    if smt_test_failures_details_H2I_Add:
         print("\n--- H2I Addition Isomorphism Test DETAILED FAILURES/NON-UNIVERSALITIES ---")
         for failure in smt_test_failures_details_H2I_Add:
             print(f"  Ω={failure['omega']}: Property '{failure['property']}' (Expected To Hold: {failure['expected_to_hold']})")
             print(f"    Observed Holds: {failure['observed_holds']}, Message: {failure['message']}")
             if failure['counterexample_witness']:
                 print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    
    print(f"\nTotal tests passed (matching expectation): {total_passed_overall}")
    print(f"Total tests failed (against expectation): {total_failed_overall}")
    print(f"{'='*70}")

    if total_failed_overall == 0 and total_passed_overall > 0:
        print("\n🎉🎉🎉 All H2I Addition Isomorphism tests behaved AS EXPECTED! 🎉🎉🎉")
    elif total_failed_overall > 0:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ Some H2I Addition Isomorphism tests FAILED AGAINST EXPECTATION. ⚠️⚠️⚠️")
    else:
        print("\n🤷🤷🤷 No H2I Addition Isomorphism tests were run or results meaningfully processed. 🤷🤷🤷")