from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Symbolic Core AVCA Definitions (from Revised Core AVCA Manuscript Draft1) ---
# These are the SMT translations of the Python specification.

Omega_py: int = 0 # Global Python Omega, set by the main test loop for each Omega scenario

def create_symbolic_avc_val(name_prefix: str) -> Dict[str, FNode]:
    """Creates symbolic components for an AVCVal."""
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], omega_smt_node: FNode) -> List[FNode]:
    """Basic constraints for a well-formed symbolic AVCVal for a given Omega."""
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))), # Convention for ZS val
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], omega_smt_node)) # Convention for AS val
    ]
    if Omega_py == 1: 
        constraints.append(Not(avc_repr["is_finite"])) # No DFI elements if Omega_py is 1
    return constraints

def avc_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    """SMT formula for equivalence of two symbolic AVCVals (Unio ZS ~ AS)."""
    both_zs = And(avc1["is_zero"], avc2["is_zero"])
    both_as = And(avc1["is_areo"], avc2["is_areo"])
    unio_cross_equiv1 = And(avc1["is_zero"], avc2["is_areo"])
    unio_cross_equiv2 = And(avc1["is_areo"], avc2["is_zero"])
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_zs, both_as, unio_cross_equiv1, unio_cross_equiv2, both_fp_equal_val)

# --- Symbolic Operation Logic Builders (Based on "Revised Core AVCA" Python) ---
# These are the SMT versions of avc_add, avc_sub, avc_mul, avc_div Python functions.

def avc_add_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])
    case1_a_is_unio = Implies(a_is_unio, And(Iff(res["is_zero"], b["is_zero"]), Iff(res["is_areo"], b["is_areo"]), Iff(res["is_finite"], b["is_finite"]), Equals(res["val"], b["val"])))
    case2_b_is_unio = Implies(And(Not(a_is_unio), b_is_unio), And(Iff(res["is_zero"], a["is_zero"]), Iff(res["is_areo"], a["is_areo"]), Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"])))
    sum_val = a["val"] + b["val"]
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_FP_sum_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], sum_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(sum_val < omega_smt_node, res_is_FP_sum_formula, res_is_ZU_formula))
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

def avc_sub_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    case1_b_is_unio = Implies(b_is_unio, And(Iff(res["is_zero"], a["is_zero"]), Iff(res["is_areo"], a["is_areo"]), Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"])))
    case2_a_is_unio_b_is_dfi = Implies(And(a_is_unio, b["is_finite"]), res_is_AU_formula)
    diff_val = a["val"] - b["val"]
    res_is_FP_diff_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], diff_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(a["val"] > b["val"], res_is_FP_diff_formula, res_is_AU_formula))
    return And(case1_b_is_unio, case2_a_is_unio_b_is_dfi, case3_dfi_dfi)

def avc_mul_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])
    case1_a_is_unio = Implies(a_is_unio, Ite(a["is_zero"], res_is_ZU_formula, res_is_AU_formula))
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b_is_unio), Ite(b["is_zero"], res_is_ZU_formula, res_is_AU_formula))
    prod_val = a["val"] * b["val"]
    res_is_FP_prod_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], prod_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), res_is_FP_prod_formula, res_is_AU_formula))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi)

def avc_div_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])
    case1_a_is_unio = Implies(a_is_unio, Ite(a["is_zero"], res_is_ZU_formula, res_is_AU_formula))
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b_is_unio), res_is_AU_formula)
    q_sym = Symbol(f"{res['name']}_q_div", SMT_INT_TYPE) 
    r_sym = Symbol(f"{res['name']}_r_div", SMT_INT_TYPE)
    div_constraints = Implies(And(b["is_finite"], b["val"] > Int(0)), And(Equals(a["val"], q_sym * b["val"] + r_sym), r_sym >= Int(0), r_sym < b["val"])) 
    valid_dfi_quotient_cond = Implies(b["is_finite"], And(Equals(r_sym, Int(0)), q_sym >= Int(1), q_sym < omega_smt_node))
    res_is_FP_quot_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), And(div_constraints, Ite(valid_dfi_quotient_cond, res_is_FP_quot_formula, res_is_AU_formula)))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi)

# --- SMT Prover Function (Reusable Harness) ---
smt_test_results_summary: Dict[int, Dict[str, int]] = {}
smt_test_failures_details: List[Dict[str, Any]] = []

def initialize_smt_omega_results(omega_val: int):
    if omega_val not in smt_test_results_summary:
        smt_test_results_summary[omega_val] = {"passed": 0, "failed": 0}

def prove_or_find_counterexample_smt(
    property_name: str, 
    omega_py_val: int, 
    setup_formulas: List[FNode], 
    property_to_verify: FNode, 
    inputs_reprs: List[Dict[str, FNode]],
    expect_property_to_hold: bool,
    is_existential: bool = False):
    
    global Omega_py # Set global Python Omega for get_base_avc_constraints context
    Omega_py = omega_py_val 
    initialize_smt_omega_results(omega_py_val)

    property_holds_observed = False 
    counterexample_witness_str = None

    with Solver(name="z3") as s: 
        for f_setup in setup_formulas: 
            s.add_assertion(f_setup)
        
        if is_existential:
            s.add_assertion(property_to_verify) 
            if s.solve():
                property_holds_observed = True
                model = s.get_model()
                ce_parts = [] 
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero'])
                        is_a = model.get_value(repr_dict['is_areo'])
                        is_f = model.get_value(repr_dict['is_finite'])
                        val_smt = model.get_value(repr_dict['val'])
                        state_str = "ZS" if is_z.is_true() else ("AS" if is_a.is_true() else (f"Fp({val_smt})" if is_f.is_true() else "UnknownState"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: 
                        ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts)
            else:
                property_holds_observed = False
        else: # Universal property 
            s.add_assertion(Not(property_to_verify)) 
            if not s.solve(): 
                property_holds_observed = True 
            else: 
                property_holds_observed = False
                model = s.get_model()
                ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero'])
                        is_a = model.get_value(repr_dict['is_areo'])
                        is_f = model.get_value(repr_dict['is_finite'])
                        val_smt = model.get_value(repr_dict['val'])
                        state_str = "ZS" if is_z.is_true() else ("AS" if is_a.is_true() else (f"Fp({val_smt})" if is_f.is_true() else "UnknownState"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: 
                        ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts)
    
    success_for_summary = (property_holds_observed == expect_property_to_hold)
    status_emoji = "✅" if success_for_summary else "❌"
    final_message = ""

    if is_existential:
        final_message = "Existence PROVED (witness found)." if property_holds_observed else "Existence FAILED (no witness found when one was expected)."
    else: # Universal
        final_message = "Property PROVED universally as expected." if property_holds_observed else "Property FAILED (counterexample found when expected to hold)."

    if success_for_summary:
        smt_test_results_summary[omega_py_val]["passed"] += 1
    else:
        smt_test_results_summary[omega_py_val]["failed"] += 1
        smt_test_failures_details.append({
            "property": property_name, "omega": omega_py_val, "is_existential": is_existential,
            "expectation_met": success_for_summary,
            "property_holds_observed_or_witness_found": property_holds_observed,
            "expected_to_hold_or_witness_exist": expect_property_to_hold,
            "message": final_message,
            "counterexample_witness": counterexample_witness_str
        })

    print(f"{status_emoji} Omega={omega_py_val}: Property '{property_name}' (Expected: {expect_property_to_hold}) - {final_message}")
    if counterexample_witness_str and (not success_for_summary or (not expect_property_to_hold and not property_holds_observed)): 
        print(f"    Counterexample/Witness: {counterexample_witness_str}")


# --- Test Constants (Symbolic Representations of ZERO_UNIO and AREO_UNIO) ---
# These are fixed symbolic values for the Unio aspects that we will constrain
# in the setup_formulas for each test.
# This makes it easier to refer to ZS_C and AS_C in tests.
ZU_const = create_symbolic_avc_val("ZU_const")
AS_const = create_symbolic_avc_val("AS_const")

# Constraints to make ZU_const and AS_const represent actual ZERO_UNIO and AREO_UNIO
# These must be added to the setup_formulas for tests using them.
def get_unio_const_constraints(omega_smt_node: FNode) -> List[FNode]:
    return [
        ZU_const["is_zero"], Not(ZU_const["is_areo"]), Not(ZU_const["is_finite"]), Equals(ZU_const["val"], Int(0)),
        Not(AS_const["is_zero"]), AS_const["is_areo"], Not(AS_const["is_finite"]), Equals(AS_const["val"], omega_smt_node)
    ]

# --- Experiment 1.1: PySMT Formal Verification of Unio's Operational Profile ---

def smt_unio_operational_profile(omega_val_py: int):
    omega_smt_node = Int(omega_val_py)
    
    # Symbolic variable for X, representing ANY element in S_Omega
    x = create_symbolic_avc_val("x_any")
    
    # Create symbolic results for various interactions
    res_zu_op_x_add = create_symbolic_avc_val("res_ZU_X_add")
    res_as_op_x_add = create_symbolic_avc_val("res_AS_X_add")
    res_x_op_zu_add = create_symbolic_avc_val("res_X_ZU_add")
    res_x_op_as_add = create_symbolic_avc_val("res_X_AS_add")

    res_zu_op_x_sub = create_symbolic_avc_val("res_ZU_X_sub")
    res_as_op_x_sub = create_symbolic_avc_val("res_AS_X_sub")
    res_x_op_zu_sub = create_symbolic_avc_val("res_X_ZU_sub")
    res_x_op_as_sub = create_symbolic_avc_val("res_X_AS_sub")

    res_zu_op_x_mul = create_symbolic_avc_val("res_ZU_X_mul")
    res_as_op_x_mul = create_symbolic_avc_val("res_AS_X_mul")
    res_x_op_zu_mul = create_symbolic_avc_val("res_X_ZU_mul")
    res_x_op_as_mul = create_symbolic_avc_val("res_X_AS_mul")

    res_zu_op_x_div = create_symbolic_avc_val("res_ZU_X_div")
    res_as_op_x_div = create_symbolic_avc_val("res_AS_X_div")
    res_x_op_zu_div = create_symbolic_avc_val("res_X_ZU_div")
    res_x_op_as_div = create_symbolic_avc_val("res_X_AS_div")

    # Initial setup for all variables and constants
    setup = get_base_avc_constraints(x, omega_smt_node) + \
            get_base_avc_constraints(ZU_const, omega_smt_node) + \
            get_base_avc_constraints(AS_const, omega_smt_node) + \
            get_unio_const_constraints(omega_smt_node) # Constrain ZU_const, AS_const

    # Add SMT logic for each operation
    setup.append(avc_add_smt_logic(ZU_const, x, res_zu_op_x_add, omega_smt_node))
    setup.append(avc_add_smt_logic(AS_const, x, res_as_op_x_add, omega_smt_node))
    setup.append(avc_add_smt_logic(x, ZU_const, res_x_op_zu_add, omega_smt_node))
    setup.append(avc_add_smt_logic(x, AS_const, res_x_op_as_add, omega_smt_node))

    setup.append(avc_sub_smt_logic(ZU_const, x, res_zu_op_x_sub, omega_smt_node))
    setup.append(avc_sub_smt_logic(AS_const, x, res_as_op_x_sub, omega_smt_node))
    setup.append(avc_sub_smt_logic(x, ZU_const, res_x_op_zu_sub, omega_smt_node))
    setup.append(avc_sub_smt_logic(x, AS_const, res_x_op_as_sub, omega_smt_node))

    setup.append(avc_mul_smt_logic(ZU_const, x, res_zu_op_x_mul, omega_smt_node))
    setup.append(avc_mul_smt_logic(AS_const, x, res_as_op_x_mul, omega_smt_node))
    setup.append(avc_mul_smt_logic(x, ZU_const, res_x_op_zu_mul, omega_smt_node))
    setup.append(avc_mul_smt_logic(x, AS_const, res_x_op_as_mul, omega_smt_node))

    setup.append(avc_div_smt_logic(ZU_const, x, res_zu_op_x_div, omega_smt_node))
    setup.append(avc_div_smt_logic(AS_const, x, res_as_op_x_div, omega_smt_node))
    setup.append(avc_div_smt_logic(x, ZU_const, res_x_op_zu_div, omega_smt_node))
    setup.append(avc_div_smt_logic(x, AS_const, res_x_op_as_div, omega_smt_node))


    # --- Properties to Verify (based on Revised Core AVCA spec and previous Python output) ---

    # 1. Addition (Unio is perfect identity)
    prop_add_unio_is_identity = And(
        avc_equiv_smt(res_zu_op_x_add, x), # ZU + X = X
        avc_equiv_smt(res_as_op_x_add, x), # AS + X = X (crucial Unio-Dilemma resolution)
        avc_equiv_smt(res_x_op_zu_add, x), # X + ZU = X
        avc_equiv_smt(res_x_op_as_add, x)  # X + AS = X
    )
    prove_or_find_counterexample_smt(f"Unio Operational Profile: ADDITION (Unio is Identity)", 
                                     omega_val_py, setup, prop_add_unio_is_identity, 
                                     [x, ZU_const, AS_const], expect_property_to_hold=True)

    # 2. Subtraction (Unio is asymmetric: subtrahend identity, minuend absorption)
    prop_sub_unio_profile = And(
        avc_equiv_smt(res_x_op_zu_sub, x),  # X - ZU = X
        avc_equiv_smt(res_x_op_as_sub, x),  # X - AS = X
        # For Unio as minuend, result is AREO_UNIO.
        # This requires x to be a DFI element for this case.
        # So, we test: IF x is DFI, THEN ZU - x = AS and AS - x = AS.
        Implies(x["is_finite"], And(avc_equiv_smt(res_zu_op_x_sub, AS_const), 
                                    avc_equiv_smt(res_as_op_x_sub, AS_const)))
    )
    prove_or_find_counterexample_smt(f"Unio Operational Profile: SUBTRACTION (Asymmetric)", 
                                     omega_val_py, setup, prop_sub_unio_profile, 
                                     [x, ZU_const, AS_const], expect_property_to_hold=True)

    # 3. Multiplication (Aspect-dependent Annihilator/Absorber)
    prop_mul_unio_profile = And(
        # ZU is annihilator
        avc_equiv_smt(res_zu_op_x_mul, ZU_const), # ZU * X = ZU
        avc_equiv_smt(res_x_op_zu_mul, ZU_const), # X * ZU = ZU
        # AS is absorber (unless ZU involved, which ZU dominates)
        # So, if X is not ZU_const, AS*X=AS, X*AS=AS.
        Implies(Not(avc_equiv_smt(x, ZU_const)), And(avc_equiv_smt(res_as_op_x_mul, AS_const), 
                                                    avc_equiv_smt(res_x_op_as_mul, AS_const)))
    )
    prove_or_find_counterexample_smt(f"Unio Operational Profile: MULTIPLICATION (Aspect-Dependent)", 
                                     omega_val_py, setup, prop_mul_unio_profile, 
                                     [x, ZU_const, AS_const], expect_property_to_hold=True)

    # 4. Division (Aspect-dependent Dividend, Collapsing Divisor)
    prop_div_unio_profile = And(
        # Unio as dividend preserves aspect
        avc_equiv_smt(res_zu_op_x_div, ZU_const), # ZU / X = ZU
        avc_equiv_smt(res_as_op_x_div, AS_const), # AS / X = AS
        # Unio as divisor leads to AS_const (collapse to Areo)
        # This requires X to be a DFI element for this case.
        Implies(x["is_finite"], And(avc_equiv_smt(res_x_op_zu_div, AS_const),
                                    avc_equiv_smt(res_x_op_as_div, AS_const)))
    )
    prove_or_find_counterexample_smt(f"Unio Operational Profile: DIVISION (Aspect-Dependent)", 
                                     omega_val_py, setup, prop_div_unio_profile, 
                                     [x, ZU_const, AS_const], expect_property_to_hold=True)


# --- Main SMT Test Execution ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] # Covering phase transitions and edge cases
    
    print(f"\n{'='*30} STARTING PySMT TESTS FOR UNIO'S OPERATIONAL PROFILE {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        # Omega_py is set globally within prove_or_find_counterexample_smt
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        
        # Run the SMT test for Unio's Operational Profile
        smt_unio_operational_profile(current_omega_py_val)
        
        print(f"\nSMT Summary for Omega={current_omega_py_val}: Passed={smt_test_results_summary[current_omega_py_val]['passed']}, Failed={smt_test_results_summary[current_omega_py_val]['failed']}")
        print(f"{'='*60}")

    # --- Overall Test Suite Summary ---
    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY {'='*30}")
    total_passed_smt_all = 0
    total_failed_smt_all = 0
    for omega_val, results in smt_test_results_summary.items():
        total_passed_smt_all += results['passed']
        total_failed_smt_all += results['failed']
        print(f"Omega={omega_val}: Passed={results['passed']}, Failed={results['failed']}")
    
    if smt_test_failures_details:
        print("\n--- SMT DETAILED FAILURES ---")
        for failure in smt_test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}' (Expected: {failure['expected_to_hold_or_witness_exist']})")
            print(f"    Observed: {failure['property_holds_observed_or_witness_found']}, Message: {failure['message']}")
            if failure['counterexample_witness']:
                 print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")

    if total_failed_smt_all == 0 and total_passed_smt_all > 0 :
        print("\n🎉🎉🎉 ALL SMT UNIO OPERATIONAL PROFILE TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: 
        print("\n🤷🤷🤷 NO SMT TESTS WERE EXECUTED FOR UNIO OPERATIONAL PROFILE. 🤷🤷🤷")
    else:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT UNIO OPERATIONAL PROFILE TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")