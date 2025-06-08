from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE,
                             Iff)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Symbolic Core AVCA Definitions (from AVCA_CORE_7_ext1.py) ---
Omega_py: int = 0

def create_symbolic_avc_val(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], omega_smt_node: FNode) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], omega_smt_node))
    ]
    if Omega_py == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    both_zs = And(avc1["is_zero"], avc2["is_zero"])
    both_as = And(avc1["is_areo"], avc2["is_areo"])
    unio_cross_equiv1 = And(avc1["is_zero"], avc2["is_areo"])
    unio_cross_equiv2 = And(avc1["is_areo"], avc2["is_zero"])
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_zs, both_as, unio_cross_equiv1, unio_cross_equiv2, both_fp_equal_val)

# --- SMT Logic Builders (from AVCA_CORE_7_ext1.py, ensure these are the definitive versions) ---
def avc_add_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])
    case1_a_is_unio = Implies(a_is_unio, And(Iff(res["is_zero"], b["is_zero"]), Iff(res["is_areo"], b["is_areo"]), Iff(res["is_finite"], b["is_finite"]), Equals(res["val"], b["val"])))
    case2_b_is_unio = Implies(And(Not(a_is_unio), b_is_unio), And(Iff(res["is_zero"], a["is_zero"]), Iff(res["is_areo"], a["is_areo"]), Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"])))
    sum_val = a["val"] + b["val"]
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_FP_sum_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], sum_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(sum_val < omega_smt_node, res_is_FP_sum_formula, res_is_ZU_formula))
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

def avc_sub_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    case1_b_is_unio = Implies(b_is_unio, And(Iff(res["is_zero"], a["is_zero"]), Iff(res["is_areo"], a["is_areo"]), Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"])))
    case2_a_is_unio_b_is_dfi = Implies(And(a_is_unio, b["is_finite"]), res_is_AU_formula)
    diff_val = a["val"] - b["val"]
    res_is_FP_diff_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], diff_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(a["val"] > b["val"], res_is_FP_diff_formula, res_is_AU_formula))
    return And(case1_b_is_unio, case2_a_is_unio_b_is_dfi, case3_dfi_dfi)

def avc_mul_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
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

def avc_div_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])
    case1_a_is_unio = Implies(a_is_unio, Ite(a["is_zero"], res_is_ZU_formula, res_is_AU_formula))
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b_is_unio), res_is_AU_formula)
    q_sym = Symbol(f"{res['name']}_q_div", SMT_INT_TYPE); r_sym = Symbol(f"{res['name']}_r_div", SMT_INT_TYPE)
    div_constraints = Implies(And(b["is_finite"], b["val"] > Int(0)), And(Equals(a["val"], q_sym * b["val"] + r_sym), r_sym >= Int(0), r_sym < b["val"]))
    valid_dfi_quotient_cond = Implies(b["is_finite"], And(Equals(r_sym, Int(0)), q_sym >= Int(1), q_sym < omega_smt_node))
    res_is_FP_quot_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), And(div_constraints, Ite(valid_dfi_quotient_cond, res_is_FP_quot_formula, res_is_AU_formula)))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi)

# --- Symbolic Prover Function (from AVCA_CORE_7_ext1.py) ---
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
    inputs_reprs: List[Dict[str, FNode]], # For counterexample display
    expect_property_to_hold: bool,
    is_existential: bool = False):

    global Omega_py
    Omega_py = omega_py_val
    initialize_smt_omega_results(omega_py_val)

    property_holds_observed = False
    counterexample_witness_str = None

    with Solver(name="z3") as s:
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)

        if is_existential:
            # For existential: ForAll inputs_reprs (implicitly by setup), Exists (other free vars in property_to_verify)
            # We want to see if property_to_verify can be SAT.
            s.add_assertion(property_to_verify)
            if s.solve():
                property_holds_observed = True
                model = s.get_model()
                ce_parts = []
                for repr_dict in inputs_reprs: # Display all named inputs
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero']); is_a = model.get_value(repr_dict['is_areo']); is_f = model.get_value(repr_dict['is_finite']); val_smt = model.get_value(repr_dict['val'])
                        state_str = "ZS" if is_z.is_true() else ("AS" if is_a.is_true() else (f"Fp({val_smt})" if is_f.is_true() else "Unknown"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: ce_parts.append(f"{name}=?") # If symbol not in model
                counterexample_witness_str = "; ".join(ce_parts)
            else: # property_to_verify is UNSAT
                property_holds_observed = False
        else: # Universal property
            # We want to see if property_to_verify is universally true.
            # So, we ask the solver if its negation Not(property_to_verify) is satisfiable.
            s.add_assertion(Not(property_to_verify))
            if not s.solve(): # Not(property_to_verify) is UNSAT
                property_holds_observed = True # Means property_to_verify is always TRUE
            else: # Not(property_to_verify) is SAT (counterexample to property_to_verify found)
                property_holds_observed = False
                model = s.get_model()
                ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero']); is_a = model.get_value(repr_dict['is_areo']); is_f = model.get_value(repr_dict['is_finite']); val_smt = model.get_value(repr_dict['val'])
                        state_str = "ZS" if is_z.is_true() else ("AS" if is_a.is_true() else (f"Fp({val_smt})" if is_f.is_true() else "Unknown"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts)

    success_for_summary = (property_holds_observed == expect_property_to_hold)
    status_emoji = "✅" if success_for_summary else "❌"
    final_message = ""

    if is_existential:
        if expect_property_to_hold: final_message = "Existence PROVED (witness found)." if property_holds_observed else "Existence FAILED (no witness found when one was expected)."
        else: final_message = "Non-existence CONFIRMED (no witness found)." if not property_holds_observed else "Non-existence FAILED (witness found when none was expected)."
    else: # Universal
        if expect_property_to_hold: final_message = "Property PROVED universally as expected." if property_holds_observed else "Property FAILED (counterexample found when expected to hold)."
        else: final_message = "Property correctly demonstrated NON-UNIVERSALITY (counterexample found as expected)." if not property_holds_observed else "Property INCORRECTLY held universally (expected non-universality/counterexample)."

    if success_for_summary: smt_test_results_summary[omega_py_val]["passed"] += 1
    else:
        smt_test_results_summary[omega_py_val]["failed"] += 1
        smt_test_failures_details.append({
            "property": property_name, "omega": omega_py_val, "is_existential": is_existential,
            "expectation_met": success_for_summary, "property_holds_observed_or_witness_found": property_holds_observed,
            "expected_to_hold_or_witness_exist": expect_property_to_hold, "message": final_message,
            "counterexample_witness": counterexample_witness_str
        })

    print(f"{status_emoji} Omega={omega_py_val}: Property '{property_name}' (Expect P to hold/witness exist: {expect_property_to_hold}) - {final_message}")
    if counterexample_witness_str:
        label = "Witness" if (is_existential and property_holds_observed and expect_property_to_hold) else \
                ("Counterexample" if (not is_existential and not property_holds_observed and expect_property_to_hold) else \
                 ("Confirming CE for Non-Universality" if (not is_existential and not property_holds_observed and not expect_property_to_hold) else \
                  ("Unexpected Witness" if (is_existential and not expect_property_to_hold and property_holds_observed) else \
                   ("Unexpected Counterexample" if (not is_existential and expect_property_to_hold and not property_holds_observed) else "Debug Info"))))
        print(f"    {label}: {counterexample_witness_str}")


# --- SMT Test Function Implementations for Experiment A ---

def smt_test_A1_totality_all_ops(omega_val_py: int):
    property_name_base = "SMT A.1: Operation Totality"
    omega_smt_node = Int(omega_val_py)
    
    ops_logic_map = {
        "Add": avc_add_smt_logic, "Sub": avc_sub_smt_logic,
        "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic
    }
    
    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a_sym = create_symbolic_avc_val(f"a_tot_{op_name_str}_{omega_val_py}")
        b_sym = create_symbolic_avc_val(f"b_tot_{op_name_str}_{omega_val_py}")
        res_sym = create_symbolic_avc_val(f"res_tot_{op_name_str}_{omega_val_py}")

        setup_tot = get_base_avc_constraints(a_sym, omega_smt_node) + \
                    get_base_avc_constraints(b_sym, omega_smt_node)
        
        setup_tot.append(op_logic_func(a_sym, b_sym, res_sym, omega_smt_node))
        
        res_constraints_tot = get_base_avc_constraints(res_sym, omega_smt_node)
        property_res_is_valid_tot = And(res_constraints_tot)

        prove_or_find_counterexample_smt(
            current_property_name, omega_val_py, setup_tot,
            property_res_is_valid_tot, [a_sym, b_sym, res_sym], 
            expect_property_to_hold=True, is_existential=False # Totality is a ForAll property
        )

def smt_test_A2_well_definedness_all_ops(omega_val_py: int):
    property_name_base = "SMT A.2: Well-Definedness w.r.t. Unio Equivalence"
    omega_smt_node = Int(omega_val_py)

    ops_logic_map = {
        "Add": avc_add_smt_logic, "Sub": avc_sub_smt_logic,
        "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic
    }

    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a1 = create_symbolic_avc_val(f"a1_wd_{op_name_str}_{omega_val_py}")
        a2 = create_symbolic_avc_val(f"a2_wd_{op_name_str}_{omega_val_py}")
        b1 = create_symbolic_avc_val(f"b1_wd_{op_name_str}_{omega_val_py}")
        b2 = create_symbolic_avc_val(f"b2_wd_{op_name_str}_{omega_val_py}")
        res1 = create_symbolic_avc_val(f"res1_wd_{op_name_str}_{omega_val_py}")
        res2 = create_symbolic_avc_val(f"res2_wd_{op_name_str}_{omega_val_py}")

        setup_wd = get_base_avc_constraints(a1, omega_smt_node) + \
                   get_base_avc_constraints(a2, omega_smt_node) + \
                   get_base_avc_constraints(b1, omega_smt_node) + \
                   get_base_avc_constraints(b2, omega_smt_node) + \
                   get_base_avc_constraints(res1, omega_smt_node) + \
                   get_base_avc_constraints(res2, omega_smt_node)

        # Define operations
        setup_wd.append(op_logic_func(a1, b1, res1, omega_smt_node))
        setup_wd.append(op_logic_func(a2, b2, res2, omega_smt_node))

        # Property: If a1~a2 AND b1~b2 THEN res1~res2
        premise = And(avc_equiv_smt(a1, a2), avc_equiv_smt(b1, b2))
        conclusion = avc_equiv_smt(res1, res2)
        property_well_defined = Implies(premise, conclusion)
        
        prove_or_find_counterexample_smt(
            current_property_name, omega_val_py, setup_wd,
            property_well_defined, [a1,a2,b1,b2,res1,res2],
            expect_property_to_hold=True, is_existential=False
        )

# --- Main SMT Test Execution ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] # Representative Omega values
    print(f"\n\n{'='*30} SMT EXPERIMENT A: FOUNDATIONAL INTEGRITY TESTS {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val # Set global Python Omega for get_base_avc_constraints context
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        print("\n--- Testing A.1: Operational Totality ---")
        smt_test_A1_totality_all_ops(current_omega_py_val)
        
        print("\n--- Testing A.2: Well-Definedness w.r.t. Unio Equivalence ---")
        smt_test_A2_well_definedness_all_ops(current_omega_py_val)
        
        print(f"\nSMT Summary for Omega={current_omega_py_val}: Passed={smt_test_results_summary[current_omega_py_val]['passed']}, Failed={smt_test_results_summary[current_omega_py_val]['failed']}")
        print(f"{'='*60}")

    # Overall summary printing (same as in AVCA_CORE_7_ext1.py)
    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY (EXPERIMENT A) {'='*30}")
    total_passed_smt_all = 0; total_failed_smt_all = 0
    for ov_summary, results in smt_test_results_summary.items():
        total_passed_smt_all += results['passed']; total_failed_smt_all += results['failed']
        print(f"Omega={ov_summary}: Passed={results['passed']}, Failed={results['failed']}")
    if smt_test_failures_details:
        print("\n--- SMT DETAILED FAILURES (EXPERIMENT A) ---")
        for failure in smt_test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}' (Expect P to hold/witness exist: {failure['expected_to_hold_or_witness_exist']})")
            print(f"    Observed P held/witness found: {failure['property_holds_observed_or_witness_found']}")
            print(f"    Message: {failure['message']}")
            if failure['counterexample_witness']: print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")
    if total_failed_smt_all == 0 and total_passed_smt_all > 0 : print("\n🎉🎉🎉 ALL SMT FOUNDATIONAL INTEGRITY TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: print("\n🤷🤷🤷 NO SMT FOUNDATIONAL INTEGRITY TESTS WERE RUN / DEFINED. 🤷🤷🤷")
    else: print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT FOUNDATIONAL INTEGRITY TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")