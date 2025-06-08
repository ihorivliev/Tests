from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE,
                             Iff)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Symbolic Core AVCA Definitions ---

# Global Python Omega, set for each test scenario to define constraints
Omega_py: int = 0 # This will be set by the main test loop

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
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], omega_smt_node))
    ]
    if Omega_py == 1: # Global Python Omega_py for context
        constraints.append(Not(avc_repr["is_finite"]))
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

def avc_add_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    case1 = Implies(a_is_unio, And(Iff(res["is_zero"], b["is_zero"]),
                                   Iff(res["is_areo"], b["is_areo"]),
                                   Iff(res["is_finite"], b["is_finite"]),
                                   Equals(res["val"], b["val"])))
    case2 = Implies(And(Not(a_is_unio), b_is_unio), 
                    And(Iff(res["is_zero"], a["is_zero"]),
                        Iff(res["is_areo"], a["is_areo"]),
                        Iff(res["is_finite"], a["is_finite"]),
                        Equals(res["val"], a["val"])))
    
    sum_val = a["val"] + b["val"]
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(sum_val < omega_smt_node,
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], sum_val)), 
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), 
                                    Equals(res["val"], Int(0))) 
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_sub_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                            Equals(res["val"], omega_smt_node))

    case1 = Implies(b_is_unio, And(Iff(res["is_zero"], a["is_zero"]),
                                   Iff(res["is_areo"], a["is_areo"]),
                                   Iff(res["is_finite"], a["is_finite"]),
                                   Equals(res["val"], a["val"])))
    case2 = Implies(And(a_is_unio, Not(b_is_unio)), res_is_AU_formula) # a is Unio, b is DFI
    
    diff_val = a["val"] - b["val"]
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(a["val"] > b["val"],
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], diff_val)), 
                                res_is_AU_formula 
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_mul_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))

    case1 = Implies(Or(a["is_zero"], a["is_areo"]), 
                    Ite(a["is_zero"], res_is_ZU_formula, res_is_AU_formula))
    
    case2 = Implies(And(a["is_finite"], Or(b["is_zero"], b["is_areo"])),
                    Ite(b["is_zero"], res_is_ZU_formula, res_is_AU_formula))
    
    prod_val = a["val"] * b["val"]
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), # DFI result must be > 0
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], prod_val)), 
                                res_is_AU_formula 
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_div_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))

    case1 = Implies(Or(a["is_zero"], a["is_areo"]), 
                    Ite(a["is_zero"], res_is_ZU_formula, res_is_AU_formula))

    case2 = Implies(And(a["is_finite"], Or(b["is_zero"], b["is_areo"])),
                    res_is_AU_formula)
    
    q_sym = Symbol(f"{res['name']}_q_div", SMT_INT_TYPE) 
    r_sym = Symbol(f"{res['name']}_r_div", SMT_INT_TYPE)

    # b["is_finite"] implies b["val"] > Int(0) due to get_base_avc_constraints
    div_constraints = Implies(b["is_finite"], # Only define q,r if divisor is DFI
                              And(Equals(a["val"], q_sym * b["val"] + r_sym),
                                  r_sym >= Int(0),
                                  r_sym < b["val"])) 
    
    valid_dfi_quotient_cond = Implies(b["is_finite"], # Only if b is DFI
                                      And(Equals(r_sym, Int(0)), 
                                          q_sym >= Int(1), 
                                          q_sym < omega_smt_node))

    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            And(div_constraints, 
                                Ite(valid_dfi_quotient_cond,
                                    And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                        Equals(res["val"], q_sym)), 
                                    res_is_AU_formula 
                                )
                            ))
    return And(case1, case2, case3_dfi_dfi)

# --- Symbolic Prover Function (Refined) ---
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
    expect_property_to_hold: bool):
    
    global Omega_py 
    Omega_py = omega_py_val 
    initialize_smt_omega_results(omega_py_val)

    property_holds_observed = False
    counterexample_str = None

    with Solver(name="z3") as s:
        for f_setup in setup_formulas: 
            s.add_assertion(f_setup)
        
        s.add_assertion(Not(property_to_verify))
        
        if not s.solve(): 
            property_holds_observed = True 
        else: 
            property_holds_observed = False
            model = s.get_model()
            ce_parts = []
            for avc_repr in inputs_reprs:
                name = avc_repr['name']
                try:
                    is_z = model.get_value(avc_repr['is_zero'])
                    is_a = model.get_value(avc_repr['is_areo'])
                    is_f = model.get_value(avc_repr['is_finite'])
                    val_smt = model.get_value(avc_repr['val'])
                    
                    state_str = "ZS" if is_z.is_true() else \
                                ("AS" if is_a.is_true() else \
                                 (f"Fp({val_smt})" if is_f.is_true() else "UnknownState"))
                    ce_parts.append(f"{name}={state_str}")
                except Exception:
                    ce_parts.append(f"{name}=?")
            counterexample_str = "; ".join(ce_parts)

    success_for_summary = (property_holds_observed == expect_property_to_hold)
    status_emoji = "✅" if success_for_summary else "❌"
    final_message = ""

    if expect_property_to_hold:
        final_message = "Property PROVED universally as expected." if property_holds_observed else "Property FAILED (counterexample found when expected to hold)."
    else: 
        final_message = "Property correctly demonstrated NON-UNIVERSALITY (counterexample found as expected)." if not property_holds_observed \
                        else "Property INCORRECTLY held universally (expected non-universality/counterexample)."

    if success_for_summary:
        smt_test_results_summary[omega_py_val]["passed"] += 1
    else:
        smt_test_results_summary[omega_py_val]["failed"] += 1
        smt_test_failures_details.append({
            "property": property_name, "omega": omega_py_val, 
            "expectation_met": success_for_summary,
            "property_held_observed": property_holds_observed,
            "expected_to_hold": expect_property_to_hold,
            "message": final_message,
            "counterexample": counterexample_str
        })

    print(f"{status_emoji} Omega={omega_py_val}: Property '{property_name}' (Expected to hold: {expect_property_to_hold}) - {final_message}")
    if counterexample_str and (not success_for_summary or (not expect_property_to_hold and not property_holds_observed)): 
        print(f"    Counterexample/Witness: {counterexample_str}")


# --- SMT Test Function Implementations ---

def smt_test_totality(omega_val_py: int):
    property_name = "SMT Operation Totality"
    omega_smt_node = Int(omega_val_py)
    
    ops_logic = {
        "Add": avc_add_smt_logic, "Sub": avc_sub_smt_logic,
        "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic
    }
    all_ops_total = True
    failing_op_details = None

    for op_name_str, op_logic_func in ops_logic.items():
        a = create_symbolic_avc_val(f"a_tot_{op_name_str}")
        b = create_symbolic_avc_val(f"b_tot_{op_name_str}")
        res = create_symbolic_avc_val(f"res_tot_{op_name_str}")

        setup = get_base_avc_constraints(a, omega_smt_node) + \
                get_base_avc_constraints(b, omega_smt_node)
        
        # Define the operation
        setup.append(op_logic_func(a, b, res, omega_smt_node))
        
        # Property: The result 'res' must satisfy base AVC constraints
        # This is implicitly handled if we check if Not(base_constraints(res)) is SAT
        res_constraints = get_base_avc_constraints(res, omega_smt_node)
        property_res_is_valid = And(res_constraints)

        with Solver(name="z3") as s:
            for f_setup in setup: s.add_assertion(f_setup)
            s.add_assertion(Not(property_res_is_valid)) # Is there a case where result is NOT valid?
            
            if s.solve(): # If SAT, means result can be invalid -> Totality FAILED for this op
                all_ops_total = False
                model = s.get_model()
                ce_parts = []
                for avc_repr_ce in [a,b,res]: # Corrected variable name
                    name = avc_repr_ce['name']
                    try:
                        is_z = model.get_value(avc_repr_ce['is_zero'])
                        is_a = model.get_value(avc_repr_ce['is_areo'])
                        is_f = model.get_value(avc_repr_ce['is_finite'])
                        val_smt = model.get_value(avc_repr_ce['val'])
                        state_str = "ZS" if is_z.is_true() else \
                                    ("AS" if is_a.is_true() else \
                                    (f"Fp({val_smt})" if is_f.is_true() else "UnknownState"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception:
                        ce_parts.append(f"{name}=?")
                failing_op_details = {"op": op_name_str, "counterexample": "; ".join(ce_parts)}
                break 
        if not all_ops_total: break
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, [], TRUE(), [], # Dummy call to use reporting
        expect_property_to_hold=True) # This will be overridden by direct recording
    
    # Manual recording for totality as it's structured differently
    initialize_smt_omega_results(omega_val_py)
    status_emoji_tot = "✅" if all_ops_total else "❌"
    final_message_tot = "All operations are total." if all_ops_total else f"Operation '{failing_op_details['op']}' is NOT total."
    
    if all_ops_total:
        smt_test_results_summary[omega_val_py]["passed"] += 1
    else:
        smt_test_results_summary[omega_val_py]["failed"] += 1
        smt_test_failures_details.append({
            "property": property_name, "omega": omega_val_py,
            "expectation_met": all_ops_total, # True if passed
            "property_held_observed": all_ops_total,
            "expected_to_hold": True,
            "message": final_message_tot,
            "counterexample": failing_op_details["counterexample"] if failing_op_details else None
        })
    print(f"{status_emoji_tot} Omega={omega_val_py}: Property '{property_name}' - {final_message_tot}")
    if failing_op_details and not all_ops_total:
        print(f"    Failing Op: {failing_op_details['op']}, Counterexample: {failing_op_details['counterexample']}")


def smt_test_commutativity(op_logic_func: Callable, op_name_str: str, omega_val_py: int):
    property_name = f"SMT Commutativity of {op_name_str}"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_comm_{op_name_str[:3]}")
    b = create_symbolic_avc_val(f"b_comm_{op_name_str[:3]}")
    res1 = create_symbolic_avc_val(f"res1_comm_{op_name_str[:3]}")
    res2 = create_symbolic_avc_val(f"res2_comm_{op_name_str[:3]}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(res1, omega_smt_node) + \
            get_base_avc_constraints(res2, omega_smt_node)
    
    setup.append(op_logic_func(a, b, res1, omega_smt_node))
    setup.append(op_logic_func(b, a, res2, omega_smt_node))

    property_formula = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        property_formula, [a,b], expect_property_to_hold=True)

def smt_test_associativity(op_logic_func: Callable, op_name_str: str, omega_val_py: int, expected_to_hold: bool):
    property_name = f"SMT Associativity of {op_name_str}"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_assoc_{op_name_str[:3]}")
    b = create_symbolic_avc_val(f"b_assoc_{op_name_str[:3]}")
    c = create_symbolic_avc_val(f"c_assoc_{op_name_str[:3]}")
    
    op_ab = create_symbolic_avc_val(f"op_ab_{op_name_str[:3]}")
    lhs = create_symbolic_avc_val(f"lhs_assoc_{op_name_str[:3]}")
    op_bc = create_symbolic_avc_val(f"op_bc_{op_name_str[:3]}")
    rhs = create_symbolic_avc_val(f"rhs_assoc_{op_name_str[:3]}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(op_ab, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(op_bc, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    setup.append(op_logic_func(a,b,op_ab,omega_smt_node))
    setup.append(op_logic_func(op_ab,c,lhs,omega_smt_node))
    setup.append(op_logic_func(b,c,op_bc,omega_smt_node))
    setup.append(op_logic_func(a,op_bc,rhs,omega_smt_node))
    
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        associativity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

def smt_test_distributivity_mul_over_add(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Distributivity of Mul over Add"
    omega_smt_node = Int(omega_val_py)
    # ... (rest of the setup similar to smt_test_associativity)
    a = create_symbolic_avc_val("a_dist")
    b = create_symbolic_avc_val("b_dist")
    c = create_symbolic_avc_val("c_dist")

    b_plus_c = create_symbolic_avc_val("bpc_dist")
    lhs = create_symbolic_avc_val("lhs_dist") # a * (b+c)

    a_mul_b = create_symbolic_avc_val("amb_dist")
    a_mul_c = create_symbolic_avc_val("amc_dist")
    rhs = create_symbolic_avc_val("rhs_dist") # (a*b) + (a*c)

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(b_plus_c, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(a_mul_b, omega_smt_node) + \
            get_base_avc_constraints(a_mul_c, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    setup.append(avc_add_smt_logic(b,c,b_plus_c,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,b_plus_c,lhs,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,b,a_mul_b,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,c,a_mul_c,omega_smt_node))
    setup.append(avc_add_smt_logic(a_mul_b,a_mul_c,rhs,omega_smt_node))

    distributivity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        distributivity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

# --- Main SMT Test Execution ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] 
    print(f"\n\n{'='*30} STARTING PySMT TESTS FOR REVISED CORE AVCA {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val 
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        smt_test_totality(current_omega_py_val)
        smt_test_commutativity(avc_add_smt_logic, "Addition", current_omega_py_val)
        smt_test_commutativity(avc_mul_smt_logic, "Multiplication", current_omega_py_val)
        
        add_assoc_expected = (current_omega_py_val <= 2)
        smt_test_associativity(avc_add_smt_logic, "Addition", current_omega_py_val, add_assoc_expected)
        smt_test_associativity(avc_mul_smt_logic, "Multiplication", current_omega_py_val, True)
        
        distrib_mul_over_add_expected = (current_omega_py_val <= 2)
        smt_test_distributivity_mul_over_add(current_omega_py_val) # expected_to_hold is handled inside

        print(f"TODO: Implement SMT tests for Subtraction Asymmetry, DFI-Haven, Stuck-at-Areo, Full-Circle Add, Omega=1/2 specifics for Omega={current_omega_py_val}")
        
        print(f"\nSMT Summary for Omega={current_omega_py_val}: Passed={smt_test_results_summary[current_omega_py_val]['passed']}, Failed={smt_test_results_summary[current_omega_py_val]['failed']}")
        print(f"{'='*60}")

    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY {'='*30}")
    total_passed_smt_all = 0
    total_failed_smt_all = 0
    for ov_summary, results in smt_test_results_summary.items():
        total_passed_smt_all += results['passed']
        total_failed_smt_all += results['failed']
        print(f"Omega={ov_summary}: Passed={results['passed']}, Failed={results['failed']}")
    
    if smt_test_failures_details:
        print("\n--- SMT DETAILED FAILURES ---")
        for failure in smt_test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}' (Expected to hold: {failure['expected_to_hold']})")
            print(f"    Observed Property Held: {failure['property_held_observed']}")
            print(f"    Message: {failure['message']}")
            if failure['counterexample']:
                 print(f"    Counterexample/Witness: {failure['counterexample']}")
    
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")

    if total_failed_smt_all == 0 and total_passed_smt_all > 0 :
        print("\n🎉🎉🎉 ALL IMPLEMENTED SMT REVISED CORE AVCA TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: 
        print("\n🤷🤷🤷 NO SMT TESTS WERE FULLY IMPLEMENTED AND RUN / NO TESTS DEFINED. 🤷🤷🤷")
    else:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT REVISED CORE AVCA TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")