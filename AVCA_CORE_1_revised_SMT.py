from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE, ForAll, Exists, simplify,
                             Iff) # Make sure Iff is added here
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Symbolic Core AVCA Definitions ---

# Global Python Omega, set for each test scenario to define constraints
Omega_py: int = 0

def create_symbolic_avc_val(name_prefix: str) -> Dict[str, FNode]:
    """Creates symbolic components for an AVCVal."""
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix  # Store name for easier debugging
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], omega_smt_node: FNode) -> List[FNode]:
    """Basic constraints for a well-formed symbolic AVCVal for a given Omega."""
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))),  # Convention for val
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], omega_smt_node)) # Convention for val
    ]
    # Access the global Python Omega_py to handle Omega=1 case for DFI
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

# --- Symbolic Operation Logic Builders (Corrected and Expanded) ---

def avc_add_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    """SMT logic for Core AVCA avc_add, using Iff for boolean comparisons."""
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    # Case 1: a is Unio -> res is b
    case1 = Implies(a_is_unio, And(Iff(res["is_zero"], b["is_zero"]),
                                   Iff(res["is_areo"], b["is_areo"]),
                                   Iff(res["is_finite"], b["is_finite"]),
                                   Equals(res["val"], b["val"])))
    # Case 2: b is Unio (and a is not DFI) -> res is a
    case2 = Implies(And(Not(a_is_unio), b_is_unio), 
                    And(Iff(res["is_zero"], a["is_zero"]),
                        Iff(res["is_areo"], a["is_areo"]),
                        Iff(res["is_finite"], a["is_finite"]),
                        Equals(res["val"], a["val"])))
    
    # Case 3: a and b are DFI (a["is_finite"] and b["is_finite"])
    sum_val = a["val"] + b["val"]
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(sum_val < omega_smt_node,
                                # Result is Fp(sum_val)
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], sum_val)),
                                # Result is ZERO_UNIO (aspect "zero")
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), 
                                    Equals(res["val"], Int(0))) 
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_sub_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    """SMT logic for Core AVCA avc_sub."""
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    # Case 1: b is Unio -> res is a
    case1 = Implies(b_is_unio, And(Iff(res["is_zero"], a["is_zero"]),
                                   Iff(res["is_areo"], a["is_areo"]),
                                   Iff(res["is_finite"], a["is_finite"]),
                                   Equals(res["val"], a["val"])))
    # Case 2: a is Unio (and b is DFI) -> res is AREO_UNIO
    case2 = Implies(And(a_is_unio, b["is_finite"]), # b cannot be Unio here due to case1
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                        Equals(res["val"], omega_smt_node)))
    
    # Case 3: a and b are DFI
    diff_val = a["val"] - b["val"]
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(a["val"] > b["val"],
                                # Result is Fp(diff_val)
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], diff_val)),
                                # Result is AREO_UNIO (a <= b)
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                                    Equals(res["val"], omega_smt_node))
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_mul_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    """SMT logic for Core AVCA avc_mul."""
    # Case 1: a is Unio. Result depends on a's aspect.
    # a.aspect == "zero" is a["is_zero"]
    # a.aspect == "areo" is a["is_areo"]
    res_if_a_is_ZU = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_if_a_is_AU = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    case1 = Implies(Or(a["is_zero"], a["is_areo"]), Ite(a["is_zero"], res_if_a_is_ZU, res_if_a_is_AU))

    # Case 2: b is Unio (and a is DFI). Result depends on b's aspect.
    res_if_b_is_ZU = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_if_b_is_AU = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    case2 = Implies(And(a["is_finite"], Or(b["is_zero"], b["is_areo"])), 
                    Ite(b["is_zero"], res_if_b_is_ZU, res_if_b_is_AU))
    
    # Case 3: a and b are DFI
    prod_val = a["val"] * b["val"]
    # Core AVCA DFI implies val > 0. So prod_val > 0 if inputs are DFI.
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(prod_val < omega_smt_node, # Assumes prod_val > 0 given DFI inputs
                                # Result is Fp(prod_val)
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], prod_val)),
                                # Result is AREO_UNIO (overflow)
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                                    Equals(res["val"], omega_smt_node))
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_div_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    """SMT logic for Core AVCA avc_div."""
    # Case 1: a is Unio. Result depends on a's aspect.
    res_if_a_is_ZU = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_if_a_is_AU = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    case1 = Implies(Or(a["is_zero"], a["is_areo"]), Ite(a["is_zero"], res_if_a_is_ZU, res_if_a_is_AU))

    # Case 2: b is Unio (and a is DFI) -> res is AREO_UNIO
    case2 = Implies(And(a["is_finite"], Or(b["is_zero"], b["is_areo"])),
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                        Equals(res["val"], omega_smt_node)))
    
    # Case 3: a and b are DFI
    # Symbolic quotient and remainder. b["val"] is DFI, so b["val"] >= 1.
    q_sym = Symbol(f"{res['name']}_q_div", SMT_INT_TYPE) 
    r_sym = Symbol(f"{res['name']}_r_div", SMT_INT_TYPE)

    # Standard division properties: a = q*b + r AND 0 <= r < b
    # Since b["val"] is DFI, b["val"] > 0.
    div_constraints = And(Equals(a["val"], q_sym * b["val"] + r_sym),
                          r_sym >= Int(0),
                          r_sym < b["val"]) # b["val"] is always > 0 if b is DFI

    # Condition for a valid DFI quotient: r==0 AND 1 <= q < Omega
    valid_dfi_quotient_cond = And(Equals(r_sym, Int(0)), 
                                  q_sym >= Int(1), # As per "1 <= q" in spec
                                  q_sym < omega_smt_node)

    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            And(div_constraints, # Define q_sym and r_sym
                                Ite(valid_dfi_quotient_cond,
                                    # Result is Fp(q_sym)
                                    And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                        Equals(res["val"], q_sym)),
                                    # Result is AREO_UNIO
                                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                                        Equals(res["val"], omega_smt_node))
                                )
                            ))
    return And(case1, case2, case3_dfi_dfi)


# --- Symbolic Prover Function ---
smt_test_results_summary: Dict[int, Dict[str, int]] = {}
smt_test_failures_details: List[Dict[str, Any]] = []

def initialize_smt_omega_results(omega_val: int):
    if omega_val not in smt_test_results_summary:
        smt_test_results_summary[omega_val] = {"passed": 0, "failed": 0}

def prove_or_find_counterexample_smt(
    property_name: str, 
    omega_py_val: int, 
    setup_formulas: List[FNode], 
    property_to_test: FNode, # This is the property we want to check if it holds
    inputs_reprs: List[Dict[str, FNode]],
    expect_property_to_hold: bool):
    
    global Omega_py # Update global Python Omega for constraint generation context
    Omega_py = omega_py_val 
    initialize_smt_omega_results(omega_py_val)

    status_emoji = ""
    final_message = ""
    counterexample_str = None
    property_holds_observed = False

    with Solver(name="z3") as s:
        for f_setup in setup_formulas: 
            s.add_assertion(f_setup)
        
        # We want to see if property_to_test is universally true.
        # So, we ask the solver if its negation Not(property_to_test) is satisfiable.
        # If Not(property_to_test) is UNSAT, then property_to_test is always true.
        # If Not(property_to_test) is SAT, then property_to_test is false, and we have a counterexample.
        s.add_assertion(Not(property_to_test))
        
        if not s.solve(): # Not(property_to_test) is UNSAT
            property_holds_observed = True 
        else: # Not(property_to_test) is SAT (counterexample to property_to_test found)
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
                except Exception as e:
                    ce_parts.append(f"{name}=(Error getting model value: {e})")
            counterexample_str = "; ".join(ce_parts)

    # Determine overall success based on expectation
    success_for_summary = (property_holds_observed == expect_property_to_hold)
    status_emoji = "✅" if success_for_summary else "❌"

    if expect_property_to_hold:
        final_message = "Property PROVED universally as expected." if property_holds_observed else "Property FAILED (counterexample found when expected to hold)."
    else: # Expect property NOT to hold (e.g. non-associativity)
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
    if counterexample_str and not success_for_summary: # Or if CE is relevant even on "pass" for non-universal
        print(f"    Counterexample: {counterexample_str}")
    elif not property_holds_observed and not expect_property_to_hold and counterexample_str : # Successful non-universality
         print(f"    Confirming counterexample: {counterexample_str}")


# --- SMT Test Functions ---
def smt_test_commutativity_add_smt(omega_val_py: int):
    omega_smt = Int(omega_val_py)
    a = create_symbolic_avc_val("a")
    b = create_symbolic_avc_val("b")
    res1 = create_symbolic_avc_val("res1_add_comm")
    res2 = create_symbolic_avc_val("res2_add_comm")

    setup = get_base_avc_constraints(a, omega_smt) + \
            get_base_avc_constraints(b, omega_smt) + \
            get_base_avc_constraints(res1, omega_smt) + \
            get_base_avc_constraints(res2, omega_smt)
    
    setup.append(avc_add_smt_logic(a, b, res1, omega_smt))
    setup.append(avc_add_smt_logic(b, a, res2, omega_smt))

    property_formula = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(
        "SMT Commutativity of Addition", omega_val_py, setup, 
        property_formula, [a,b], expect_property_to_hold=True)

def smt_test_associativity_add_smt(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2) # From Revised Core AVCA spec
    property_name = f"SMT {'Associativity' if expected_to_hold else 'Non-Associativity'} of Addition"
    
    omega_smt = Int(omega_val_py)
    a = create_symbolic_avc_val("a_as")
    b = create_symbolic_avc_val("b_as")
    c = create_symbolic_avc_val("c_as")
    ab = create_symbolic_avc_val("ab_as")
    lhs = create_symbolic_avc_val("lhs_as")
    bc = create_symbolic_avc_val("bc_as")
    rhs = create_symbolic_avc_val("rhs_as")

    setup = get_base_avc_constraints(a, omega_smt) + \
            get_base_avc_constraints(b, omega_smt) + \
            get_base_avc_constraints(c, omega_smt) + \
            get_base_avc_constraints(ab, omega_smt) + \
            get_base_avc_constraints(lhs, omega_smt) + \
            get_base_avc_constraints(bc, omega_smt) + \
            get_base_avc_constraints(rhs, omega_smt)

    setup.append(avc_add_smt_logic(a,b,ab,omega_smt))
    setup.append(avc_add_smt_logic(ab,c,lhs,omega_smt))
    setup.append(avc_add_smt_logic(b,c,bc,omega_smt))
    setup.append(avc_add_smt_logic(a,bc,rhs,omega_smt))
    
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        associativity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

# --- Placeholder for other SMT test functions ---
def smt_test_commutativity_mul_smt(omega_val_py: int): print(f"TODO: SMT Commutativity Mul Test for Omega={omega_val_py}")
def smt_test_associativity_mul_smt(omega_val_py: int): print(f"TODO: SMT Associativity Mul Test for Omega={omega_val_py}") # Expected True
def smt_test_distributivity_mul_over_add_smt(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    print(f"TODO: SMT Distributivity Mul/Add Test for Omega={omega_val_py} (exp_hold={expected_to_hold})")
# ... and so on for all properties ...

# --- Main SMT Test Execution ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] 
    print(f"\n\n{'='*30} STARTING PySMT TESTS FOR REVISED CORE AVCA {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val # Set global Python Omega for constraint context
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        smt_test_commutativity_add_smt(current_omega_py_val)
        smt_test_associativity_add_smt(current_omega_py_val)
        
        # Call other SMT test functions here
        smt_test_commutativity_mul_smt(current_omega_py_val)
        smt_test_associativity_mul_smt(current_omega_py_val)
        smt_test_distributivity_mul_over_add_smt(current_omega_py_val)
        # ... etc. ...
        
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
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}'")
            print(f"    Expectation Met: {failure['expectation_met']}, Observed Property Held: {failure['property_held_observed']}, Expected to Hold: {failure['expected_to_hold']}")
            print(f"    Message: {failure['message']}")
            if failure['counterexample']:
                 print(f"    Counterexample: {failure['counterexample']}")
    
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")

    if total_failed_smt_all == 0 and total_passed_smt_all > 0 :
        print("\n🎉🎉🎉 ALL IMPLEMENTED SMT REVISED CORE AVCA TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: # No tests fully ran or defined
        print("\n🤷🤷🤷 NO SMT TESTS WERE FULLY IMPLEMENTED AND RUN. 🤷🤷🤷")
    else:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT REVISED CORE AVCA TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")