from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE,
                             Iff) # Corrected import
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
    if Omega_py == 1: # Access global Python Omega_py
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

    # Python: if isinstance(a, Unio): return b
    case1 = Implies(a_is_unio, And(Iff(res["is_zero"], b["is_zero"]),
                                   Iff(res["is_areo"], b["is_areo"]),
                                   Iff(res["is_finite"], b["is_finite"]),
                                   Equals(res["val"], b["val"])))
    # Python: if isinstance(b, Unio): return a
    case2 = Implies(And(Not(a_is_unio), b_is_unio), 
                    And(Iff(res["is_zero"], a["is_zero"]),
                        Iff(res["is_areo"], a["is_areo"]),
                        Iff(res["is_finite"], a["is_finite"]),
                        Equals(res["val"], a["val"])))
    
    # Python: s = a + b; return s if s < Omega else ZERO_UNIO
    sum_val = a["val"] + b["val"]
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(sum_val < omega_smt_node,
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], sum_val)), # Result is Fp(sum_val)
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), 
                                    Equals(res["val"], Int(0))) # Result is ZERO_UNIO
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_sub_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    # Python: if isinstance(b, Unio): return a
    case1 = Implies(b_is_unio, And(Iff(res["is_zero"], a["is_zero"]),
                                   Iff(res["is_areo"], a["is_areo"]),
                                   Iff(res["is_finite"], a["is_finite"]),
                                   Equals(res["val"], a["val"])))
    # Python: if isinstance(a, Unio): return AREO_UNIO
    case2 = Implies(And(a_is_unio, Not(b_is_unio)), # a is Unio, b is DFI
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                        Equals(res["val"], omega_smt_node))) # Result is AREO_UNIO
    
    # Python: return (a - b) if a > b else AREO_UNIO
    diff_val = a["val"] - b["val"]
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(a["val"] > b["val"],
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], diff_val)), # Result is Fp(diff_val)
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                                    Equals(res["val"], omega_smt_node)) # Result is AREO_UNIO
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_mul_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # Python:
    # if isinstance(a, Unio): return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    # if isinstance(b, Unio): return ZERO_UNIO if b.aspect=="zero" else AREO_UNIO
    # p = a * b
    # return p if p < Omega else AREO_UNIO

    res_is_ZU = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))

    # Case 1: a is Unio
    # a["is_zero"] represents ZERO_UNIO aspect, a["is_areo"] represents AREO_UNIO aspect
    case1 = Implies(Or(a["is_zero"], a["is_areo"]), 
                    Ite(a["is_zero"], res_is_ZU, res_is_AU))
    
    # Case 2: b is Unio (and a is DFI)
    case2 = Implies(And(a["is_finite"], Or(b["is_zero"], b["is_areo"])),
                    Ite(b["is_zero"], res_is_ZU, res_is_AU))
    
    # Case 3: a and b are DFI
    prod_val = a["val"] * b["val"]
    # DFI inputs are > 0, so prod_val > 0 if both are DFI
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(prod_val < omega_smt_node, # And prod_val > 0 is implicit
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                    Equals(res["val"], prod_val)), # Result is Fp(prod_val)
                                res_is_AU # Result is AREO_UNIO (overflow)
                            ))
    return And(case1, case2, case3_dfi_dfi)

def avc_div_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # Python:
    # if isinstance(a, Unio): return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    # if isinstance(b, Unio): return AREO_UNIO
    # q, r = divmod(a, b)
    # return q if (r == 0 and 1 <= q < Omega) else AREO_UNIO

    res_is_ZU = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))

    # Case 1: a is Unio
    case1 = Implies(Or(a["is_zero"], a["is_areo"]), 
                    Ite(a["is_zero"], res_is_ZU, res_is_AU))

    # Case 2: b is Unio (and a is DFI) -> res is AREO_UNIO
    case2 = Implies(And(a["is_finite"], Or(b["is_zero"], b["is_areo"])),
                    res_is_AU)
    
    # Case 3: a and b are DFI
    # b["val"] for DFI is >= 1.
    q_sym = Symbol(f"{res['name']}_q_div", SMT_INT_TYPE) 
    r_sym = Symbol(f"{res['name']}_r_div", SMT_INT_TYPE)

    # SMT does not have divmod directly. Define integer division properties.
    # For b_val > 0: a_val = q_sym * b_val + r_sym AND 0 <= r_sym < b_val
    # We must ensure b_val is not zero for these constraints. b["is_finite"] implies b["val"] > 0.
    div_constraints = Implies(b["val"] > Int(0), # Ensure divisor is positive for these semantics
                              And(Equals(a["val"], q_sym * b["val"] + r_sym),
                                  r_sym >= Int(0),
                                  r_sym < b["val"]))
    
    # Condition for a valid DFI quotient: r==0 AND 1 <= q < Omega
    valid_dfi_quotient_cond = And(Equals(r_sym, Int(0)), 
                                  q_sym >= Int(1), 
                                  q_sym < omega_smt_node)

    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), # b["val"] > 0 is implied
                            And(div_constraints, 
                                Ite(valid_dfi_quotient_cond,
                                    And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], 
                                        Equals(res["val"], q_sym)), # Result is Fp(q_sym)
                                    res_is_AU # Result is AREO_UNIO
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

    with Solver(name="z3") as s: # Removed logic="ALL" for broader compatibility
        for f_setup in setup_formulas: 
            s.add_assertion(f_setup)
        
        s.add_assertion(Not(property_to_verify)) # Try to find a case where property_to_verify is FALSE
        
        if not s.solve(): # If Not(property_to_verify) is UNSAT
            property_holds_observed = True # Means property_to_verify is always TRUE
        else: # Not(property_to_verify) is SAT (counterexample to property_to_verify found)
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
                except Exception: # Handle cases where a symbol might not be in the model if not relevant
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
    if counterexample_str and (not success_for_summary or not expect_property_to_hold) : 
        print(f"    Counterexample/Witness: {counterexample_str}")


# --- SMT Test Functions (Examples) ---
def smt_test_commutativity_add(omega_val_py: int):
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val("a_ca")
    b = create_symbolic_avc_val("b_ca")
    res1 = create_symbolic_avc_val("res1_ca")
    res2 = create_symbolic_avc_val("res2_ca")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(res1, omega_smt_node) + \
            get_base_avc_constraints(res2, omega_smt_node)
    
    setup.append(avc_add_smt_logic(a, b, res1, omega_smt_node))
    setup.append(avc_add_smt_logic(b, a, res2, omega_smt_node))

    property_formula = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(
        "SMT Commutativity of Addition", omega_val_py, setup, 
        property_formula, [a,b], expect_property_to_hold=True)

def smt_test_associativity_add(omega_val_py: int):
    # From Revised Core AVCA: Associativity of Add holds for Omega <= 2
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Associativity of Addition"
    
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val("a_aa")
    b = create_symbolic_avc_val("b_aa")
    c = create_symbolic_avc_val("c_aa")
    ab = create_symbolic_avc_val("ab_aa")
    lhs = create_symbolic_avc_val("lhs_aa")
    bc = create_symbolic_avc_val("bc_aa")
    rhs = create_symbolic_avc_val("rhs_aa")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(ab, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(bc, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    setup.append(avc_add_smt_logic(a,b,ab,omega_smt_node))
    setup.append(avc_add_smt_logic(ab,c,lhs,omega_smt_node))
    setup.append(avc_add_smt_logic(b,c,bc,omega_smt_node))
    setup.append(avc_add_smt_logic(a,bc,rhs,omega_smt_node))
    
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        associativity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

def smt_test_associativity_mul(omega_val_py: int):
    expected_to_hold = True # Multiplication is always associative
    property_name = f"SMT Associativity of Multiplication"
    
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val("a_am")
    b = create_symbolic_avc_val("b_am")
    c = create_symbolic_avc_val("c_am")
    ab = create_symbolic_avc_val("ab_am")
    lhs = create_symbolic_avc_val("lhs_am")
    bc = create_symbolic_avc_val("bc_am")
    rhs = create_symbolic_avc_val("rhs_am")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(ab, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(bc, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    setup.append(avc_mul_smt_logic(a,b,ab,omega_smt_node))
    setup.append(avc_mul_smt_logic(ab,c,lhs,omega_smt_node))
    setup.append(avc_mul_smt_logic(b,c,bc,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,bc,rhs,omega_smt_node))
    
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        associativity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

def smt_test_distributivity_mul_over_add(omega_val_py: int):
    # From Revised Core AVCA: Distributivity holds for Omega <= 2
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Distributivity of Mul over Add"

    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val("a_dist")
    b = create_symbolic_avc_val("b_dist")
    c = create_symbolic_avc_val("c_dist")

    b_plus_c = create_symbolic_avc_val("bpc_dist")
    lhs = create_symbolic_avc_val("lhs_dist")

    a_mul_b = create_symbolic_avc_val("amb_dist")
    a_mul_c = create_symbolic_avc_val("amc_dist")
    rhs = create_symbolic_avc_val("rhs_dist")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(b_plus_c, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(a_mul_b, omega_smt_node) + \
            get_base_avc_constraints(a_mul_c, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    # LHS: a * (b+c)
    setup.append(avc_add_smt_logic(b,c,b_plus_c,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,b_plus_c,lhs,omega_smt_node))

    # RHS: (a*b) + (a*c)
    setup.append(avc_mul_smt_logic(a,b,a_mul_b,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,c,a_mul_c,omega_smt_node))
    setup.append(avc_add_smt_logic(a_mul_b,a_mul_c,rhs,omega_smt_node))

    distributivity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        distributivity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

# --- Main SMT Test Execution ---
if __name__ == "__main__":
    # Omegas to test, covering phase transitions from Revised Core AVCA
    omegas_to_test_smt = [1, 2, 3, 5] 
    print(f"\n\n{'='*30} STARTING PySMT TESTS FOR REVISED CORE AVCA {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val 
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        smt_test_commutativity_add(current_omega_py_val)
        smt_test_associativity_add(current_omega_py_val) 
        smt_test_associativity_mul(current_omega_py_val) # Expected to hold for all Omega
        smt_test_distributivity_mul_over_add(current_omega_py_val)
        
        # --- Add calls to other SMT test functions here ---
        # e.g.:
        # smt_test_commutativity_mul_smt(current_omega_py_val)
        # smt_test_subtraction_asymmetry_smt(current_omega_py_val)
        # smt_test_dfi_haven_smt(current_omega_py_val)
        # smt_test_stuck_at_areo_smt(current_omega_py_val)
        # smt_test_full_circle_addition_smt(current_omega_py_val)
        # if current_omega_py_val == 1: smt_test_omega_1_specifics_smt()
        # if current_omega_py_val == 2: smt_test_omega_2_algebra_smt()
        print(f"TODO: Implement remaining SMT tests for Omega={current_omega_py_val}")

        print(f"\nSMT Summary for Omega={current_omega_py_val}: Passed={smt_test_results_summary[current_omega_py_val]['passed']}, Failed={smt_test_results_summary[current_omega_py_val]['failed']}")
        print(f"{'='*60}")

    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY {'='*30}")
    # ... (rest of summary printing code from previous script) ...
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
                 print(f"    Counterexample/Witness: {failure['counterexample']}") # Witness if expected to fail & found
    
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")

    if total_failed_smt_all == 0 and total_passed_smt_all > 0 :
        print("\n🎉🎉🎉 ALL IMPLEMENTED SMT REVISED CORE AVCA TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: 
        print("\n🤷🤷🤷 NO SMT TESTS WERE FULLY IMPLEMENTED AND RUN / NO TESTS DEFINED. 🤷🤷🤷")
    else:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT REVISED CORE AVCA TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")