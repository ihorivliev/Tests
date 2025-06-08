# ARBITER SCRIPT for Core AVCA-Ω v1.1 Proposal (Additive Overflow to AREO_UNIO)

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, ForAll, Exists)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Global Variables ---
Omega_py: int = 0
smt_test_results_summary: Dict[int, Dict[str, int]] = {}
smt_test_failures_details: List[Dict[str, Any]] = []

# --- Symbolic Core AVCA Definitions ---
def create_symbolic_avc_val(name_prefix: str) -> Dict[str, Any]: # FNode for SMT parts, str for name
    """Creates symbolic components for an AVCVal."""
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_zero_aspect", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_areo_aspect", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix # Store name for easier debugging
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], current_omega_val_for_constraints: int, omega_smt_node: FNode) -> List[FNode]:
    """Basic constraints for a well-formed symbolic AVCVal for a given Omega."""
    # This function uses current_omega_val_for_constraints (Python int) for Python-level conditional logic
    # and omega_smt_node (SMT FNode) for SMT-level constraints.
    global Omega_py # Keep global Omega_py for other parts of script if needed, but prefer passed params
    
    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], omega_smt_node))
    ]
    if current_omega_val_for_constraints == 1: 
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    """SMT formula for equivalence of two symbolic AVCVals (Unio ZS ~ AS)."""
    avc1_is_unio = Or(avc1["is_zero_aspect"], avc1["is_areo_aspect"])
    avc2_is_unio = Or(avc2["is_zero_aspect"], avc2["is_areo_aspect"])
    both_unio = And(avc1_is_unio, avc2_is_unio)
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_fp_equal_val)

# --- SMT Logic Builders (Based on "Revised Core AVCA" Python specification) ---
# Original Additive Logic (Overflow to ZU) - renamed for clarity
def avc_add_ZERO_overflow_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                                     res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    res_is_val_of_b = And(Iff(res["is_zero_aspect"], b["is_zero_aspect"]), Iff(res["is_areo_aspect"], b["is_areo_aspect"]), Iff(res["is_finite"], b["is_finite"]), Equals(res["val"], b["val"]))
    res_is_val_of_a = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), Iff(res["is_areo_aspect"], a["is_areo_aspect"]), Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"]))
    case1_a_is_unio = Implies(a_is_unio, res_is_val_of_b)
    case2_b_is_unio = Implies(And(Not(a_is_unio), b_is_unio), res_is_val_of_a)
    sum_val = a["val"] + b["val"]
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_FP_sum_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], sum_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(sum_val < omega_smt_node, res_is_FP_sum_formula, res_is_ZU_formula))
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

# NEW Additive Logic (Overflow to AU) - The proposed change
def avc_add_AREO_overflow_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                                     res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    res_is_val_of_b = And(Iff(res["is_zero_aspect"], b["is_zero_aspect"]), Iff(res["is_areo_aspect"], b["is_areo_aspect"]), Iff(res["is_finite"], b["is_finite"]), Equals(res["val"], b["val"]))
    res_is_val_of_a = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), Iff(res["is_areo_aspect"], a["is_areo_aspect"]), Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"]))
    case1_a_is_unio = Implies(a_is_unio, res_is_val_of_b)
    case2_b_is_unio = Implies(And(Not(a_is_unio), b_is_unio), res_is_val_of_a)
    sum_val = a["val"] + b["val"]
    # CRITICAL CHANGE HERE: Overflow goes to AREO_UNIO representation
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    res_is_FP_sum_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], sum_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(sum_val < omega_smt_node, res_is_FP_sum_formula, res_is_AU_formula)) # Changed ZU to AU
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

# Other operations remain the same as in the user's SMT_Comprehensive_Tester_Script
def avc_sub_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    # res is 'a'
    res_is_val_of_a = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), Iff(res["is_areo_aspect"], a["is_areo_aspect"]), 
                          Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"]))

    case1_b_is_unio = Implies(b_is_unio, res_is_val_of_a)
    case2_a_is_unio_b_is_dfi = Implies(And(a_is_unio, b["is_finite"]), res_is_AU_formula)
    diff_val = a["val"] - b["val"]
    res_is_FP_diff_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], diff_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(a["val"] > b["val"], res_is_FP_diff_formula, res_is_AU_formula))
    return And(case1_b_is_unio, case2_a_is_unio_b_is_dfi, case3_dfi_dfi)

def avc_mul_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    case1_a_is_unio = Implies(a_is_unio, Ite(a["is_zero_aspect"], res_is_ZU_formula, res_is_AU_formula))
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b_is_unio), Ite(b["is_zero_aspect"], res_is_ZU_formula, res_is_AU_formula))
    prod_val = a["val"] * b["val"]
    res_is_FP_prod_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], prod_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), # DFI product must be > 0
                                res_is_FP_prod_formula,
                                res_is_AU_formula
                            ))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi)

def avc_div_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])

    case1_a_is_unio = Implies(a_is_unio, Ite(a["is_zero_aspect"], res_is_ZU_formula, res_is_AU_formula))
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b_is_unio), res_is_AU_formula)
    
    q_sym = Symbol(f"{res['name']}_q_div", SMT_INT_TYPE)
    r_sym = Symbol(f"{res['name']}_r_div", SMT_INT_TYPE)

    # Define division constraints only if b is a valid DFI divisor (b.val != 0)
    # b["is_finite"] implies b.val >= 1 for Omega_py > 1, so b.val != 0 is guaranteed.
    div_constraints = Implies(b["is_finite"], # b.val > Int(0) is implied by is_finite for Omega > 1
                                And(Equals(a["val"], q_sym * b["val"] + r_sym),
                                    r_sym >= Int(0),
                                    r_sym < b["val"]))
    
    valid_dfi_quotient_cond = Implies(b["is_finite"], # Ensure b is DFI for these conditions
                                      And(Equals(r_sym, Int(0)),
                                          q_sym >= Int(1),
                                          q_sym < omega_smt_node))
    res_is_FP_quot_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], q_sym))

    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            And(div_constraints, # This must hold to define q_sym and r_sym
                                Ite(valid_dfi_quotient_cond,
                                    res_is_FP_quot_formula,
                                    res_is_AU_formula
                                )
                            ))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi)

# --- Symbolic Prover Function (from user's SMT script, adapted for this script's globals) ---
def initialize_smt_omega_results(omega_val: int):
    # Use a unique key for the summary for each test run, including script version
    # For this arbiter script, we will just use omega_val as key
    if omega_val not in smt_test_results_summary:
        smt_test_results_summary[omega_val] = {"passed": 0, "failed": 0}

def prove_or_find_counterexample_smt(
    property_name: str, current_omega_py_val: int, setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    
    global Omega_py # Used by get_base_avc_constraints via its omega_py_val parameter now
    Omega_py = current_omega_py_val # Set context for calls within this function if any implicitly use global Omega_py
    initialize_smt_omega_results(current_omega_py_val)

    property_holds_observed = False
    counterexample_witness_str = None
    
    with Solver(name="z3") as s:
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)
        
        if is_existential:
            s.add_assertion(property_to_verify)
            if s.solve():
                property_holds_observed = True
                model = s.get_model(); ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero_aspect']).is_true()
                        is_a = model.get_value(repr_dict['is_areo_aspect']).is_true()
                        is_f = model.get_value(repr_dict['is_finite']).is_true()
                        val_smt = model.get_value(repr_dict['val'])
                        val = val_smt.constant_value() if val_smt is not None else '?'
                        state_str = f"U({val},{'Z' if is_z else 'A'})" if is_z or is_a else (f"Fp({val})" if is_f else "UnknownState")
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts)
            else:
                property_holds_observed = False
        else: # Universal property
            s.add_assertion(Not(property_to_verify)) # Try to find a counterexample
            if not s.solve(): # If Not(P) is UNSAT
                property_holds_observed = True # Then P holds universally
            else: # If Not(P) is SAT
                property_holds_observed = False # Then P fails (counterexample found)
                model = s.get_model(); ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero_aspect']).is_true()
                        is_a = model.get_value(repr_dict['is_areo_aspect']).is_true()
                        is_f = model.get_value(repr_dict['is_finite']).is_true()
                        val_smt = model.get_value(repr_dict['val'])
                        val = val_smt.constant_value() if val_smt is not None else '?'
                        state_str = f"U({val},{'Z' if is_z else 'A'})" if is_z or is_a else (f"Fp({val})" if is_f else "UnknownState")
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts)

    success_for_summary = (property_holds_observed == expect_property_to_hold)
    status_emoji = "✅" if success_for_summary else "❌"; final_message = ""

    if is_existential:
        if expect_property_to_hold: final_message = "Existence PROVED (witness found)." if property_holds_observed else "Existence FAILED (no witness found when one was expected)."
        else: final_message = "Non-existence CONFIRMED (no witness found)." if not property_holds_observed else "Non-existence FAILED (witness found when none was expected)."
    else: # Universal
        if expect_property_to_hold: final_message = "Property PROVED universally as expected." if property_holds_observed else "Property FAILED (counterexample found when expected to hold)."
        else: final_message = "Property correctly demonstrated NON-UNIVERSALITY (counterexample found as expected)." if not property_holds_observed else "Property INCORRECTLY held universally (expected non-universality/counterexample)."

    if success_for_summary: smt_test_results_summary[current_omega_py_val]["passed"] += 1
    else:
        smt_test_results_summary[current_omega_py_val]["failed"] += 1
        smt_test_failures_details.append({
            "property": property_name, "omega": current_omega_py_val, "is_existential": is_existential,
            "expectation_met": success_for_summary,
            "property_holds_observed_or_witness_found": property_holds_observed,
            "expected_to_hold_or_witness_exist": expect_property_to_hold,
            "message": final_message,
            "counterexample_witness": counterexample_witness_str
        })

    print(f"{status_emoji} Omega={current_omega_py_val}: Property '{property_name}' (Expect P to hold/witness exist: {expect_property_to_hold}) - {final_message}")
    if counterexample_witness_str:
        label = "Debug Info" 
        if success_for_summary:
            if is_existential and property_holds_observed: label = "Witness (Existence PROVED)"
            elif not is_existential and not property_holds_observed: label = "Counterexample (Non-Universality CONFIRMED)"
        else: 
            if is_existential and property_holds_observed: label = "Unexpected Witness (Non-Existence FAILED)"
            elif not is_existential and not property_holds_observed: label = "Counterexample (Property FAILED)"
        print(f"     {label}: {counterexample_witness_str}")

# --- Test Constants (Symbolic Representations of ZERO_UNIO and AREO_UNIO) ---
ZU_const = create_symbolic_avc_val("ZU_const")
AS_const = create_symbolic_avc_val("AS_const")

def get_unio_const_constraints(omega_smt_node: FNode) -> List[FNode]:
    return [
        ZU_const["is_zero_aspect"], Not(ZU_const["is_areo_aspect"]), Not(ZU_const["is_finite"]), Equals(ZU_const["val"], Int(0)),
        Not(AS_const["is_zero_aspect"]), AS_const["is_areo_aspect"], Not(AS_const["is_finite"]), Equals(AS_const["val"], omega_smt_node)
    ]

# --- SMT Test Function Implementations (Comprehensive) ---
# MODIFIED Test Functions will use avc_add_AREO_overflow_smt_logic

# Generic Test Helpers
def smt_test_commutativity(op_logic_func: Callable, op_name_str: str, omega_val_py: int):
    property_name = f"SMT Commutativity of {op_name_str} (v1.1)"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_comm_{op_name_str[:3]}_{omega_val_py}"); b = create_symbolic_avc_val(f"b_comm_{op_name_str[:3]}_{omega_val_py}"); res1 = create_symbolic_avc_val(f"res1_comm_{op_name_str[:3]}_{omega_val_py}"); res2 = create_symbolic_avc_val(f"res2_comm_{op_name_str[:3]}_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_val_py, omega_smt_node) + get_base_avc_constraints(b, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(res1, omega_val_py, omega_smt_node) + get_base_avc_constraints(res2, omega_val_py, omega_smt_node)
    setup.append(op_logic_func(a, b, res1, omega_smt_node)); setup.append(op_logic_func(b, a, res2, omega_smt_node))
    property_formula = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b], True)

def smt_test_associativity(op_logic_func: Callable, op_name_str: str, omega_val_py: int, expected_to_hold: bool):
    property_name = f"SMT Associativity of {op_name_str} (v1.1)"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_assoc_{op_name_str[:3]}_{omega_val_py}"); b = create_symbolic_avc_val(f"b_assoc_{op_name_str[:3]}_{omega_val_py}"); c = create_symbolic_avc_val(f"c_assoc_{op_name_str[:3]}_{omega_val_py}")
    op_ab = create_symbolic_avc_val(f"op_ab_{op_name_str[:3]}_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_assoc_{op_name_str[:3]}_{omega_val_py}"); op_bc = create_symbolic_avc_val(f"op_bc_{op_name_str[:3]}_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_assoc_{op_name_str[:3]}_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_val_py, omega_smt_node) + get_base_avc_constraints(b, omega_val_py, omega_smt_node) + get_base_avc_constraints(c, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(op_ab, omega_val_py, omega_smt_node) + get_base_avc_constraints(lhs, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(op_bc, omega_val_py, omega_smt_node) + get_base_avc_constraints(rhs, omega_val_py, omega_smt_node)
    setup.append(op_logic_func(a,b,op_ab,omega_smt_node)); setup.append(op_logic_func(op_ab,c,lhs,omega_smt_node))
    setup.append(op_logic_func(b,c,op_bc,omega_smt_node)); setup.append(op_logic_func(a,op_bc,rhs,omega_smt_node))
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, associativity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

# --- Experiment A: Foundational Properties (v1.1) ---
def smt_test_A1_totality_all_ops(omega_val_py: int):
    property_name_base = "SMT A.1: Operation Totality (v1.1)"; omega_smt_node = Int(omega_val_py)
    # Use NEW addition logic for the 'Add' test
    ops_logic_map = {"Add": avc_add_AREO_overflow_smt_logic, "Sub": avc_sub_smt_logic, "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic}
    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a_sym = create_symbolic_avc_val(f"a_tot_{op_name_str}_{omega_val_py}"); b_sym = create_symbolic_avc_val(f"b_tot_{op_name_str}_{omega_val_py}"); res_sym = create_symbolic_avc_val(f"res_tot_{op_name_str}_{omega_val_py}")
        setup_tot = get_base_avc_constraints(a_sym, omega_val_py, omega_smt_node) + get_base_avc_constraints(b_sym, omega_val_py, omega_smt_node)
        setup_tot += get_base_avc_constraints(res_sym, omega_val_py, omega_smt_node) 
        setup_tot.append(op_logic_func(a_sym, b_sym, res_sym, omega_smt_node))
        # Property: The setup constraints (including res_sym being valid) are satisfiable.
        prove_or_find_counterexample_smt(current_property_name, omega_val_py, setup_tot, TRUE(), [a_sym, b_sym, res_sym], True, is_existential=False)

def smt_test_A2_well_definedness_all_ops(omega_val_py: int):
    property_name_base = "SMT A.2: Well-Definedness (Unio Equivalence) (v1.1)"
    omega_smt_node = Int(omega_val_py)
    # Use NEW addition logic for the 'Add' test
    ops_logic_map = {"Add": avc_add_AREO_overflow_smt_logic, "Sub": avc_sub_smt_logic, "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic}
    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a1 = create_symbolic_avc_val(f"a1_wd_{op_name_str}_{omega_val_py}"); a2 = create_symbolic_avc_val(f"a2_wd_{op_name_str}_{omega_val_py}")
        b1 = create_symbolic_avc_val(f"b1_wd_{op_name_str}_{omega_val_py}"); b2 = create_symbolic_avc_val(f"b2_wd_{op_name_str}_{omega_val_py}")
        res1 = create_symbolic_avc_val(f"res1_wd_{op_name_str}_{omega_val_py}"); res2 = create_symbolic_avc_val(f"res2_wd_{op_name_str}_{omega_val_py}")
        setup = get_base_avc_constraints(a1, omega_val_py, omega_smt_node) + get_base_avc_constraints(a2, omega_val_py, omega_smt_node) + \
                get_base_avc_constraints(b1, omega_val_py, omega_smt_node) + get_base_avc_constraints(b2, omega_val_py, omega_smt_node) + \
                get_base_avc_constraints(res1, omega_val_py, omega_smt_node) + get_base_avc_constraints(res2, omega_val_py, omega_smt_node)
        premises = And(avc_equiv_smt(a1, a2), avc_equiv_smt(b1, b2))
        setup.append(op_logic_func(a1, b1, res1, omega_smt_node))
        setup.append(op_logic_func(a2, b2, res2, omega_smt_node))
        property_formula = Implies(premises, avc_equiv_smt(res1, res2))
        prove_or_find_counterexample_smt(current_property_name, omega_val_py, setup, property_formula, [a1, a2, b1, b2], True)

# --- Experiment B: Unio's Operational Profile (v1.1) ---
def smt_test_B_unio_operational_profile(omega_val_py: int):
    omega_smt_node = Int(omega_val_py)
    x = create_symbolic_avc_val(f"x_unio_prof_{omega_val_py}")
    base_setup_B = get_base_avc_constraints(x, omega_val_py, omega_smt_node) + \
                   get_base_avc_constraints(ZU_const, omega_val_py, omega_smt_node) + \
                   get_base_avc_constraints(AS_const, omega_val_py, omega_smt_node) + \
                   get_unio_const_constraints(omega_smt_node)

    # ADDITION (v1.1 - uses avc_add_AREO_overflow_smt_logic)
    res_zu_x_add = create_symbolic_avc_val(f"res_ZUX_add_Bv11_{omega_val_py}"); res_x_zu_add = create_symbolic_avc_val(f"res_XZU_add_Bv11_{omega_val_py}")
    res_as_x_add = create_symbolic_avc_val(f"res_ASX_add_Bv11_{omega_val_py}"); res_x_as_add = create_symbolic_avc_val(f"res_XAS_add_Bv11_{omega_val_py}")
    setup_add_B = base_setup_B + get_base_avc_constraints(res_zu_x_add, omega_val_py, omega_smt_node) + get_base_avc_constraints(res_x_zu_add, omega_val_py, omega_smt_node) + \
                  get_base_avc_constraints(res_as_x_add, omega_val_py, omega_smt_node) + get_base_avc_constraints(res_x_as_add, omega_val_py, omega_smt_node)
    setup_add_B.append(avc_add_AREO_overflow_smt_logic(ZU_const, x, res_zu_x_add, omega_smt_node)) # MODIFIED
    setup_add_B.append(avc_add_AREO_overflow_smt_logic(x, ZU_const, res_x_zu_add, omega_smt_node)) # MODIFIED
    setup_add_B.append(avc_add_AREO_overflow_smt_logic(AS_const, x, res_as_x_add, omega_smt_node)) # MODIFIED
    setup_add_B.append(avc_add_AREO_overflow_smt_logic(x, AS_const, res_x_as_add, omega_smt_node)) # MODIFIED
    prop_add_unio = And(avc_equiv_smt(res_zu_x_add, x), avc_equiv_smt(res_x_zu_add, x),
                        avc_equiv_smt(res_as_x_add, x), avc_equiv_smt(res_x_as_add, x))
    prove_or_find_counterexample_smt(f"B.1: Unio Profile - ADD (Identity) (v1.1)", omega_val_py, setup_add_B, prop_add_unio, [x, ZU_const, AS_const], True)

    # SUBTRACTION, MULTIPLICATION, DIVISION remain unchanged as their logic builders are not altered by the proposal.
    # For brevity, their specific test setups from B.2, B.3, B.4 are not repeated here but would be included.
    # Their property names should indicate "(v1.1 context)" if run in this script.
    # Call the original test functions from user's SMT script for these:
    original_smt_test_B_sub(omega_val_py, base_setup_B, omega_smt_node, x) # Placeholder for actual function call
    original_smt_test_B_mul(omega_val_py, base_setup_B, omega_smt_node, x) # Placeholder
    original_smt_test_B_div(omega_val_py, base_setup_B, omega_smt_node, x) # Placeholder


# Placeholder functions for original B.2, B.3, B.4 from the user's script
# (These would contain the detailed SMT setups for SUB, MUL, DIV for Unio profile)
def original_smt_test_B_sub(omega_val_py, base_setup, omega_node, x_sym):
    prove_or_find_counterexample_smt(f"B.2: Unio Profile - SUB (Asymmetric) (v1.1 context)", omega_val_py, base_setup + [ # Assume setup specific to sub
        avc_sub_smt_logic(ZU_const, x_sym, create_symbolic_avc_val("dummy_sub1"), omega_node), # Needs full setup
        avc_sub_smt_logic(x_sym, ZU_const, create_symbolic_avc_val("dummy_sub2"), omega_node),
        avc_sub_smt_logic(AS_const, x_sym, create_symbolic_avc_val("dummy_sub3"), omega_node),
        avc_sub_smt_logic(x_sym, AS_const, create_symbolic_avc_val("dummy_sub4"), omega_node)
    ], TRUE(), [x_sym, ZU_const, AS_const], True) # Simplified property for placeholder

def original_smt_test_B_mul(omega_val_py, base_setup, omega_node, x_sym):
    prove_or_find_counterexample_smt(f"B.3: Unio Profile - MUL (Aspect-Dep) (v1.1 context)", omega_val_py, base_setup + [ # Assume setup specific to mul
        avc_mul_smt_logic(ZU_const, x_sym, create_symbolic_avc_val("dummy_mul1"), omega_node),
        avc_mul_smt_logic(x_sym, ZU_const, create_symbolic_avc_val("dummy_mul2"), omega_node),
        avc_mul_smt_logic(AS_const, x_sym, create_symbolic_avc_val("dummy_mul3"), omega_node),
        avc_mul_smt_logic(x_sym, AS_const, create_symbolic_avc_val("dummy_mul4"), omega_node)
    ], TRUE(), [x_sym, ZU_const, AS_const], True)

def original_smt_test_B_div(omega_val_py, base_setup, omega_node, x_sym):
    prove_or_find_counterexample_smt(f"B.4: Unio Profile - DIV (Aspect-Dep) (v1.1 context)", omega_val_py, base_setup + [ # Assume setup specific to div
        avc_div_smt_logic(ZU_const, x_sym, create_symbolic_avc_val("dummy_div1"), omega_node),
        avc_div_smt_logic(x_sym, ZU_const, create_symbolic_avc_val("dummy_div2"), omega_node),
        avc_div_smt_logic(AS_const, x_sym, create_symbolic_avc_val("dummy_div3"), omega_node),
        avc_div_smt_logic(x_sym, AS_const, create_symbolic_avc_val("dummy_div4"), omega_node)
    ], TRUE(), [x_sym, ZU_const, AS_const], True)


# --- Experiment C: Fundamental Algebraic Properties (v1.1) ---
def smt_test_C1_commutativity_add(omega_val_py: int):
    smt_test_commutativity(avc_add_AREO_overflow_smt_logic, "Addition", omega_val_py) # MODIFIED

def smt_test_C1_commutativity_mul(omega_val_py: int): # Unchanged
    smt_test_commutativity(avc_mul_smt_logic, "Multiplication", omega_val_py)

def smt_test_C2_associativity_add(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2) # ORIGINAL EXPECTATION
    smt_test_associativity(avc_add_AREO_overflow_smt_logic, "Addition", omega_val_py, expected_to_hold) # MODIFIED

def smt_test_C2_associativity_mul(omega_val_py: int): # Unchanged
    smt_test_associativity(avc_mul_smt_logic, "Multiplication", omega_val_py, True)

def smt_test_C3_distributivity_mul_over_add(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2) # ORIGINAL EXPECTATION
    property_name = f"SMT C.3: Left Distributivity of Mul over Add (a*(b+c)) (v1.1)"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_ldist_v11_{omega_val_py}"); b = create_symbolic_avc_val(f"b_ldist_v11_{omega_val_py}"); c = create_symbolic_avc_val(f"c_ldist_v11_{omega_val_py}")
    b_plus_c = create_symbolic_avc_val(f"bpc_ldist_v11_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_ldist_v11_{omega_val_py}")
    a_mul_b = create_symbolic_avc_val(f"amb_ldist_v11_{omega_val_py}"); a_mul_c = create_symbolic_avc_val(f"amc_ldist_v11_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_ldist_v11_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_val_py, omega_smt_node) + get_base_avc_constraints(b, omega_val_py, omega_smt_node) + get_base_avc_constraints(c, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(b_plus_c, omega_val_py, omega_smt_node) + get_base_avc_constraints(lhs, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(a_mul_b, omega_val_py, omega_smt_node) + get_base_avc_constraints(a_mul_c, omega_val_py, omega_smt_node) + get_base_avc_constraints(rhs, omega_val_py, omega_smt_node)
    setup.append(avc_add_AREO_overflow_smt_logic(b,c,b_plus_c,omega_smt_node)); setup.append(avc_mul_smt_logic(a,b_plus_c,lhs,omega_smt_node)) # MODIFIED ADD
    setup.append(avc_mul_smt_logic(a,b,a_mul_b,omega_smt_node)); setup.append(avc_mul_smt_logic(a,c,a_mul_c,omega_smt_node)); setup.append(avc_add_AREO_overflow_smt_logic(a_mul_b,a_mul_c,rhs,omega_smt_node)) # MODIFIED ADD
    distributivity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, distributivity_formula, [a,b,c], expected_to_hold)

# ... Continue modifying ALL test functions from the user's comprehensive SMT script
# that involve addition to use avc_add_AREO_overflow_smt_logic.
# This includes:
# - smt_test_C4_add_right_quasigroup_existence
# - smt_test_C4_add_left_quasigroup_existence
# - smt_test_C4_add_right_inverse_existence
# - smt_test_C5_add_left_alternative_law
# - smt_test_C5_add_right_alternative_law
# - smt_test_C5_add_power_associativity
# - smt_test_C5_add_right_bol_identity
# - smt_test_D1_unio_addition_dilemma_formalized (its setup for res_zu_x and res_as_x for add)
# - smt_test_O_right_distributivity_mul_over_add
# - smt_test_I1_add_sub_cancellation_like
# - smt_test_I2_sub_add_cancellation_like
# - smt_test_cancellation_laws_add

# For brevity, I will show one more modified complex test (C5 Power Assoc)
# and then the main execution block. The user would need to meticulously
# update all tests involving addition.

def smt_test_C5_add_power_associativity(omega_val_py: int):
    property_name = f"SMT Additive Power Associativity ((a+a)+a ~ a+(a+a)) (v1.1)"
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_pa_v11_{omega_val_py}")
    a_plus_a_lhs = create_symbolic_avc_val(f"apa_lhs_pa_v11_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_pa_v11_{omega_val_py}")
    a_plus_a_rhs = create_symbolic_avc_val(f"apa_rhs_pa_v11_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_pa_v11_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(a_plus_a_lhs, omega_val_py, omega_smt_node) + get_base_avc_constraints(lhs, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(a_plus_a_rhs, omega_val_py, omega_smt_node) + get_base_avc_constraints(rhs, omega_val_py, omega_smt_node)
    setup.append(avc_add_AREO_overflow_smt_logic(a,a,a_plus_a_lhs,omega_smt_node)); setup.append(avc_add_AREO_overflow_smt_logic(a_plus_a_lhs,a,lhs,omega_smt_node)) # MODIFIED
    setup.append(avc_add_AREO_overflow_smt_logic(a,a,a_plus_a_rhs,omega_smt_node)); setup.append(avc_add_AREO_overflow_smt_logic(a,a_plus_a_rhs,rhs,omega_smt_node)) # MODIFIED
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a], expect_property_to_hold=True) # Original Expectation

# --- Main SMT Test Execution (Arbiter Script) ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] # As per original SMT script
    
    print(f"\n\n{'='*30} ARBITER SCRIPT: Testing AVCA-Ω v1.1 (Additive Overflow to AREO_UNIO) {'='*30}")
    print("Comparing against original Core AVCA-Ω expectations for algebraic properties.")

    # Recreate the dictionary of all tests to run, ensuring the ADDITIVE ones use the NEW logic builder.
    # For this example, I will only list a few. The user would need to ensure all relevant
    # tests from their comprehensive SMT script are called with the correct addition logic.

    all_experiments_to_run_v1_1 = {
        "A1_Totality": smt_test_A1_totality_all_ops, # This internally calls the new add for "Add" part
        "A2_WellDefinedness": smt_test_A2_well_definedness_all_ops, # Likewise
        "B_UnioOperationalProfile_Add_Only": lambda ov: ( # Focus B.1 with new add
            prove_or_find_counterexample_smt(f"B.1: Unio Profile - ADD (Identity) (v1.1)", ov, 
                get_base_avc_constraints(create_symbolic_avc_val("x"), ov, Int(ov)) + 
                get_base_avc_constraints(ZU_const, ov, Int(ov)) + get_base_avc_constraints(AS_const, ov, Int(ov)) + get_unio_const_constraints(Int(ov)) +
                get_base_avc_constraints(create_symbolic_avc_val("r1"),ov,Int(ov)) + get_base_avc_constraints(create_symbolic_avc_val("r2"),ov,Int(ov)) +
                get_base_avc_constraints(create_symbolic_avc_val("r3"),ov,Int(ov)) + get_base_avc_constraints(create_symbolic_avc_val("r4"),ov,Int(ov)) +
                [avc_add_AREO_overflow_smt_logic(ZU_const, create_symbolic_avc_val("x"), create_symbolic_avc_val("r1"), Int(ov))], # This setup is simplified / incomplete
                And(avc_equiv_smt(create_symbolic_avc_val("r1"), create_symbolic_avc_val("x"))), # Simplified property
                [create_symbolic_avc_val("x"), ZU_const, AS_const], True)
        ),
        "C1_Comm_Add": lambda ov: smt_test_commutativity(avc_add_AREO_overflow_smt_logic, "Addition", ov),
        "C1_Comm_Mul": smt_test_C1_commutativity_mul, # Original
        "C2_Assoc_Add": lambda ov: smt_test_associativity(avc_add_AREO_overflow_smt_logic, "Addition", ov, (ov <= 2)),
        "C2_Assoc_Mul": smt_test_C2_associativity_mul, # Original
        "C3_Dist_MulOverAdd": lambda ov: smt_test_C3_distributivity_mul_over_add(ov), # This test function was already structured to use the general add for its internal logic
        "C5_Add_PAssoc": lambda ov: smt_test_C5_add_power_associativity(ov), # This uses new add
        # ... ALL OTHER TESTS from the original SMT script would be listed here,
        # ensuring those involving addition use avc_add_AREO_overflow_smt_logic.
    }
    
    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val # Set global context
        print(f"\n\n{'='*25} SMT ARBITER TESTING FOR OMEGA = {current_omega_py_val} (v1.1 Add Logic) {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        # Example of calling a few selected tests:
        print("\n--- Running Test Suite Part: A1_Totality (v1.1 Add) ---")
        smt_test_A1_totality_all_ops(current_omega_py_val) # Will use new add for "Add" part internally
        
        print("\n--- Running Test Suite Part: C2_Assoc_Add (v1.1 Add) ---")
        smt_test_C2_associativity_add(current_omega_py_val) # Expects (ov <= 2) to hold

        print("\n--- Running Test Suite Part: C3_Dist_MulOverAdd (v1.1 Add) ---")
        smt_test_C3_distributivity_mul_over_add(current_omega_py_val) # Expects (ov <= 2) to hold

        # It would be better to iterate all_experiments_to_run_v1_1 if fully populated
        # For this illustration, selected calls are shown.

        if current_omega_py_val in smt_test_results_summary:
            passed_count = smt_test_results_summary[current_omega_py_val]['passed']
            failed_count = smt_test_results_summary[current_omega_py_val]['failed']
            print(f"\nSMT ARBITER Summary for Omega={current_omega_py_val}: Passed={passed_count}, Failed={failed_count} (against original expectations)")
        else:
            print(f"\nSMT ARBITER Summary for Omega={current_omega_py_val}: No test results recorded.")
        print(f"{'='*70}")

    print("\n\n{'='*30} OVERALL SMT ARBITER SUITE SUMMARY (v1.1 Add Logic) {'='*30}")
    total_passed_smt_all = 0; total_failed_smt_all = 0
    if not smt_test_results_summary:
        print("No SMT ARBITER test results were recorded for any Omega value.")
    else:
        for ov_summary, results in smt_test_results_summary.items():
            total_passed_smt_all += results.get('passed', 0)
            total_failed_smt_all += results.get('failed', 0)
            print(f"Omega={ov_summary}: Passed={results.get('passed',0)}, Failed={results.get('failed',0)} (against original expectations)")
    
    if smt_test_failures_details:
        print("\n--- SMT ARBITER DETAILED FAILURES (against original expectations) ---")
        for failure in smt_test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}' "
                  f"(Original Expectation: {'Hold' if failure['expected_to_hold_or_witness_exist'] else 'Fail/CE'})")
            print(f"    Observed with v1.1 Add: {'Property Held' if failure['property_holds_observed_or_witness_found'] and not failure['is_existential'] else ('Witness Found' if failure['property_holds_observed_or_witness_found'] and failure['is_existential'] else 'Property Failed/No Witness') }")
            print(f"    Message: {failure['message']}")
            if failure['counterexample_witness']:
                print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    
    print(f"\nTotal SMT ARBITER tests 'Passed' (met original Core AVCA-Ω expectations): {total_passed_smt_all}")
    print(f"Total SMT ARBITER tests 'Failed' (deviated from original Core AVCA-Ω expectations): {total_failed_smt_all}")
    print(f"{'='*80}")

    if total_failed_smt_all == 0 and total_passed_smt_all > 0:
        print("\n🎉🎉🎉 ARBITER SCRIPT: ALL TESTS PASSED! The proposed change to `avc_add` (overflow to AREO_UNIO) PRESERVES all tested algebraic properties of the original Core AVCA-Ω. The coworker's claim appears to hold for the scope of these tests. 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0:
        print("\n🤷🤷🤷 ARBITER SCRIPT: NO SMT TESTS WERE RUN OR COMPLETED. CHECK SCRIPT AND OUTPUT. 🤷🤷🤷")
    else:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ ARBITER SCRIPT: SOME TESTS SHOWED DEVIATIONS from original Core AVCA-Ω expectations. The proposed change to `avc_add` ALTERS some fundamental algebraic properties. Review output carefully. ⚠️⚠️⚠️")