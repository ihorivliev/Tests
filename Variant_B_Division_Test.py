# ULTIMATE ARBITER SCRIPT for Core AVCA-Ω v1.2 (Variant B for Division)
# Tests:
# 1. Additive DFI Overflow -> AREO_UNIO (v1.1 rule)
# 2. Symmetric Unio Aspect Handling for Mul: AREO_UNIO if any Unio operand is Areo-aspected, else ZERO_UNIO (v1.2 rule)
# 3. "Variant B" Divisive Logic (v1.2 rule for division)
# Subtraction remains v1.0.
# All results compared against original Core AVCA-Ω v1.0 expectations.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Global Variables ---
Omega_py: int = 0 # Used by get_base_avc_constraints for Python-level context
smt_test_results_summary: Dict[str, Dict[str, Any]] = {} 
smt_test_failures_details: List[Dict[str, Any]] = []

# --- Symbolic Core AVCA Definitions (Consistent) ---
def create_symbolic_avc_val(name_prefix: str) -> Dict[str, Any]:
    """Creates symbolic components for an AVCVal."""
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_zero_aspect", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_areo_aspect", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix 
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], current_omega_for_constraints: int, omega_smt_node: FNode) -> List[FNode]:
    """Basic constraints for a well-formed symbolic AVCVal for a given Omega."""
    global Omega_py 
    original_omega_py_context = Omega_py
    Omega_py = current_omega_for_constraints # Set context for this call

    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], omega_smt_node))
    ]
    if current_omega_for_constraints == 1: 
        constraints.append(Not(avc_repr["is_finite"]))
    
    Omega_py = original_omega_py_context # Restore context
    return constraints

def avc_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    """SMT formula for algebraic equivalence (Unio ZS ~ AS)."""
    avc1_is_unio = Or(avc1["is_zero_aspect"], avc1["is_areo_aspect"])
    avc2_is_unio = Or(avc2["is_zero_aspect"], avc2["is_areo_aspect"])
    both_unio = And(avc1_is_unio, avc2_is_unio)
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_fp_equal_val)

# --- SMT Logic Builders for AVCA-Ω "v1.2 Variant B" ---

def avc_add_v1_1_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # v1.1 addition: DFI overflow to AREO_UNIO. Unio is identity.
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    
    # Result is b (if a is Unio)
    res_is_val_of_b = And(Iff(res["is_zero_aspect"], b["is_zero_aspect"]), 
                          Iff(res["is_areo_aspect"], b["is_areo_aspect"]), 
                          Iff(res["is_finite"], b["is_finite"]), 
                          Equals(res["val"], b["val"]))
    # Result is a (if b is Unio and a is DFI)
    res_is_val_of_a = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), 
                          Iff(res["is_areo_aspect"], a["is_areo_aspect"]), 
                          Iff(res["is_finite"], a["is_finite"]), 
                          Equals(res["val"], a["val"]))

    case1_a_is_unio = Implies(a_is_unio, res_is_val_of_b)
    case2_b_is_unio = Implies(And(Not(a_is_unio), b_is_unio), res_is_val_of_a)
    
    sum_val = a["val"] + b["val"]
    # DFI overflow yields AREO_UNIO
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], 
                            Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    res_is_FP_sum_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), 
                                res["is_finite"], Equals(res["val"], sum_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), 
                            Ite(sum_val < omega_smt_node, 
                                res_is_FP_sum_formula, 
                                res_is_AU_formula))
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

def avc_sub_v1_0_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                           res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # Original v1.0 subtraction logic
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], 
                            Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    res_is_val_of_a = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), 
                          Iff(res["is_areo_aspect"], a["is_areo_aspect"]), 
                          Iff(res["is_finite"], a["is_finite"]), 
                          Equals(res["val"], a["val"]))
    case1_b_is_unio = Implies(b_is_unio, res_is_val_of_a)
    case2_a_is_unio_b_is_dfi = Implies(And(a_is_unio, b["is_finite"]), res_is_AU_formula)
    diff_val = a["val"] - b["val"]
    res_is_FP_diff_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), 
                                 res["is_finite"], Equals(res["val"], diff_val)) # Corrected Syntax
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), 
                            Ite(a["val"] > b["val"], 
                                res_is_FP_diff_formula, 
                                res_is_AU_formula))
    return And(case1_b_is_unio, case2_a_is_unio_b_is_dfi, case3_dfi_dfi)

def avc_mul_v1_2_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # v1.2: Symmetric rule for Unio inputs: AREO_UNIO if any Unio operand is Areo-aspected, else ZERO_UNIO.
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    a_is_areo_aspected = And(a_is_unio, a["is_areo_aspect"]) # Check if 'a' is Unio AND Areo-aspected
    
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    b_is_areo_aspected = And(b_is_unio, b["is_areo_aspect"]) # Check if 'b' is Unio AND Areo-aspected

    is_any_operand_areo_aspected_unio = Or(a_is_areo_aspected, b_is_areo_aspected)
    
    # Logic for when at least one operand is Unio
    unio_involved_logic = Implies(Or(a_is_unio, b_is_unio),
                              Ite(is_any_operand_areo_aspected_unio,
                                  res_is_AU_formula, 
                                  res_is_ZU_formula  
                              ))
    
    # Logic for DFI * DFI
    prod_val = a["val"] * b["val"]
    res_is_FP_prod_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], prod_val))
    dfi_dfi_logic = Implies(And(a["is_finite"], b["is_finite"]),
                           Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), 
                               res_is_FP_prod_formula,
                               res_is_AU_formula # DFI Mul overflow to AU
                           ))
    
    # Combine: if both DFI, use dfi_dfi_logic; otherwise (at least one Unio), use unio_involved_logic
    return Ite(And(a["is_finite"], b["is_finite"]),
               dfi_dfi_logic,
               unio_involved_logic)

def avc_div_v1_2_variantB_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                                     res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # Variant B for division
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])

    # Rule B1: Divisor 'b' is Unio -> result is AREO_UNIO
    rule_b1_cond = b_is_unio
    rule_b1_res = res_is_AU_formula

    # Rule B2: Dividend 'a' is Unio (and 'b' must be DFI) -> result preserves 'a's aspect
    rule_b2_cond = And(a_is_unio, b["is_finite"])
    res_is_a_aspect_if_a_unio = Ite(a["is_zero_aspect"], res_is_ZU_formula, res_is_AU_formula)
    rule_b2_res = res_is_a_aspect_if_a_unio
    
    # Rule B3: Both are DFI
    q_sym = Symbol(f"{res['name']}_q_div_vB", SMT_INT_TYPE)
    r_sym = Symbol(f"{res['name']}_r_div_vB", SMT_INT_TYPE)
    
    # div_constraints must only apply if b.val is not 0.
    # b["is_finite"] implies b.val >= 1 for Omega_py > 1.
    div_constraints = Implies(And(a["is_finite"], b["is_finite"], b["val"] > Int(0)), 
                                And(Equals(a["val"], q_sym * b["val"] + r_sym),
                                    r_sym >= Int(0),
                                    r_sym < b["val"]))
    
    valid_dfi_quotient_cond = And(Equals(r_sym, Int(0)),
                                  q_sym >= Int(1),
                                  q_sym < omega_smt_node)
    res_is_FP_quot_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], q_sym))
    
    # If b is DFI but b.val is 0 (should be prevented by base constraints if Omega > 1), result is AU
    # Otherwise, apply normal DFI/DFI logic.
    dfi_dfi_inner_logic = Ite(And(b["val"] > Int(0), valid_dfi_quotient_cond), 
                              res_is_FP_quot_formula,
                              res_is_AU_formula)
    
    rule_b3_cond = And(a["is_finite"], b["is_finite"])
    rule_b3_res = And(div_constraints, dfi_dfi_inner_logic) # div_constraints needed to define q,r

    # Nested ITE structure for clarity of rules
    return Ite(rule_b1_cond, rule_b1_res,                   # If b is Unio
               Ite(rule_b2_cond, rule_b2_res,               # Else if a is Unio (and b DFI)
                   rule_b3_res                              # Else (both DFI)
                  )
              )

# --- Symbolic Prover Function (Adapted from user's comprehensive SMT script) ---
def initialize_smt_omega_results(omega_val: int, version_key: str):
    summary_key = f"Omega_{omega_val}_Version_{version_key}"
    if summary_key not in smt_test_results_summary:
        smt_test_results_summary[summary_key] = {"passed": 0, "failed": 0, "omega": omega_val, "version": version_key}

def prove_or_find_counterexample_smt_v1_2(
    property_name: str, current_omega_py_val: int, version_key: str,
    setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    
    global Omega_py 
    Omega_py = current_omega_py_val 
    initialize_smt_omega_results(current_omega_py_val, version_key)
    summary_key = f"Omega_{current_omega_py_val}_Version_{version_key}"

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
        else: 
            s.add_assertion(Not(property_to_verify)) 
            if not s.solve(): 
                property_holds_observed = True 
            else: 
                property_holds_observed = False 
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
        if expect_property_to_hold: final_message = "Existence PROVED (witness found)." if property_holds_observed else "Existence FAILED (NO witness found)."
        else: final_message = "Non-existence CONFIRMED (no witness found)." if not property_holds_observed else "Non-existence FAILED (unexpected witness found)."
    else: 
        if expect_property_to_hold: final_message = "Property PROVED universally." if property_holds_observed else "Property FAILED (counterexample found)."
        else: final_message = "Property correctly NON-UNIVERSAL (counterexample found)." if not property_holds_observed else "Property INCORRECTLY universal (NO counterexample found)."
    
    if success_for_summary: 
        smt_test_results_summary[summary_key]["passed"] += 1
    else:
        smt_test_results_summary[summary_key]["failed"] += 1
        smt_test_failures_details.append({
            "property": property_name, "omega": current_omega_py_val, "version": version_key,
            "expectation_met": success_for_summary,
            "property_holds_observed_or_witness_found": property_holds_observed,
            "expected_to_hold_or_witness_exist": expect_property_to_hold,
            "message": final_message,
            "counterexample_witness": counterexample_witness_str
        })

    print(f"{status_emoji} Omega={current_omega_py_val} ({version_key}): Property '{property_name}' (Expect P to hold/witness exist: {expect_property_to_hold}) - {final_message}")
    if counterexample_witness_str:
        label = "Details"
        if not success_for_summary : label = "Failure Details (Counterexample/Unexpected Witness)"
        elif is_existential and property_holds_observed : label = "Witness Example"
        elif not is_existential and not property_holds_observed : label = "Counterexample Confirming Non-Universality"
        print(f"     {label}: {counterexample_witness_str}")

# --- Test Constants ---
ZU_const = create_symbolic_avc_val("ZU_const") 
AS_const = create_symbolic_avc_val("AS_const") 
def get_unio_const_constraints(omega_smt_node: FNode) -> List[FNode]: 
    return [
        ZU_const["is_zero_aspect"], Not(ZU_const["is_areo_aspect"]), Not(ZU_const["is_finite"]), Equals(ZU_const["val"], Int(0)),
        Not(AS_const["is_zero_aspect"]), AS_const["is_areo_aspect"], Not(AS_const["is_finite"]), Equals(AS_const["val"], omega_smt_node)
    ]

# --- Generic Test Functions (MUST BE INCLUDED and adapted for v1.2 prover) ---
def smt_test_commutativity_v1_2(op_logic_func: Callable, op_name_str: str, 
                                current_omega_py_val: int, expected_to_hold: bool):
    version_key = "v1.2_kernel"
    property_name = f"SMT Commutativity of {op_name_str}"
    omega_smt_node = Int(current_omega_py_val)
    a = create_symbolic_avc_val(f"a_comm_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    b = create_symbolic_avc_val(f"b_comm_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    res1 = create_symbolic_avc_val(f"res1_comm_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    res2 = create_symbolic_avc_val(f"res2_comm_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    setup = get_base_avc_constraints(a, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(b, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(res1, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(res2, current_omega_py_val, omega_smt_node)
    setup.append(op_logic_func(a, b, res1, omega_smt_node))
    setup.append(op_logic_func(b, a, res2, omega_smt_node))
    property_formula = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt_v1_2(property_name, current_omega_py_val, version_key, 
                                          setup, property_formula, [a,b,res1,res2], expected_to_hold)

def smt_test_associativity_v1_2(op_logic_func: Callable, op_name_str: str, 
                                current_omega_py_val: int, expected_to_hold: bool):
    version_key = "v1.2_kernel"
    property_name = f"SMT Associativity of {op_name_str}"
    omega_smt_node = Int(current_omega_py_val)
    a = create_symbolic_avc_val(f"a_assoc_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    b = create_symbolic_avc_val(f"b_assoc_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    c = create_symbolic_avc_val(f"c_assoc_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    op_ab = create_symbolic_avc_val(f"op_ab_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    lhs = create_symbolic_avc_val(f"lhs_assoc_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    op_bc = create_symbolic_avc_val(f"op_bc_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    rhs = create_symbolic_avc_val(f"rhs_assoc_{op_name_str[:3]}_{version_key}_{current_omega_py_val}")
    setup = get_base_avc_constraints(a, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(b, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(c, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(op_ab, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(lhs, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(op_bc, current_omega_py_val, omega_smt_node) + \
            get_base_avc_constraints(rhs, current_omega_py_val, omega_smt_node)
    setup.append(op_logic_func(a,b,op_ab,omega_smt_node))
    setup.append(op_logic_func(op_ab,c,lhs,omega_smt_node))
    setup.append(op_logic_func(b,c,op_bc,omega_smt_node))
    setup.append(op_logic_func(a,op_bc,rhs,omega_smt_node))
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt_v1_2(property_name, current_omega_py_val, version_key, 
                                          setup, associativity_formula, [a,b,c, op_ab, lhs, op_bc, rhs], expected_to_hold)

# --- Specific Test Function Implementations (for v1.2) ---
def smt_test_A1_totality_v1_2(omega_val_py: int):
    property_name_base = "SMT A.1: Operation Totality"; version_key = "v1.2_kernel"
    omega_smt_node = Int(omega_val_py)
    ops_logic_map = {"Add": avc_add_v1_1_smt_logic, "Sub": avc_sub_v1_0_smt_logic, 
                     "Mul": avc_mul_v1_2_smt_logic, "Div": avc_div_v1_2_variantB_smt_logic}
    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a_sym = create_symbolic_avc_val(f"a_tot_{op_name_str}_{version_key}_{omega_val_py}")
        b_sym = create_symbolic_avc_val(f"b_tot_{op_name_str}_{version_key}_{omega_val_py}")
        res_sym = create_symbolic_avc_val(f"res_tot_{op_name_str}_{version_key}_{omega_val_py}")
        setup_tot = get_base_avc_constraints(a_sym, omega_val_py, omega_smt_node) + \
                    get_base_avc_constraints(b_sym, omega_val_py, omega_smt_node) + \
                    get_base_avc_constraints(res_sym, omega_val_py, omega_smt_node)
        setup_tot.append(op_logic_func(a_sym, b_sym, res_sym, omega_smt_node))
        prove_or_find_counterexample_smt_v1_2(current_property_name, omega_val_py, version_key, 
                                              setup_tot, TRUE(), 
                                              [a_sym, b_sym, res_sym], 
                                              expect_property_to_hold=True)

def smt_test_C3_distributivity_v1_2(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2) # ORIGINAL v1.0 EXPECTATION
    property_name = f"SMT C.3: Left Distributivity (a*(b+c))"; version_key = "v1.2_kernel"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_ldist_{version_key}_{omega_val_py}"); b = create_symbolic_avc_val(f"b_ldist_{version_key}_{omega_val_py}"); c = create_symbolic_avc_val(f"c_ldist_{version_key}_{omega_val_py}")
    b_plus_c = create_symbolic_avc_val(f"bpc_ldist_{version_key}_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_ldist_{version_key}_{omega_val_py}")
    a_mul_b = create_symbolic_avc_val(f"amb_ldist_{version_key}_{omega_val_py}"); a_mul_c = create_symbolic_avc_val(f"amc_ldist_{version_key}_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_ldist_{version_key}_{omega_val_py}")
    
    setup = get_base_avc_constraints(a, omega_val_py, omega_smt_node) + get_base_avc_constraints(b, omega_val_py, omega_smt_node) + get_base_avc_constraints(c, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(b_plus_c, omega_val_py, omega_smt_node) + get_base_avc_constraints(lhs, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(a_mul_b, omega_val_py, omega_smt_node) + get_base_avc_constraints(a_mul_c, omega_val_py, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_val_py, omega_smt_node)
    
    setup.append(avc_add_v1_1_smt_logic(b,c,b_plus_c,omega_smt_node))       
    setup.append(avc_mul_v1_2_smt_logic(a,b_plus_c,lhs,omega_smt_node))    
    setup.append(avc_mul_v1_2_smt_logic(a,b,a_mul_b,omega_smt_node))       
    setup.append(avc_mul_v1_2_smt_logic(a,c,a_mul_c,omega_smt_node))       
    setup.append(avc_add_v1_1_smt_logic(a_mul_b,a_mul_c,rhs,omega_smt_node)) 
    
    distributivity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt_v1_2(property_name, omega_val_py, version_key, setup, 
                                          distributivity_formula, [a,b,c, lhs, rhs, b_plus_c, a_mul_b, a_mul_c], expected_to_hold)

# --- Main SMT Test Execution (Arbiter Script for v1.2) ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] 
    
    print(f"\n\n{'='*30} ARBITER SCRIPT: Testing AVCA-Ω v1.2 (Variant B Div) Proposal {'='*30}")
    print("  v1.1 Additive Logic: DFI Overflow -> AREO_UNIO")
    print("  v1.2 Multiplicative Logic: Symmetric Unio Aspect Handling (AreO Dominates if present in Unio ops)")
    print("  v1.2 Divisive Logic (Variant B): Divisor Unio -> AREO_UNIO; Dividend Unio/DFI -> Preserves Dividend Aspect")
    print("  Subtraction Logic: v1.0 (Original)")
    print("  Comparing against original Core AVCA-Ω v1.0 expectations for algebraic properties.")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val # Set global context for any implicit uses
        version_key_report = "v1.2_VariantB"
        print(f"\n\n{'='*25} SMT ARBITER TESTING FOR OMEGA = {current_omega_py_val} ({version_key_report} Logic Set) {'='*25}")
        
        # Call a representative set of tests. A full run would include all tests from the comprehensive suite.
        print(f"\n--- Testing Foundational Properties ({version_key_report}) ---")
        smt_test_A1_totality_v1_2(current_omega_py_val)
        # smt_test_A2_well_definedness_all_ops_v1_2(current_omega_py_val) # (Assuming it's defined and uses v1.2 ops)

        print(f"\n--- Testing Additive Properties (using v1.1 add logic) ---")
        smt_test_commutativity_v1_2(avc_add_v1_1_smt_logic, "Addition", current_omega_py_val, True)
        smt_test_associativity_v1_2(avc_add_v1_1_smt_logic, "Addition", current_omega_py_val, (current_omega_py_val <= 2))

        print(f"\n--- Testing Multiplicative Properties (using v1.2 mul logic) ---")
        smt_test_commutativity_v1_2(avc_mul_v1_2_smt_logic, "Multiplication", current_omega_py_val, True)
        smt_test_associativity_v1_2(avc_mul_v1_2_smt_logic, "Multiplication", current_omega_py_val, True)

        print(f"\n--- Testing Distributivity (v1.1 add, v1.2 mul) ---")
        smt_test_C3_distributivity_v1_2(current_omega_py_val)
        
        summary_key_v1_2 = f"Omega_{current_omega_py_val}_Version_{version_key_report}"
        if summary_key_v1_2 in smt_test_results_summary:
            passed_count = smt_test_results_summary[summary_key_v1_2]['passed']
            failed_count = smt_test_results_summary[summary_key_v1_2]['failed']
            print(f"\nSMT ARBITER Summary for Omega={current_omega_py_val} ({version_key_report} Logic): Passed={passed_count}, Failed={failed_count} (against original v1.0 expectations)")
        else:
             print(f"\nSMT ARBITER Summary for Omega={current_omega_py_val} ({version_key_report} Logic): No test results yet for this specific summary key.")
        print(f"{'='*70}")

    print("\n\n{'='*30} OVERALL SMT ARBITER SUITE SUMMARY (v1.2 Variant B Logic Set) {'='*30}")
    total_passed_smt_all = 0; total_failed_smt_all = 0
    for key, results in smt_test_results_summary.items():
        if "v1.2_VariantB" in results.get("version", ""): 
            total_passed_smt_all += results.get('passed', 0)
            total_failed_smt_all += results.get('failed', 0)
            print(f"Omega={results['omega']} ({results['version']}): Passed={results.get('passed',0)}, Failed={results.get('failed',0)} (vs v1.0 expectations)")
    
    if smt_test_failures_details:
        print("\n--- SMT ARBITER DETAILED FAILURES (v1.2 Variant B Logic Set vs v1.0 expectations) ---")
        for failure in smt_test_failures_details:
             if failure.get('version') == "v1.2_VariantB":
                print(f"  Omega={failure['omega']} ({failure['version']}): FAILED Property '{failure['property']}' "
                      f"(Original v1.0 Expectation: {'Hold' if failure['expected_to_hold_or_witness_exist'] else 'Fail/CE'})")
                observed_result_str = "Error in test logic"
                if failure.get('is_existential', False):
                    observed_result_str = "Witness Found" if failure['property_holds_observed_or_witness_found'] else "No Witness Found"
                else:
                    observed_result_str = "Property Held Universally" if failure['property_holds_observed_or_witness_found'] else "Property Failed (CE Found)"
                print(f"    Observed with v1.2_VariantB Logic Set: {observed_result_str}")
                print(f"    Message: {failure['message']}")
                if failure['counterexample_witness']:
                    print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    
    print(f"\nTotal SMT ARBITER tests 'Passed' (met original Core AVCA-Ω v1.0 expectations with v1.2_VariantB logic set): {total_passed_smt_all}")
    print(f"Total SMT ARBITER tests 'Failed' (deviated from original Core AVCA-Ω v1.0 expectations with v1.2_VariantB logic set): {total_failed_smt_all}")
    print(f"{'='*80}")

    if total_failed_smt_all == 0 and total_passed_smt_all > 0:
        print("\n🎉🎉🎉 ARBITER SCRIPT (v1.2 Variant B): ALL EXECUTED TESTS PASSED! The v1.2 changes (v1.1 add, v1.2 mul, v1.2 Variant B div) appear to PRESERVE the tested algebraic properties of the original Core AVCA-Ω v1.0. The coworker's claim for this refined v1.2 appears to hold for the scope of these specific tests. 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0:
        print("\n🤷🤷🤷 ARBITER SCRIPT (v1.2 Variant B): NO SMT TESTS WERE EFFECTIVELY RUN OR COMPLETED WITH RESULTS. CHECK SCRIPT AND TEST CALLS. 🤷🤷🤷")
    else:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ ARBITER SCRIPT (v1.2 Variant B): SOME TESTS SHOWED DEVIATIONS from original Core AVCA-Ω v1.0 expectations. The proposed v1.2 changes ALTER some fundamental algebraic properties. Review output carefully. ⚠️⚠️⚠️")

