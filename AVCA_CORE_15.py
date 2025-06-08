from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE,
                             Iff, ForAll, Exists) # Added ForAll, Exists for clarity, though prover handles
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Symbolic Core AVCA Definitions (from previous script) ---
Omega_py: int = 0

def create_symbolic_avc_val(name_prefix: str) -> Dict[str, FNode]:
    # ... (same as before)
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], omega_smt_node: FNode) -> List[FNode]:
    # ... (same as before)
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
    # ... (same as before)
    both_zs = And(avc1["is_zero"], avc2["is_zero"])
    both_as = And(avc1["is_areo"], avc2["is_areo"])
    unio_cross_equiv1 = And(avc1["is_zero"], avc2["is_areo"])
    unio_cross_equiv2 = And(avc1["is_areo"], avc2["is_zero"])
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_zs, both_as, unio_cross_equiv1, unio_cross_equiv2, both_fp_equal_val)

# --- SMT Logic Builders (from previous script, ensure these are definitive) ---
def avc_add_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # ... (same as before)
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
    # ... (same as before)
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
    # ... (same as before)
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
    # ... (same as before)
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

# --- Symbolic Prover Function (from previous script) ---
smt_test_results_summary: Dict[int, Dict[str, int]] = {}
smt_test_failures_details: List[Dict[str, Any]] = []

def initialize_smt_omega_results(omega_val: int):
    # ... (same as before)
    if omega_val not in smt_test_results_summary:
        smt_test_results_summary[omega_val] = {"passed": 0, "failed": 0}

def prove_or_find_counterexample_smt(
    property_name: str, omega_py_val: int, setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, FNode]],
    expect_property_to_hold: bool, is_existential: bool = False):
    # ... (same as before, ensuring it's the refined version from AVCA_CORE_7_ext1.py)
    global Omega_py
    Omega_py = omega_py_val
    initialize_smt_omega_results(omega_py_val)
    property_holds_observed = False; counterexample_witness_str = None
    with Solver(name="z3") as s:
        for f_setup in setup_formulas: s.add_assertion(f_setup)
        if is_existential:
            s.add_assertion(property_to_verify)
            if s.solve():
                property_holds_observed = True; model = s.get_model(); ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero']); is_a = model.get_value(repr_dict['is_areo']); is_f = model.get_value(repr_dict['is_finite']); val_smt = model.get_value(repr_dict['val'])
                        state_str = "ZS" if is_z.is_true() else ("AS" if is_a.is_true() else (f"Fp({val_smt})" if is_f.is_true() else "Unknown"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts)
            else: property_holds_observed = False
        else: # Universal
            s.add_assertion(Not(property_to_verify))
            if not s.solve(): property_holds_observed = True
            else:
                property_holds_observed = False; model = s.get_model(); ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero']); is_a = model.get_value(repr_dict['is_areo']); is_f = model.get_value(repr_dict['is_finite']); val_smt = model.get_value(repr_dict['val'])
                        state_str = "ZS" if is_z.is_true() else ("AS" if is_a.is_true() else (f"Fp({val_smt})" if is_f.is_true() else "Unknown"))
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
    if success_for_summary: smt_test_results_summary[omega_py_val]["passed"] += 1
    else:
        smt_test_results_summary[omega_py_val]["failed"] += 1
        smt_test_failures_details.append({"property": property_name, "omega": omega_py_val, "is_existential": is_existential, "expectation_met": success_for_summary, "property_holds_observed_or_witness_found": property_holds_observed, "expected_to_hold_or_witness_exist": expect_property_to_hold, "message": final_message, "counterexample_witness": counterexample_witness_str})
    print(f"{status_emoji} Omega={omega_py_val}: Property '{property_name}' (Expect P to hold/witness exist: {expect_property_to_hold}) - {final_message}")
    if counterexample_witness_str:
        label = "Witness" if (is_existential and property_holds_observed and expect_property_to_hold) else ("Counterexample" if (not is_existential and not property_holds_observed and expect_property_to_hold) else ("Confirming CE for Non-Universality" if (not is_existential and not property_holds_observed and not expect_property_to_hold) else ("Unexpected Witness" if (is_existential and not expect_property_to_hold and property_holds_observed) else ("Unexpected Counterexample" if (not is_existential and expect_property_to_hold and not property_holds_observed) else "Debug Info"))))
        print(f"    {label}: {counterexample_witness_str}")

# --- SMT Test Function Implementations for Experiments E, F, G, H, I, J ---

# E. Uniqueness Properties
def smt_test_E1_uniqueness_additive_inverses(omega_val_py: int):
    property_name = "SMT E.1: Uniqueness of Additive Inverses"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_e1_{omega_val_py}")
    x1 = create_symbolic_avc_val(f"x1_e1_{omega_val_py}")
    x2 = create_symbolic_avc_val(f"x2_e1_{omega_val_py}")
    res_ax1 = create_symbolic_avc_val(f"res_ax1_e1_{omega_val_py}")
    res_ax2 = create_symbolic_avc_val(f"res_ax2_e1_{omega_val_py}")
    zs_identity = create_symbolic_avc_val(f"zs_e1_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(x1, omega_smt_node) + \
            get_base_avc_constraints(x2, omega_smt_node) + \
            get_base_avc_constraints(res_ax1, omega_smt_node) + \
            get_base_avc_constraints(res_ax2, omega_smt_node) + \
            get_base_avc_constraints(zs_identity, omega_smt_node)
    
    setup.append(zs_identity["is_zero"]) # Define ZS as the identity
    setup.append(avc_add_smt_logic(a, x1, res_ax1, omega_smt_node))
    setup.append(avc_add_smt_logic(a, x2, res_ax2, omega_smt_node))

    # Property: If (a+x1 ~ ZS) AND (a+x2 ~ ZS) THEN (x1 ~ x2)
    premise = And(avc_equiv_smt(res_ax1, zs_identity), avc_equiv_smt(res_ax2, zs_identity))
    conclusion = avc_equiv_smt(x1, x2)
    property_formula = Implies(premise, conclusion)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,x1,x2], True)

def smt_test_E2_uniqueness_quasigroup_solutions_add(omega_val_py: int):
    property_name_base = "SMT E.2: Uniqueness of Additive Quasigroup Solutions"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_e2_{omega_val_py}")
    b_target = create_symbolic_avc_val(f"b_target_e2_{omega_val_py}")
    x1 = create_symbolic_avc_val(f"x1_e2_{omega_val_py}")
    x2 = create_symbolic_avc_val(f"x2_e2_{omega_val_py}")
    res_ax1 = create_symbolic_avc_val(f"res_ax1_e2_{omega_val_py}")
    res_ax2 = create_symbolic_avc_val(f"res_ax2_e2_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b_target, omega_smt_node) + \
            get_base_avc_constraints(x1, omega_smt_node) + \
            get_base_avc_constraints(x2, omega_smt_node) + \
            get_base_avc_constraints(res_ax1, omega_smt_node) + \
            get_base_avc_constraints(res_ax2, omega_smt_node)

    setup.append(avc_add_smt_logic(a, x1, res_ax1, omega_smt_node))
    setup.append(avc_add_smt_logic(a, x2, res_ax2, omega_smt_node))

    # Right Quasigroup Uniqueness: If (a+x1 ~ b_target) AND (a+x2 ~ b_target) THEN (x1 ~ x2)
    premise_rq = And(avc_equiv_smt(res_ax1, b_target), avc_equiv_smt(res_ax2, b_target))
    conclusion_rq = avc_equiv_smt(x1, x2)
    property_rq_unique = Implies(premise_rq, conclusion_rq)
    prove_or_find_counterexample_smt(f"{property_name_base} (Right: a+x=b)", omega_val_py, setup, property_rq_unique, [a,b_target,x1,x2], True)

    # Left Quasigroup Uniqueness (using y1, y2 for clarity, and renaming res)
    y1 = create_symbolic_avc_val(f"y1_e2L_{omega_val_py}")
    y2 = create_symbolic_avc_val(f"y2_e2L_{omega_val_py}")
    res_y1a = create_symbolic_avc_val(f"res_y1a_e2L_{omega_val_py}")
    res_y2a = create_symbolic_avc_val(f"res_y2a_e2L_{omega_val_py}")
    setup_lq = get_base_avc_constraints(a, omega_smt_node) + \
               get_base_avc_constraints(b_target, omega_smt_node) + \
               get_base_avc_constraints(y1, omega_smt_node) + \
               get_base_avc_constraints(y2, omega_smt_node) + \
               get_base_avc_constraints(res_y1a, omega_smt_node) + \
               get_base_avc_constraints(res_y2a, omega_smt_node)
    setup_lq.append(avc_add_smt_logic(y1, a, res_y1a, omega_smt_node))
    setup_lq.append(avc_add_smt_logic(y2, a, res_y2a, omega_smt_node))
    premise_lq = And(avc_equiv_smt(res_y1a, b_target), avc_equiv_smt(res_y2a, b_target))
    conclusion_lq = avc_equiv_smt(y1, y2)
    property_lq_unique = Implies(premise_lq, conclusion_lq)
    prove_or_find_counterexample_smt(f"{property_name_base} (Left: y+a=b)", omega_val_py, setup_lq, property_lq_unique, [a,b_target,y1,y2], True)


# F. Cancellation Laws
def smt_test_F_additive_cancellation(omega_val_py: int):
    property_name = "SMT F: Additive Cancellation (a+c ~ b+c => a ~ b)"
    expected_to_hold = (omega_val_py <= 2) # Fails for Omega >= 3
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_fcancA_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_fcancA_{omega_val_py}")
    c = create_symbolic_avc_val(f"c_fcancA_{omega_val_py}")
    res_ac = create_symbolic_avc_val(f"res_ac_fcancA_{omega_val_py}")
    res_bc = create_symbolic_avc_val(f"res_bc_fcancA_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(res_ac, omega_smt_node) + \
            get_base_avc_constraints(res_bc, omega_smt_node)
    setup.append(avc_add_smt_logic(a,c,res_ac,omega_smt_node))
    setup.append(avc_add_smt_logic(b,c,res_bc,omega_smt_node))

    premise = avc_equiv_smt(res_ac, res_bc)
    conclusion = avc_equiv_smt(a,b)
    property_formula = Implies(premise, conclusion)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b,c], expected_to_hold)

def smt_test_F_multiplicative_cancellation(omega_val_py: int):
    property_name = "SMT F: Multiplicative Cancellation (ac ~ bc AND c!=ZU => a ~ b)"
    expected_to_hold = (omega_val_py <= 1) # Likely fails for Omega >= 2 due to AREO_UNIO
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_fcancM_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_fcancM_{omega_val_py}")
    c = create_symbolic_avc_val(f"c_fcancM_{omega_val_py}")
    res_ac = create_symbolic_avc_val(f"res_ac_fcancM_{omega_val_py}")
    res_bc = create_symbolic_avc_val(f"res_bc_fcancM_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(res_ac, omega_smt_node) + \
            get_base_avc_constraints(res_bc, omega_smt_node)
    setup.append(avc_mul_smt_logic(a,c,res_ac,omega_smt_node))
    setup.append(avc_mul_smt_logic(b,c,res_bc,omega_smt_node))

    c_is_not_zu = Not(c["is_zero"]) # c is not ZERO_UNIO
    premise = And(avc_equiv_smt(res_ac, res_bc), c_is_not_zu)
    conclusion = avc_equiv_smt(a,b)
    property_formula = Implies(premise, conclusion)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b,c], expected_to_hold)

# G. Idempotence and Nilpotence
def smt_test_G1_additive_idempotence(omega_val_py: int):
    property_name = "SMT G.1: Additive Idempotence (a+a ~ a)"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_g1_{omega_val_py}")
    res_aa = create_symbolic_avc_val(f"res_aa_g1_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(res_aa, omega_smt_node)
    setup.append(avc_add_smt_logic(a,a,res_aa,omega_smt_node))
    property_formula = avc_equiv_smt(res_aa, a)
    # Expected to hold only if a is Unio (ZU or AU). Fails for DFI.
    # So, this universal claim is expected to be False for Omega > 1.
    expected = (omega_val_py == 1) # Only Unio exists
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a], expected)

def smt_test_G2_multiplicative_idempotence(omega_val_py: int):
    property_name = "SMT G.2: Multiplicative Idempotence (a*a ~ a)"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_g2_{omega_val_py}")
    res_aa = create_symbolic_avc_val(f"res_aa_g2_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(res_aa, omega_smt_node)
    setup.append(avc_mul_smt_logic(a,a,res_aa,omega_smt_node))
    property_formula = avc_equiv_smt(res_aa, a)
    # Expected to hold for ZU, AU, and Fp(1) (if 1 < Omega). Fails for other DFI.
    # Universal claim expected to be False for Omega > 2 (where other DFIs exist).
    # For Omega=2, DFI={1}, 1*1=1. ZU*ZU=ZU, AU*AU=AU. So holds for Omega=2.
    expected = (omega_val_py <= 2)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a], expected)

# G.3 Additive Nilpotence (Order of Elements) is more complex for SMT as it requires iteration or quantifiers over n.
# We can test for a fixed small n, or if every element has *some* order.
# For a finite loop, every element must reach identity. This is tied to inverse existence.

# H. Substructure Exploration
def smt_test_H1_dfi_closure_add(omega_val_py: int):
    property_name = "SMT H.1: DFI Closure under Addition"
    if omega_val_py <= 1: # No DFI
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True); print(" (Vacuously true)"); return
        
    omega_smt_node = Int(omega_val_py)
    dfi1 = create_symbolic_avc_val(f"dfi1_h1_{omega_val_py}")
    dfi2 = create_symbolic_avc_val(f"dfi2_h1_{omega_val_py}")
    res_add = create_symbolic_avc_val(f"res_add_h1_{omega_val_py}")
    setup = get_base_avc_constraints(dfi1, omega_smt_node) + \
            get_base_avc_constraints(dfi2, omega_smt_node) + \
            get_base_avc_constraints(res_add, omega_smt_node)
    setup.append(dfi1["is_finite"]); setup.append(dfi2["is_finite"]) # Constrain inputs to be DFI
    setup.append(avc_add_smt_logic(dfi1,dfi2,res_add,omega_smt_node))
    
    property_formula = res_add["is_finite"] # Is the result also DFI?
    # Expected to FAIL if overflow is possible (e.g. Omega=2, 1+1=ZU; Omega=3, 1+2=ZU)
    expected = False if omega_val_py > 1 else True # Only true if Omega=1 (no DFI, premise false)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [dfi1,dfi2], expected)

# I. Complex Chained Operations (Representative Example)
def smt_test_I_add_sub_chain_equivalence(omega_val_py: int):
    property_name = "SMT I: (a+b)-c ~ a+(b-c) (Illustrative Chained Op)"
    # This is NOT generally true even in standard arithmetic.
    # We expect this to FAIL due to non-associativity of underlying ops.
    expected_to_hold = (omega_val_py <= 1) # Only trivially for Omega=1. Maybe Omega=2 if sub is also assoc.
                                         # Given sub is non-assoc, expect False for Omega >=2.
    
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_i1_{omega_val_py}"); b = create_symbolic_avc_val(f"b_i1_{omega_val_py}"); c = create_symbolic_avc_val(f"c_i1_{omega_val_py}")
    apb = create_symbolic_avc_val(f"apb_i1_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_i1_{omega_val_py}")
    bmc = create_symbolic_avc_val(f"bmc_i1_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_i1_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(apb, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(bmc, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)

    setup.append(avc_add_smt_logic(a,b,apb,omega_smt_node)); setup.append(avc_sub_smt_logic(apb,c,lhs,omega_smt_node))
    setup.append(avc_sub_smt_logic(b,c,bmc,omega_smt_node)); setup.append(avc_add_smt_logic(a,bmc,rhs,omega_smt_node))
    
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b,c], expected_to_hold)

# J. Formalizing Pole-Role Asymmetries (Already covered by Experiment B tests)
# We can add specific theorems here if desired, e.g.,
# ForAll DFI_k: (ZERO_UNIO * DFI_k ~ ZERO_UNIO) AND (AREO_UNIO * DFI_k ~ AREO_UNIO)

# --- Main SMT Test Execution (Experiments A, B, C, E, F, G, H, I) ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5]
    print(f"\n\n{'='*30} SMT EXPERIMENTS A-J: COMPREHENSIVE ALGEBRAIC CHARACTERIZATION {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        # From Experiment A & B (Foundations & Unio Roles - already proven to pass)
        # smt_test_A1_totality_all_ops(current_omega_py_val)
        # smt_test_A2_well_definedness_all_ops(current_omega_py_val)
        # smt_test_B1_unio_role_in_addition(current_omega_py_val)
        # smt_test_B2_unio_role_in_subtraction(current_omega_py_val)
        # smt_test_B3_unio_role_in_multiplication(current_omega_py_val)
        # smt_test_B4_unio_role_in_division(current_omega_py_val)

        # From Experiment C (Core Algebraic Laws - already proven to pass as per expectations)
        # smt_test_C1_commutativity_add(current_omega_py_val)
        # smt_test_C1_commutativity_mul(current_omega_py_val)
        # smt_test_C2_associativity_add(current_omega_py_val) # Uses expected_to_hold
        # smt_test_C2_associativity_mul(current_omega_py_val)
        # smt_test_C3_distributivity_mul_over_add(current_omega_py_val) # Uses expected_to_hold
        # smt_test_C4_add_right_quasigroup_existence(current_omega_py_val)
        # smt_test_C4_add_left_quasigroup_existence(current_omega_py_val)
        # smt_test_C4_add_right_inverse_existence(current_omega_py_val)
        # smt_test_C5_add_left_alternative_law(current_omega_py_val) # Uses expected_to_hold
        # smt_test_C5_add_right_alternative_law(current_omega_py_val) # Uses expected_to_hold
        # smt_test_C5_add_power_associativity(current_omega_py_val)
        # smt_test_C5_add_right_bol_identity(current_omega_py_val) # Uses expected_to_hold
        
        print("\n--- Testing E: Uniqueness Properties ---")
        smt_test_E1_uniqueness_additive_inverses(current_omega_py_val)
        smt_test_E2_uniqueness_quasigroup_solutions_add(current_omega_py_val)

        print("\n--- Testing F: Cancellation Laws ---")
        smt_test_F_additive_cancellation(current_omega_py_val)
        smt_test_F_multiplicative_cancellation(current_omega_py_val)

        print("\n--- Testing G: Idempotence ---") # Nilpotence is more complex for SMT
        smt_test_G1_additive_idempotence(current_omega_py_val)
        smt_test_G2_multiplicative_idempotence(current_omega_py_val)

        print("\n--- Testing H: Substructure Exploration ---")
        smt_test_H1_dfi_closure_add(current_omega_py_val)
        
        print("\n--- Testing I: Complex Chained Operations (Illustrative) ---")
        smt_test_I_add_sub_chain_equivalence(current_omega_py_val)

        # Testing J (Formalizing Pole-Role Asymmetries) is largely covered by Experiment B.
        # If specific theorems are desired, they can be added.
        
        print(f"\nSMT Summary for Omega={current_omega_py_val}: Passed={smt_test_results_summary[current_omega_py_val]['passed']}, Failed={smt_test_results_summary[current_omega_py_val]['failed']}")
        print(f"{'='*60}")

    # Overall summary printing
    # ... (same as before) ...
    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY (EXPERIMENTS E-I ADDED) {'='*30}")
    total_passed_smt_all = 0; total_failed_smt_all = 0
    for ov_summary, results in smt_test_results_summary.items():
        total_passed_smt_all += results['passed']; total_failed_smt_all += results['failed']
        print(f"Omega={ov_summary}: Passed={results['passed']}, Failed={results['failed']}")
    if smt_test_failures_details:
        print("\n--- SMT DETAILED FAILURES (EXPERIMENTS E-I ADDED) ---")
        for failure in smt_test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}' (Expect P to hold/witness exist: {failure['expected_to_hold_or_witness_exist']})")
            print(f"    Observed P held/witness found: {failure['property_holds_observed_or_witness_found']}")
            print(f"    Message: {failure['message']}")
            if failure['counterexample_witness']: print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")
    if total_failed_smt_all == 0 and total_passed_smt_all > 0 : print("\n🎉🎉🎉 ALL IMPLEMENTED SMT DEEPER ALGEBRAIC TESTS PASSED SUCCESSFULLY (ACCORDING TO EXPECTATIONS)! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: print("\n🤷🤷🤷 NO SMT DEEPER ALGEBRAIC TESTS WERE RUN / DEFINED. 🤷🤷🤷")
    else: print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT DEEPER ALGEBRAIC TESTS FAILED AGAINST EXPECTATIONS. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")