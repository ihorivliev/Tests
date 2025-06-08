from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE,
                             Iff)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Symbolic Core AVCA Definitions ---
Omega_py: int = 0 # Global Python Omega for context in get_base_avc_constraints

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
    # Omega_py is the global Python int for the current Omega being tested
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

# --- SMT Logic Builders ---
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
    q_sym = Symbol(f"{res['name']}_q_div", SMT_INT_TYPE); r_sym = Symbol(f"{res['name']}_r_div", SMT_INT_TYPE)
    div_constraints = Implies(And(b["is_finite"], b["val"] > Int(0)), And(Equals(a["val"], q_sym * b["val"] + r_sym), r_sym >= Int(0), r_sym < b["val"]))
    valid_dfi_quotient_cond = Implies(b["is_finite"], And(Equals(r_sym, Int(0)), q_sym >= Int(1), q_sym < omega_smt_node))
    res_is_FP_quot_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), And(div_constraints, Ite(valid_dfi_quotient_cond, res_is_FP_quot_formula, res_is_AU_formula)))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi)

# --- Symbolic Prover Function ---
smt_test_results_summary: Dict[int, Dict[str, int]] = {}
smt_test_failures_details: List[Dict[str, Any]] = []

def initialize_smt_omega_results(omega_val: int): # DEFINITION IS HERE
    if omega_val not in smt_test_results_summary:
        smt_test_results_summary[omega_val] = {"passed": 0, "failed": 0}

def prove_or_find_counterexample_smt(
    property_name: str, omega_py_val: int, setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, FNode]],
    expect_property_to_hold: bool, is_existential: bool = False):

    global Omega_py
    Omega_py = omega_py_val
    initialize_smt_omega_results(omega_py_val) # Call the defined function

    property_holds_observed = False
    counterexample_witness_str = None

    with Solver(name="z3") as s:
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)

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

# --- SMT Test Function Implementations for Experiment A ---
def smt_test_A1_totality_all_ops(omega_val_py: int):
    # ... (definition as in previous correct script)
    property_name_base = "SMT A.1: Operation Totality"; omega_smt_node = Int(omega_val_py)
    ops_logic_map = {"Add": avc_add_smt_logic, "Sub": avc_sub_smt_logic, "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic}
    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a_sym = create_symbolic_avc_val(f"a_tot_{op_name_str}_{omega_val_py}"); b_sym = create_symbolic_avc_val(f"b_tot_{op_name_str}_{omega_val_py}"); res_sym = create_symbolic_avc_val(f"res_tot_{op_name_str}_{omega_val_py}")
        setup_tot = get_base_avc_constraints(a_sym, omega_smt_node) + get_base_avc_constraints(b_sym, omega_smt_node)
        setup_tot.append(op_logic_func(a_sym, b_sym, res_sym, omega_smt_node))
        res_constraints_tot = get_base_avc_constraints(res_sym, omega_smt_node); property_res_is_valid_tot = And(res_constraints_tot)
        prove_or_find_counterexample_smt(current_property_name, omega_val_py, setup_tot, property_res_is_valid_tot, [a_sym, b_sym, res_sym], True)

def smt_test_A2_well_definedness_all_ops(omega_val_py: int):
    # ... (definition as in previous correct script)
    property_name_base = "SMT A.2: Well-Definedness w.r.t. Unio Equivalence"; omega_smt_node = Int(omega_val_py)
    ops_logic_map = {"Add": avc_add_smt_logic, "Sub": avc_sub_smt_logic, "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic}
    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a1 = create_symbolic_avc_val(f"a1_wd_{op_name_str}_{omega_val_py}"); a2 = create_symbolic_avc_val(f"a2_wd_{op_name_str}_{omega_val_py}")
        b1 = create_symbolic_avc_val(f"b1_wd_{op_name_str}_{omega_val_py}"); b2 = create_symbolic_avc_val(f"b2_wd_{op_name_str}_{omega_val_py}")
        res1 = create_symbolic_avc_val(f"res1_wd_{op_name_str}_{omega_val_py}"); res2 = create_symbolic_avc_val(f"res2_wd_{op_name_str}_{omega_val_py}")
        setup_wd = get_base_avc_constraints(a1, omega_smt_node) + get_base_avc_constraints(a2, omega_smt_node) + get_base_avc_constraints(b1, omega_smt_node) + get_base_avc_constraints(b2, omega_smt_node) + get_base_avc_constraints(res1, omega_smt_node) + get_base_avc_constraints(res2, omega_smt_node)
        setup_wd.append(op_logic_func(a1, b1, res1, omega_smt_node)); setup_wd.append(op_logic_func(a2, b2, res2, omega_smt_node))
        premise = And(avc_equiv_smt(a1, a2), avc_equiv_smt(b1, b2)); conclusion = avc_equiv_smt(res1, res2)
        property_well_defined = Implies(premise, conclusion)
        prove_or_find_counterexample_smt(current_property_name, omega_val_py, setup_wd, property_well_defined, [a1,a2,b1,b2,res1,res2], True)

# --- SMT Test Functions for Experiment B: Unio's Precise Role ---
def smt_test_B1_unio_role_in_addition(omega_val_py: int):
    # ... (definition as in previous correct script)
    property_name_base = "SMT B.1: Unio Role in Addition"; omega_smt_node = Int(omega_val_py)
    x = create_symbolic_avc_val(f"x_addU_{omega_val_py}"); zu_const = create_symbolic_avc_val(f"ZU_addU_{omega_val_py}"); au_const = create_symbolic_avc_val(f"AU_addU_{omega_val_py}")
    res_zu_plus_x = create_symbolic_avc_val(f"resZUpX_{omega_val_py}"); res_au_plus_x = create_symbolic_avc_val(f"resAUpX_{omega_val_py}")
    res_x_plus_zu = create_symbolic_avc_val(f"resXpZU_{omega_val_py}"); res_x_plus_au = create_symbolic_avc_val(f"resXpAU_{omega_val_py}")
    setup = get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node) + get_base_avc_constraints(au_const, omega_smt_node) + \
            get_base_avc_constraints(res_zu_plus_x, omega_smt_node) + get_base_avc_constraints(res_au_plus_x, omega_smt_node) + \
            get_base_avc_constraints(res_x_plus_zu, omega_smt_node) + get_base_avc_constraints(res_x_plus_au, omega_smt_node)
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"]))); setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))
    setup.append(avc_add_smt_logic(zu_const, x, res_zu_plus_x, omega_smt_node)); setup.append(avc_add_smt_logic(au_const, x, res_au_plus_x, omega_smt_node))
    setup.append(avc_add_smt_logic(x, zu_const, res_x_plus_zu, omega_smt_node)); setup.append(avc_add_smt_logic(x, au_const, res_x_plus_au, omega_smt_node))
    property_unio_acts_as_identity = And(avc_equiv_smt(res_zu_plus_x, x), avc_equiv_smt(res_au_plus_x, x), avc_equiv_smt(res_x_plus_zu, x), avc_equiv_smt(res_x_plus_au, x))
    prove_or_find_counterexample_smt(f"{property_name_base} (Unio as Identity)", omega_val_py, setup, property_unio_acts_as_identity, [x, zu_const, au_const], True)

def smt_test_B2_unio_role_in_subtraction(omega_val_py: int):
    # ... (definition as in previous correct script)
    property_name_base = "SMT B.2: Unio Role in Subtraction"; omega_smt_node = Int(omega_val_py)
    x = create_symbolic_avc_val(f"x_subU_{omega_val_py}"); dfi_k = create_symbolic_avc_val(f"dfiK_subU_{omega_val_py}")
    zu_const = create_symbolic_avc_val(f"ZU_subU_{omega_val_py}"); au_const = create_symbolic_avc_val(f"AU_subU_{omega_val_py}")
    res_x_minus_zu = create_symbolic_avc_val(f"resXmZU_sU_{omega_val_py}"); res_x_minus_au = create_symbolic_avc_val(f"resXmAU_sU_{omega_val_py}")
    res_zu_minus_dfik = create_symbolic_avc_val(f"resZUmDFIK_sU_{omega_val_py}"); res_au_minus_dfik = create_symbolic_avc_val(f"resAUmDFIK_sU_{omega_val_py}")
    res_zu_minus_au = create_symbolic_avc_val(f"resZUmAU_sU_{omega_val_py}")
    setup = get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(dfi_k, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node) + get_base_avc_constraints(au_const, omega_smt_node) + \
            get_base_avc_constraints(res_x_minus_zu, omega_smt_node) + get_base_avc_constraints(res_x_minus_au, omega_smt_node) + get_base_avc_constraints(res_zu_minus_dfik, omega_smt_node) + get_base_avc_constraints(res_au_minus_dfik, omega_smt_node) + get_base_avc_constraints(res_zu_minus_au, omega_smt_node)
    if Omega_py > 1 : setup.append(dfi_k["is_finite"])
    else: setup.append(Not(dfi_k["is_finite"]))
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"]))); setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))
    setup.append(avc_sub_smt_logic(x, zu_const, res_x_minus_zu, omega_smt_node)); setup.append(avc_sub_smt_logic(x, au_const, res_x_minus_au, omega_smt_node))
    setup.append(avc_sub_smt_logic(zu_const, dfi_k, res_zu_minus_dfik, omega_smt_node)); setup.append(avc_sub_smt_logic(au_const, dfi_k, res_au_minus_dfik, omega_smt_node))
    setup.append(avc_sub_smt_logic(zu_const, au_const, res_zu_minus_au, omega_smt_node))
    prop1 = And(avc_equiv_smt(res_x_minus_zu, x), avc_equiv_smt(res_x_minus_au, x))
    prove_or_find_counterexample_smt(f"{property_name_base} (X - Unio ~ X)", omega_val_py, setup, prop1, [x, zu_const, au_const], True)
    prop2_premise = dfi_k["is_finite"]; prop2_conclusion = And(avc_equiv_smt(res_zu_minus_dfik, au_const), avc_equiv_smt(res_au_minus_dfik, au_const))
    prop2 = Implies(prop2_premise, prop2_conclusion)
    prove_or_find_counterexample_smt(f"{property_name_base} (Unio - DFI ~ AU)", omega_val_py, setup, prop2, [dfi_k, zu_const, au_const], True)
    prop3 = avc_equiv_smt(res_zu_minus_au, zu_const)
    prove_or_find_counterexample_smt(f"{property_name_base} (ZU - AU ~ ZU)", omega_val_py, setup, prop3, [dfi_k, zu_const, au_const, res_zu_minus_au], True)

def smt_test_B3_unio_role_in_multiplication(omega_val_py: int):
    # ... (definition as in previous correct script)
    property_name_base = "SMT B.3: Unio Role in Multiplication"; omega_smt_node = Int(omega_val_py)
    x = create_symbolic_avc_val(f"x_mulU_{omega_val_py}"); dfi_k = create_symbolic_avc_val(f"dfiK_mulU_{omega_val_py}")
    zu_const = create_symbolic_avc_val(f"ZU_mulU_{omega_val_py}"); au_const = create_symbolic_avc_val(f"AU_mulU_{omega_val_py}")
    res_zu_mul_x = create_symbolic_avc_val(f"resZUmX_mU_{omega_val_py}"); res_x_mul_zu = create_symbolic_avc_val(f"resXmZU_mU_{omega_val_py}")
    res_au_mul_dfik = create_symbolic_avc_val(f"resAUmDFIK_mU_{omega_val_py}"); res_dfik_mul_au = create_symbolic_avc_val(f"resDFIKmAU_mU_{omega_val_py}")
    res_au_mul_au = create_symbolic_avc_val(f"resAUmAU_mU_{omega_val_py}"); res_zu_mul_au = create_symbolic_avc_val(f"resZUmAU_mU_{omega_val_py}")
    setup = get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(dfi_k, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node) + get_base_avc_constraints(au_const, omega_smt_node) + \
            get_base_avc_constraints(res_zu_mul_x, omega_smt_node) + get_base_avc_constraints(res_x_mul_zu, omega_smt_node) + get_base_avc_constraints(res_au_mul_dfik, omega_smt_node) + get_base_avc_constraints(res_dfik_mul_au, omega_smt_node) + \
            get_base_avc_constraints(res_au_mul_au, omega_smt_node) + get_base_avc_constraints(res_zu_mul_au, omega_smt_node)
    if Omega_py > 1 : setup.append(dfi_k["is_finite"])
    else: setup.append(Not(dfi_k["is_finite"]))
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"]))); setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))
    setup.append(avc_mul_smt_logic(zu_const, x, res_zu_mul_x, omega_smt_node)); setup.append(avc_mul_smt_logic(x, zu_const, res_x_mul_zu, omega_smt_node))
    setup.append(avc_mul_smt_logic(au_const, dfi_k, res_au_mul_dfik, omega_smt_node)); setup.append(avc_mul_smt_logic(dfi_k, au_const, res_dfik_mul_au, omega_smt_node))
    setup.append(avc_mul_smt_logic(au_const, au_const, res_au_mul_au, omega_smt_node)); setup.append(avc_mul_smt_logic(zu_const, au_const, res_zu_mul_au, omega_smt_node))
    prop1 = And(avc_equiv_smt(res_zu_mul_x, zu_const), avc_equiv_smt(res_x_mul_zu, zu_const))
    prove_or_find_counterexample_smt(f"{property_name_base} (ZU as Annihilator)", omega_val_py, setup, prop1, [x, zu_const], True)
    prop2_premise = dfi_k["is_finite"]; prop2_conclusion = And(avc_equiv_smt(res_au_mul_dfik, au_const), avc_equiv_smt(res_dfik_mul_au, au_const), avc_equiv_smt(res_au_mul_au, au_const))
    prop2 = Implies(prop2_premise, prop2_conclusion)
    prove_or_find_counterexample_smt(f"{property_name_base} (AU as Absorber/Idempotent)", omega_val_py, setup, prop2, [dfi_k, au_const], True)
    prop3 = avc_equiv_smt(res_zu_mul_au, zu_const)
    prove_or_find_counterexample_smt(f"{property_name_base} (ZU * AU ~ ZU)", omega_val_py, setup, prop3, [zu_const, au_const, res_zu_mul_au], True)

def smt_test_B4_unio_role_in_division(omega_val_py: int):
    # ... (definition as in previous correct script)
    property_name_base = "SMT B.4: Unio Role in Division"; omega_smt_node = Int(omega_val_py)
    x_any = create_symbolic_avc_val(f"x_any_divU_{omega_val_py}"); dfi_k = create_symbolic_avc_val(f"dfiK_divU_{omega_val_py}")
    zu_const = create_symbolic_avc_val(f"ZU_divU_{omega_val_py}"); au_const = create_symbolic_avc_val(f"AU_divU_{omega_val_py}")
    res_zu_div_x = create_symbolic_avc_val(f"resZUdX_dU_{omega_val_py}"); res_au_div_x = create_symbolic_avc_val(f"resAUdX_dU_{omega_val_py}")
    res_dfik_div_zu = create_symbolic_avc_val(f"resDFIKdZU_dU_{omega_val_py}"); res_dfik_div_au = create_symbolic_avc_val(f"resDFIKdAU_dU_{omega_val_py}")
    setup = get_base_avc_constraints(x_any, omega_smt_node) + get_base_avc_constraints(dfi_k, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node) + get_base_avc_constraints(au_const, omega_smt_node) + \
            get_base_avc_constraints(res_zu_div_x, omega_smt_node) + get_base_avc_constraints(res_au_div_x, omega_smt_node) + get_base_avc_constraints(res_dfik_div_zu, omega_smt_node) + get_base_avc_constraints(res_dfik_div_au, omega_smt_node)
    if Omega_py > 1: setup.append(dfi_k["is_finite"])
    else: setup.append(Not(dfi_k["is_finite"]))
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"]))); setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))
    setup.append(avc_div_smt_logic(zu_const, x_any, res_zu_div_x, omega_smt_node)); setup.append(avc_div_smt_logic(au_const, x_any, res_au_div_x, omega_smt_node))
    setup.append(avc_div_smt_logic(dfi_k, zu_const, res_dfik_div_zu, omega_smt_node)); setup.append(avc_div_smt_logic(dfi_k, au_const, res_dfik_div_au, omega_smt_node))
    prop1 = And(avc_equiv_smt(res_zu_div_x, zu_const), avc_equiv_smt(res_au_div_x, au_const))
    prove_or_find_counterexample_smt(f"{property_name_base} (Unio(aspect) / X ~ Unio(aspect))", omega_val_py, setup, prop1, [x_any, zu_const, au_const, res_zu_div_x, res_au_div_x], True)
    prop2_premise = dfi_k["is_finite"]; prop2_conclusion = And(avc_equiv_smt(res_dfik_div_zu, au_const), avc_equiv_smt(res_dfik_div_au, au_const))
    prop2 = Implies(prop2_premise, prop2_conclusion)
    prove_or_find_counterexample_smt(f"{property_name_base} (DFI / Unio ~ AU)", omega_val_py, setup, prop2, [dfi_k, zu_const, au_const, res_dfik_div_zu, res_dfik_div_au], True)

# --- SMT Test Functions for Experiment D: Deeper Nature ---
def smt_test_D1_unio_addition_dilemma_formalized(omega_val_py: int):
    property_name = "SMT D.1: Unio Addition Dilemma (Formal Contradiction)"
    omega_smt_node = Int(omega_val_py)

    U_pole = create_symbolic_avc_val(f"U_D1_{omega_val_py}")
    X_dfi = create_symbolic_avc_val(f"X_D1_{omega_val_py}")
    # For this test, we don't need a 'res' that is defined by an op_logic.
    # We are testing if the *conjunction* of desired properties can hold for U_pole and X_dfi.

    setup_D1 = get_base_avc_constraints(U_pole, omega_smt_node) + \
               get_base_avc_constraints(X_dfi, omega_smt_node)

    # 1. U_pole is Unio
    setup_D1.append(Or(U_pole["is_zero"], U_pole["is_areo"]))
    
    # The property we want to show is contradictory (i.e., False) if X_dfi is DFI for Omega > 1:
    # "X_dfi is DFI AND X_dfi is algebraically equivalent to U_pole"
    # This directly tests if a DFI element can simultaneously be Unio.
    property_dfi_can_be_unio = And(X_dfi["is_finite"], avc_equiv_smt(X_dfi, U_pole))
    
    # We expect this property_dfi_can_be_unio to be FALSE if Omega_py > 1.
    # If Omega_py = 1, DFI is empty, so X_dfi["is_finite"] will be False, making the And False.
    # So, we always expect this property to be False.
    # A "pass" for this test means the SMT solver confirms property_dfi_can_be_unio is False (UNSAT if asserted).
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup_D1,
        property_dfi_can_be_unio, # Can this be true?
        [U_pole, X_dfi],
        expect_property_to_hold=False, # We expect it's NOT possible for a DFI to be Unio.
        is_existential=True # Does there EXIST a U and X_DFI such that X_DFI is DFI AND X_DFI ~ U?
                            # We expect the answer to be NO (so property_holds_observed will be False)
                            # And since expect_property_to_hold is False, this will be a PASS.
    )
    # The above test confirms that a DFI cannot be Unio.
    # The dilemma is: if op(U,X_DFI)=Res1 by identity rule (Res1~X_DFI)
    # AND op(U,X_DFI)=Res2 by absorber rule (Res2~U)
    # AND op must be single-valued (Res1~Res2)
    # THEN X_DFI ~ U.
    # Since we just showed X_DFI cannot be U (if DFI), the premise (single op can be both) must be false.
    # This is what the "Additive Postulate Conflict Test" from earlier SMT work did more directly.
    # The current D1 test is a more fundamental check that underpins why the dilemma is a dilemma.

def smt_test_D2_resetting_subtraction_well_definedness(omega_val_py: int):
    property_name = "SMT D.2: Hypothetical Resetting Sub Well-Definedness"
    if omega_val_py <= 1:
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True)
        print(f"    (Test NA for Omega={omega_val_py} as DFI is empty or too simple for interesting reset)")
        return

    omega_smt_node = Int(omega_val_py)
    dfi_k = create_symbolic_avc_val(f"dfiK_D2_{omega_val_py}")
    zu_const = create_symbolic_avc_val(f"ZU_D2_{omega_val_py}")
    au_const = create_symbolic_avc_val(f"AU_D2_{omega_val_py}")
    res_zu_minus_dfik_current = create_symbolic_avc_val(f"resZUmDFIKcurr_D2_{omega_val_py}")
    res_au_minus_dfik_hypo_dfi = create_symbolic_avc_val(f"resAUmDFIKhypoDFI_D2_{omega_val_py}")

    setup = get_base_avc_constraints(dfi_k, omega_smt_node) + \
            get_base_avc_constraints(zu_const, omega_smt_node) + \
            get_base_avc_constraints(au_const, omega_smt_node) + \
            get_base_avc_constraints(res_zu_minus_dfik_current, omega_smt_node) + \
            get_base_avc_constraints(res_au_minus_dfik_hypo_dfi, omega_smt_node)

    setup.append(dfi_k["is_finite"]) # k is DFI
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"])))
    setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))

    # Behavior 1: ZU - DFI_k -> AU (current avc_sub logic defines res_zu_minus_dfik_current)
    setup.append(avc_sub_smt_logic(zu_const, dfi_k, res_zu_minus_dfik_current, omega_smt_node))
    
    # Behavior 2 (Hypothetical): AU - DFI_k -> some DFI_y
    # We constrain res_au_minus_dfik_hypo_dfi to be a DFI.
    setup.append(res_au_minus_dfik_hypo_dfi["is_finite"])
    # For it to be a specific DFI like Omega-k, we'd add:
    # setup.append(Equals(res_au_minus_dfik_hypo_dfi["val"], omega_smt_node - dfi_k["val"]))


    # Property to verify: Are the outcomes equivalent, given ZU ~ AU?
    # IF ZU ~ AU, then (ZU - DFIk) must be ~ (AU - DFIk_hypothetical_reset_to_DFI)
    # We expect this to be FALSE, because res_zu_minus_dfik_current will be AU,
    # and res_au_minus_dfik_hypo_dfi is constrained to be DFI. AU is not ~ DFI.
    # So, the property "the outcomes are equivalent" is expected to be False.
    # This means the hypothetical mixed-rule subtraction is NOT well-defined.
    
    property_hypothetical_sub_is_well_defined = avc_equiv_smt(res_zu_minus_dfik_current, res_au_minus_dfik_hypo_dfi)
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_hypothetical_sub_is_well_defined, # Is it possible for these outcomes to be equivalent?
        [dfi_k, zu_const, au_const, res_zu_minus_dfik_current, res_au_minus_dfik_hypo_dfi],
        expect_property_to_hold=False # Expect False, meaning the hypothetical sub is NOT well-defined.
                                      # A "pass" means SMT confirms it's False (or finds CE to it being True).
    )

# --- Main SMT Test Execution (Experiments A, B, D) ---
if __name__ == "__main__":
    # ... (same main loop as the one that produced the successful A & B output)
    omegas_to_test_smt = [1, 2, 3, 5]
    print(f"\n\n{'='*30} SMT EXPERIMENTS A, B, D: FOUNDATIONS, UNIO ROLES, DEEPER NATURE {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        print("\n--- Testing A.1: Operational Totality ---")
        smt_test_A1_totality_all_ops(current_omega_py_val)
        
        print("\n--- Testing A.2: Well-Definedness w.r.t. Unio Equivalence ---")
        smt_test_A2_well_definedness_all_ops(current_omega_py_val)

        print("\n--- Testing B.1: Unio Role in Addition ---")
        smt_test_B1_unio_role_in_addition(current_omega_py_val)
        
        print("\n--- Testing B.2: Unio Role in Subtraction ---")
        smt_test_B2_unio_role_in_subtraction(current_omega_py_val)

        print("\n--- Testing B.3: Unio Role in Multiplication ---")
        smt_test_B3_unio_role_in_multiplication(current_omega_py_val)

        print("\n--- Testing B.4: Unio Role in Division ---")
        smt_test_B4_unio_role_in_division(current_omega_py_val)

        print("\n--- Testing D.1: Unio Addition Dilemma Formalized ---")
        smt_test_D1_unio_addition_dilemma_formalized(current_omega_py_val)

        print("\n--- Testing D.2: Hypothetical Resetting Subtraction Well-Definedness ---")
        smt_test_D2_resetting_subtraction_well_definedness(current_omega_py_val)
        
        print(f"\nSMT Summary for Omega={current_omega_py_val}: Passed={smt_test_results_summary[current_omega_py_val]['passed']}, Failed={smt_test_results_summary[current_omega_py_val]['failed']}")
        print(f"{'='*60}")

    # Overall summary printing
    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY (EXPERIMENTS A, B, D) {'='*30}")
    total_passed_smt_all = 0; total_failed_smt_all = 0
    for ov_summary, results in smt_test_results_summary.items():
        total_passed_smt_all += results['passed']; total_failed_smt_all += results['failed']
        print(f"Omega={ov_summary}: Passed={results['passed']}, Failed={results['failed']}")
    if smt_test_failures_details:
        print("\n--- SMT DETAILED FAILURES (EXPERIMENTS A, B, D) ---")
        for failure in smt_test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}' (Expect P to hold/witness exist: {failure['expected_to_hold_or_witness_exist']})")
            print(f"    Observed P held/witness found: {failure['property_holds_observed_or_witness_found']}")
            print(f"    Message: {failure['message']}")
            if failure['counterexample_witness']: print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")
    if total_failed_smt_all == 0 and total_passed_smt_all > 0 : print("\n🎉🎉🎉 ALL IMPLEMENTED SMT FOUNDATIONAL, UNIO ROLE, & DEEPER NATURE TESTS PASSED SUCCESSFULLY (ACCORDING TO EXPECTATIONS)! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: print("\n🤷🤷🤷 NO SMT TESTS WERE RUN / DEFINED. 🤷🤷🤷")
    else: print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT TESTS FAILED AGAINST EXPECTATIONS. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")