from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE,
                             Iff)
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

def initialize_smt_omega_results(omega_val: int): # Definition
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

# --- SMT Test Functions for Experiment C: Algebraic Laws ---

# C.1: Commutativity Tests (from AVCA_CORE_7_ext1.py)
def smt_test_C1_commutativity_add(omega_val_py: int):
    # ... (same as smt_test_commutativity(avc_add_smt_logic, "Addition", omega_val_py) from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.1: Commutativity of Addition"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_ca_{omega_val_py}"); b = create_symbolic_avc_val(f"b_ca_{omega_val_py}")
    res1 = create_symbolic_avc_val(f"res1_ca_{omega_val_py}"); res2 = create_symbolic_avc_val(f"res2_ca_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res1, omega_smt_node) + get_base_avc_constraints(res2, omega_smt_node)
    setup.append(avc_add_smt_logic(a, b, res1, omega_smt_node)); setup.append(avc_add_smt_logic(b, a, res2, omega_smt_node))
    property_formula = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b], True)

def smt_test_C1_commutativity_mul(omega_val_py: int):
    # ... (same as smt_test_commutativity(avc_mul_smt_logic, "Multiplication", omega_val_py) from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.1: Commutativity of Multiplication"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_cm_{omega_val_py}"); b = create_symbolic_avc_val(f"b_cm_{omega_val_py}")
    res1 = create_symbolic_avc_val(f"res1_cm_{omega_val_py}"); res2 = create_symbolic_avc_val(f"res2_cm_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res1, omega_smt_node) + get_base_avc_constraints(res2, omega_smt_node)
    setup.append(avc_mul_smt_logic(a, b, res1, omega_smt_node)); setup.append(avc_mul_smt_logic(b, a, res2, omega_smt_node))
    property_formula = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b], True)

# C.2: Associativity Tests (from AVCA_CORE_7_ext1.py)
def smt_test_C2_associativity_add(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    # ... (same as smt_test_associativity(avc_add_smt_logic, "Addition", omega_val_py, expected_to_hold) from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.2: Associativity of Addition"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_aa_{omega_val_py}"); b = create_symbolic_avc_val(f"b_aa_{omega_val_py}"); c = create_symbolic_avc_val(f"c_aa_{omega_val_py}")
    op_ab = create_symbolic_avc_val(f"op_ab_aa_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_aa_{omega_val_py}")
    op_bc = create_symbolic_avc_val(f"op_bc_aa_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_aa_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(op_ab, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(op_bc, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(a,b,op_ab,omega_smt_node)); setup.append(avc_add_smt_logic(op_ab,c,lhs,omega_smt_node))
    setup.append(avc_add_smt_logic(b,c,op_bc,omega_smt_node)); setup.append(avc_add_smt_logic(a,op_bc,rhs,omega_smt_node))
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, associativity_formula, [a,b,c], expected_to_hold)

def smt_test_C2_associativity_mul(omega_val_py: int):
    # ... (same as smt_test_associativity(avc_mul_smt_logic, "Multiplication", omega_val_py, True) from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.2: Associativity of Multiplication"; omega_smt_node = Int(omega_val_py); expected_to_hold = True
    a = create_symbolic_avc_val(f"a_am_{omega_val_py}"); b = create_symbolic_avc_val(f"b_am_{omega_val_py}"); c = create_symbolic_avc_val(f"c_am_{omega_val_py}")
    op_ab = create_symbolic_avc_val(f"op_ab_am_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_am_{omega_val_py}")
    op_bc = create_symbolic_avc_val(f"op_bc_am_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_am_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(op_ab, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(op_bc, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_mul_smt_logic(a,b,op_ab,omega_smt_node)); setup.append(avc_mul_smt_logic(op_ab,c,lhs,omega_smt_node))
    setup.append(avc_mul_smt_logic(b,c,op_bc,omega_smt_node)); setup.append(avc_mul_smt_logic(a,op_bc,rhs,omega_smt_node))
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, associativity_formula, [a,b,c], expected_to_hold)

# C.3: Distributivity Test (from AVCA_CORE_7_ext1.py)
def smt_test_C3_distributivity_mul_over_add(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    # ... (same as smt_test_distributivity_mul_over_add(omega_val_py) from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.3: Distributivity of Mul over Add"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_dist_{omega_val_py}"); b = create_symbolic_avc_val(f"b_dist_{omega_val_py}"); c = create_symbolic_avc_val(f"c_dist_{omega_val_py}")
    b_plus_c = create_symbolic_avc_val(f"bpc_dist_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_dist_{omega_val_py}")
    a_mul_b = create_symbolic_avc_val(f"amb_dist_{omega_val_py}"); a_mul_c = create_symbolic_avc_val(f"amc_dist_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_dist_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(b_plus_c, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(a_mul_b, omega_smt_node) + get_base_avc_constraints(a_mul_c, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(b,c,b_plus_c,omega_smt_node)); setup.append(avc_mul_smt_logic(a,b_plus_c,lhs,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,b,a_mul_b,omega_smt_node)); setup.append(avc_mul_smt_logic(a,c,a_mul_c,omega_smt_node)); setup.append(avc_add_smt_logic(a_mul_b,a_mul_c,rhs,omega_smt_node))
    distributivity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, distributivity_formula, [a,b,c], expected_to_hold)

# C.4: Loop/Quasigroup Properties for Addition (from AVCA_CORE_7_ext1.py)
def smt_test_C4_add_right_quasigroup_existence(omega_val_py: int):
    # ... (same as smt_test_add_right_quasigroup_existence from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.4: Additive Right Quasigroup (Existence)"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_rqg_{omega_val_py}"); b = create_symbolic_avc_val(f"b_rqg_{omega_val_py}"); x = create_symbolic_avc_val(f"x_rqg_{omega_val_py}")
    res_ax = create_symbolic_avc_val(f"res_ax_rqg_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(res_ax, omega_smt_node)
    setup.append(avc_add_smt_logic(a, x, res_ax, omega_smt_node)); property_inner_exists = avc_equiv_smt(res_ax, b)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_inner_exists, [a, b, x], True, True)

def smt_test_C4_add_left_quasigroup_existence(omega_val_py: int):
    # ... (same as smt_test_add_left_quasigroup_existence from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.4: Additive Left Quasigroup (Existence)"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_lqg_{omega_val_py}"); b = create_symbolic_avc_val(f"b_lqg_{omega_val_py}"); y = create_symbolic_avc_val(f"y_lqg_{omega_val_py}")
    res_ya = create_symbolic_avc_val(f"res_ya_lqg_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(y, omega_smt_node) + get_base_avc_constraints(res_ya, omega_smt_node)
    setup.append(avc_add_smt_logic(y, a, res_ya, omega_smt_node)); property_inner_exists = avc_equiv_smt(res_ya, b)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_inner_exists, [a,b,y], True, True)

def smt_test_C4_add_right_inverse_existence(omega_val_py: int):
    # ... (same as smt_test_add_right_inverse_existence from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.4: Additive Right Inverse (Existence)"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_rinv_{omega_val_py}"); x = create_symbolic_avc_val(f"x_rinv_{omega_val_py}"); res_ax = create_symbolic_avc_val(f"res_ax_rinv_{omega_val_py}")
    zs_target = create_symbolic_avc_val(f"zs_target_rinv_{omega_val_py}")
    setup_zs_target = get_base_avc_constraints(zs_target, omega_smt_node) + [zs_target["is_zero"]]
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(res_ax, omega_smt_node) + setup_zs_target
    setup.append(avc_add_smt_logic(a, x, res_ax, omega_smt_node)); property_inner_exists = avc_equiv_smt(res_ax, zs_target)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_inner_exists, [a,x], True, True)

# C.5: Further Loop Theory Properties for Addition (from AVCA_CORE_7_ext1.py)
def smt_test_C5_add_left_alternative_law(omega_val_py: int):
    # From Manuscript Draft1, Section 4.2.7: Expected to hold for Ω≤2, fail for Ω≥3.
    expected_to_hold = (omega_val_py <= 2)
    # ... (same as smt_test_add_left_alternative_law from AVCA_CORE_7_ext1.py, but with correct expected_to_hold)
    property_name = f"SMT C.5: Additive Left Alternative Law"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_lal_{omega_val_py}"); b = create_symbolic_avc_val(f"b_lal_{omega_val_py}")
    a_plus_a = create_symbolic_avc_val(f"apa_lal_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_lal_{omega_val_py}")
    a_plus_b = create_symbolic_avc_val(f"apb_lal_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_lal_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(a_plus_a, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(a_plus_b, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(a,a,a_plus_a,omega_smt_node)); setup.append(avc_add_smt_logic(a_plus_a,b,lhs,omega_smt_node))
    setup.append(avc_add_smt_logic(a,b,a_plus_b,omega_smt_node)); setup.append(avc_add_smt_logic(a,a_plus_b,rhs,omega_smt_node))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b], expected_to_hold)

def smt_test_C5_add_right_alternative_law(omega_val_py: int):
    # From Manuscript Draft1, Section 4.2.8: Expected to hold for Ω≤2, fail for Ω≥3.
    expected_to_hold = (omega_val_py <= 2)
    # ... (same as smt_test_add_right_alternative_law from AVCA_CORE_7_ext1.py, but with correct expected_to_hold)
    property_name = f"SMT C.5: Additive Right Alternative Law"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_ral_{omega_val_py}"); b = create_symbolic_avc_val(f"b_ral_{omega_val_py}")
    b_plus_a = create_symbolic_avc_val(f"bpa_ral_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_ral_{omega_val_py}")
    a_plus_a = create_symbolic_avc_val(f"apa_ral_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_ral_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(b_plus_a, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(a_plus_a, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(b,a,b_plus_a,omega_smt_node)); setup.append(avc_add_smt_logic(b_plus_a,a,lhs,omega_smt_node))
    setup.append(avc_add_smt_logic(a,a,a_plus_a,omega_smt_node)); setup.append(avc_add_smt_logic(b,a_plus_a,rhs,omega_smt_node))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b], expected_to_hold)

def smt_test_C5_add_power_associativity(omega_val_py: int):
    # From Manuscript Draft1, Section 4.2.9: Expected to hold universally.
    expected_to_hold = True
    # ... (same as smt_test_add_power_associativity from AVCA_CORE_7_ext1.py)
    property_name = f"SMT C.5: Additive Power Associativity"; omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_pa_{omega_val_py}")
    a_plus_a_lhs = create_symbolic_avc_val(f"apa_lhs_pa_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_pa_{omega_val_py}")
    a_plus_a_rhs = create_symbolic_avc_val(f"apa_rhs_pa_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_pa_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(a_plus_a_lhs, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(a_plus_a_rhs, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(a,a,a_plus_a_lhs,omega_smt_node)); setup.append(avc_add_smt_logic(a_plus_a_lhs,a,lhs,omega_smt_node))
    setup.append(avc_add_smt_logic(a,a,a_plus_a_rhs,omega_smt_node)); setup.append(avc_add_smt_logic(a,a_plus_a_rhs,rhs,omega_smt_node))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a], expected_to_hold)

def smt_test_C5_add_right_bol_identity(omega_val_py: int):
    # From Manuscript Draft1, Section 4.2 (inferred from SMT output analysis): Expected to hold for Ω≤2, fail for Ω≥3.
    expected_to_hold = (omega_val_py <= 2)
    # ... (same as smt_test_add_right_bol_identity from AVCA_CORE_7_ext1.py, but with correct expected_to_hold)
    property_name = f"SMT C.5: Additive Right Bol Identity"; omega_smt_node = Int(omega_val_py)
    x = create_symbolic_avc_val(f"x_rbol_{omega_val_py}"); y = create_symbolic_avc_val(f"y_rbol_{omega_val_py}"); z = create_symbolic_avc_val(f"z_rbol_{omega_val_py}")
    xy = create_symbolic_avc_val(f"xy_rbol_{omega_val_py}"); xyz = create_symbolic_avc_val(f"xyz_rbol_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_rbol_{omega_val_py}")
    yz = create_symbolic_avc_val(f"yz_rbol_{omega_val_py}"); yzy = create_symbolic_avc_val(f"yzy_rbol_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_rbol_{omega_val_py}")
    setup = get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(y, omega_smt_node) + get_base_avc_constraints(z, omega_smt_node) + \
            get_base_avc_constraints(xy, omega_smt_node) + get_base_avc_constraints(xyz, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(yz, omega_smt_node) + get_base_avc_constraints(yzy, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(x,y,xy,omega_smt_node)); setup.append(avc_add_smt_logic(xy,z,xyz,omega_smt_node)); setup.append(avc_add_smt_logic(xyz,y,lhs,omega_smt_node))
    setup.append(avc_add_smt_logic(y,z,yz,omega_smt_node)); setup.append(avc_add_smt_logic(yz,y,yzy,omega_smt_node)); setup.append(avc_add_smt_logic(x,yzy,rhs,omega_smt_node))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [x,y,z], expected_to_hold)


# --- Main SMT Test Execution (Experiment C) ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5]
    print(f"\n\n{'='*30} SMT EXPERIMENT C: ALGEBRAIC LAW TESTS {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        print("\n--- Testing C.1: Commutativity ---")
        smt_test_C1_commutativity_add(current_omega_py_val)
        smt_test_C1_commutativity_mul(current_omega_py_val) # Assuming mul is also to be tested

        print("\n--- Testing C.2: Associativity ---")
        smt_test_C2_associativity_add(current_omega_py_val)
        smt_test_C2_associativity_mul(current_omega_py_val)

        print("\n--- Testing C.3: Distributivity ---")
        smt_test_C3_distributivity_mul_over_add(current_omega_py_val)
        
        print("\n--- Testing C.4: Additive Loop/Quasigroup Core Properties ---")
        smt_test_C4_add_right_quasigroup_existence(current_omega_py_val)
        smt_test_C4_add_left_quasigroup_existence(current_omega_py_val)
        smt_test_C4_add_right_inverse_existence(current_omega_py_val)
        # Full Circle Addition / Identity is implicitly tested by B.1 and is key for loop

        print("\n--- Testing C.5: Further Additive Loop Theory Properties ---")
        smt_test_C5_add_left_alternative_law(current_omega_py_val)
        smt_test_C5_add_right_alternative_law(current_omega_py_val) # Added this call
        smt_test_C5_add_power_associativity(current_omega_py_val)
        smt_test_C5_add_right_bol_identity(current_omega_py_val)
        
        # Consider adding tests for specific Unio role properties from B if not covered by C's focus
        # e.g., smt_test_B1_unio_role_in_addition(current_omega_py_val) to confirm identity explicitly
        # smt_test_B3_unio_role_in_multiplication for ZU annihilator / AU absorber

        print(f"\nSMT Summary for Omega={current_omega_py_val}: Passed={smt_test_results_summary[current_omega_py_val]['passed']}, Failed={smt_test_results_summary[current_omega_py_val]['failed']}")
        print(f"{'='*60}")

    # Overall summary printing (same as before)
    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY (EXPERIMENT C) {'='*30}")
    total_passed_smt_all = 0; total_failed_smt_all = 0
    for ov_summary, results in smt_test_results_summary.items():
        total_passed_smt_all += results['passed']; total_failed_smt_all += results['failed']
        print(f"Omega={ov_summary}: Passed={results['passed']}, Failed={results['failed']}")
    if smt_test_failures_details:
        print("\n--- SMT DETAILED FAILURES (EXPERIMENT C) ---")
        for failure in smt_test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}' (Expect P to hold/witness exist: {failure['expected_to_hold_or_witness_exist']})")
            print(f"    Observed P held/witness found: {failure['property_holds_observed_or_witness_found']}")
            print(f"    Message: {failure['message']}")
            if failure['counterexample_witness']: print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")
    if total_failed_smt_all == 0 and total_passed_smt_all > 0 : print("\n🎉🎉🎉 ALL IMPLEMENTED SMT ALGEBRAIC LAW TESTS PASSED SUCCESSFULLY (ACCORDING TO EXPECTATIONS)! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: print("\n🤷🤷🤷 NO SMT ALGEBRAIC LAW TESTS WERE RUN / DEFINED. 🤷🤷🤷")
    else: print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT ALGEBRAIC LAW TESTS FAILED AGAINST EXPECTATIONS. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")