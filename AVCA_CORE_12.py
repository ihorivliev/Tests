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
ZU_const = create_symbolic_avc_val("ZU_const")
AS_const = create_symbolic_avc_val("AS_const")

def get_unio_const_constraints(omega_smt_node: FNode) -> List[FNode]:
    return [
        ZU_const["is_zero"], Not(ZU_const["is_areo"]), Not(ZU_const["is_finite"]), Equals(ZU_const["val"], Int(0)),
        Not(AS_const["is_zero"]), AS_const["is_areo"], Not(AS_const["is_finite"]), Equals(AS_const["val"], omega_smt_node)
    ]

# --- SMT Test Function Implementations (Expanding Coverage) ---

# Tests from previous runs (mostly general properties, now called from main loop)
def smt_test_totality_all_ops(omega_val_py: int): # Calls prove_or_find_counterexample_smt internally for each op
    property_name_base = "SMT Operation Totality"
    omega_smt_node = Int(omega_val_py)
    ops_logic_map = {"Add": avc_add_smt_logic, "Sub": avc_sub_smt_logic, "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic}
    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a = create_symbolic_avc_val(f"a_tot_{op_name_str}_{omega_val_py}"); b = create_symbolic_avc_val(f"b_tot_{op_name_str}_{omega_val_py}"); res = create_symbolic_avc_val(f"res_tot_{op_name_str}_{omega_val_py}")
        setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node)
        setup.append(op_logic_func(a, b, res, omega_smt_node))
        res_constraints = get_base_avc_constraints(res, omega_smt_node)
        property_res_is_valid = And(res_constraints)
        prove_or_find_counterexample_smt(current_property_name, omega_val_py, setup, property_res_is_valid, [a,b,res], True)

def smt_test_commutativity(op_logic_func: Callable, op_name_str: str, omega_val_py: int):
    property_name = f"SMT Commutativity of {op_name_str}"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_comm_{op_name_str[:3]}_{omega_val_py}"); b = create_symbolic_avc_val(f"b_comm_{op_name_str[:3]}_{omega_val_py}"); res1 = create_symbolic_avc_val(f"res1_comm_{op_name_str[:3]}_{omega_val_py}"); res2 = create_symbolic_avc_val(f"res2_comm_{op_name_str[:3]}_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res1, omega_smt_node) + get_base_avc_constraints(res2, omega_smt_node)
    setup.append(op_logic_func(a, b, res1, omega_smt_node)); setup.append(op_logic_func(b, a, res2, omega_smt_node))
    property_formula = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b], True)

def smt_test_associativity(op_logic_func: Callable, op_name_str: str, omega_val_py: int, expected_to_hold: bool):
    property_name = f"SMT Associativity of {op_name_str}"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_assoc_{op_name_str[:3]}_{omega_val_py}"); b = create_symbolic_avc_val(f"b_assoc_{op_name_str[:3]}_{omega_val_py}"); c = create_symbolic_avc_val(f"c_assoc_{op_name_str[:3]}_{omega_val_py}")
    op_ab = create_symbolic_avc_val(f"op_ab_{op_name_str[:3]}_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_assoc_{op_name_str[:3]}_{omega_val_py}"); op_bc = create_symbolic_avc_val(f"op_bc_{op_name_str[:3]}_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_assoc_{op_name_str[:3]}_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(c, omega_smt_node) + get_base_avc_constraints(op_ab, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(op_bc, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(op_logic_func(a,b,op_ab,omega_smt_node)); setup.append(op_logic_func(op_ab,c,lhs,omega_smt_node))
    setup.append(op_logic_func(b,c,op_bc,omega_smt_node)); setup.append(op_logic_func(a,op_bc,rhs,omega_smt_node))
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, associativity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

def smt_test_distributivity_mul_over_add(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Distributivity of Mul over Add"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_dist_{omega_val_py}"); b = create_symbolic_avc_val(f"b_dist_{omega_val_py}"); c = create_symbolic_avc_val(f"c_dist_{omega_val_py}")
    b_plus_c = create_symbolic_avc_val(f"bpc_dist_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_dist_{omega_val_py}")
    a_mul_b = create_symbolic_avc_val(f"amb_dist_{omega_val_py}"); a_mul_c = create_symbolic_avc_val(f"amc_dist_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_dist_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(c, omega_smt_node) + get_base_avc_constraints(b_plus_c, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(a_mul_b, omega_smt_node) + get_base_avc_constraints(a_mul_c, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(b,c,b_plus_c,omega_smt_node)); setup.append(avc_mul_smt_logic(a,b_plus_c,lhs,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,b,a_mul_b,omega_smt_node)); setup.append(avc_mul_smt_logic(a,c,a_mul_c,omega_smt_node)); setup.append(avc_add_smt_logic(a_mul_b,a_mul_c,rhs,omega_smt_node))
    distributivity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, distributivity_formula, [a,b,c], expected_to_hold)

def smt_test_subtraction_asymmetry(omega_val_py: int): # Already covers all the details needed from python test
    property_name = "SMT Subtraction Asymmetry"
    omega_smt_node = Int(omega_val_py); x = create_symbolic_avc_val(f"x_sub_asym_{omega_val_py}"); zu_const_repr = create_symbolic_avc_val(f"ZU_sub_asym_{omega_val_py}"); au_const_repr = create_symbolic_avc_val(f"AU_sub_asym_{omega_val_py}")
    res_x_m_zu = create_symbolic_avc_val(f"res_xmzu_{omega_val_py}"); res_x_m_au = create_symbolic_avc_val(f"res_xmau_{omega_val_py}"); res_zu_m_x = create_symbolic_avc_val(f"res_zumx_{omega_val_py}"); res_au_m_x = create_symbolic_avc_val(f"res_aumx_{omega_val_py}")
    setup = get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(zu_const_repr, omega_smt_node) + get_base_avc_constraints(au_const_repr, omega_smt_node) + get_base_avc_constraints(res_x_m_zu, omega_smt_node) + get_base_avc_constraints(res_x_m_au, omega_smt_node) + get_base_avc_constraints(res_zu_m_x, omega_smt_node) + get_base_avc_constraints(res_au_m_x, omega_smt_node)
    setup.append(And(zu_const_repr["is_zero"], Not(zu_const_repr["is_areo"]), Not(zu_const_repr["is_finite"]))); setup.append(And(Not(au_const_repr["is_zero"]), au_const_repr["is_areo"], Not(au_const_repr["is_finite"])))
    setup.append(avc_sub_smt_logic(x, zu_const_repr, res_x_m_zu, omega_smt_node)); setup.append(avc_sub_smt_logic(x, au_const_repr, res_x_m_au, omega_smt_node))
    prop_x_minus_unio_is_x = And(avc_equiv_smt(res_x_m_zu, x), avc_equiv_smt(res_x_m_au, x))
    setup.append(avc_sub_smt_logic(zu_const_repr, x, res_zu_m_x, omega_smt_node)); setup.append(avc_sub_smt_logic(au_const_repr, x, res_au_m_x, omega_smt_node))
    prop_unio_minus_x_behavior = And(Implies(x["is_finite"], And(avc_equiv_smt(res_zu_m_x, au_const_repr), avc_equiv_smt(res_au_m_x, au_const_repr))),Implies(Or(x["is_zero"], x["is_areo"]), And(avc_equiv_smt(res_zu_m_x, zu_const_repr), avc_equiv_smt(res_au_m_x, au_const_repr))))
    full_asymmetry_property = And(prop_x_minus_unio_is_x, prop_unio_minus_x_behavior)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, full_asymmetry_property, [x, zu_const_repr, au_const_repr], True)

def smt_test_dfi_haven(omega_val_py: int): # Already covers Add, Mul, Sub, Div DFI Haven
    property_name_base = "SMT DFI-Haven"
    if omega_val_py <= 1:
        prove_or_find_counterexample_smt(f"{property_name_base} (Vacuously True)", omega_val_py, [], TRUE(), [], True)
        print(f"    (Vacuously true for Omega={omega_val_py} as DFI is empty or non-existent)")
        return
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_dfih_{omega_val_py}"); b = create_symbolic_avc_val(f"b_dfih_{omega_val_py}")
    dfi_constraints_ab = [ a["is_finite"], b["is_finite"] ]
    # Add
    res_add = create_symbolic_avc_val(f"res_add_dfih_{omega_val_py}"); setup_add = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res_add, omega_smt_node) + dfi_constraints_ab; setup_add.append(avc_add_smt_logic(a,b,res_add,omega_smt_node)); sum_val = a["val"] + b["val"]; expected_add_fp = And(Not(res_add["is_zero"]), Not(res_add["is_areo"]), res_add["is_finite"], Equals(res_add["val"], sum_val)); expected_add_zu = And(res_add["is_zero"], Not(res_add["is_areo"]), Not(res_add["is_finite"])); prop_add_dfi = Ite(sum_val < omega_smt_node, expected_add_fp, expected_add_zu); prove_or_find_counterexample_smt(f"{property_name_base} (Addition)", omega_val_py, setup_add, prop_add_dfi, [a,b], True)
    # Mul
    res_mul = create_symbolic_avc_val(f"res_mul_dfih_{omega_val_py}"); setup_mul = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res_mul, omega_smt_node) + dfi_constraints_ab; setup_mul.append(avc_mul_smt_logic(a,b,res_mul,omega_smt_node)); prod_val = a["val"] * b["val"]; expected_mul_fp = And(Not(res_mul["is_zero"]), Not(res_mul["is_areo"]), res_mul["is_finite"], Equals(res_mul["val"], prod_val)); expected_mul_au = And(Not(res_mul["is_zero"]), res_mul["is_areo"], Not(res_mul["is_finite"])) # Corrected closing parenthesis
    prop_mul_dfi = Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), expected_mul_fp, expected_mul_au); prove_or_find_counterexample_smt(f"{property_name_base} (Multiplication)", omega_val_py, setup_mul, prop_mul_dfi, [a,b], True)
    # Sub
    res_sub = create_symbolic_avc_val(f"res_sub_dfih_{omega_val_py}"); setup_sub = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res_sub, omega_smt_node) + dfi_constraints_ab; setup_sub.append(avc_sub_smt_logic(a,b,res_sub,omega_smt_node)); diff_val = a["val"] - b["val"]; expected_sub_fp = And(Not(res_sub["is_zero"]), Not(res_sub["is_areo"]), res_sub["is_finite"], Equals(res_sub["val"], diff_val)); expected_sub_au = And(Not(res_sub["is_zero"]), res_sub["is_areo"], Not(res_sub["is_finite"])) # Corrected closing parenthesis
    prop_sub_dfi = Ite(a["val"] > b["val"], expected_sub_fp, expected_sub_au); prove_or_find_counterexample_smt(f"{property_name_base} (Subtraction)", omega_val_py, setup_sub, prop_sub_dfi, [a,b], True)
    # Div
    res_div = create_symbolic_avc_val(f"res_div_dfih_{omega_val_py}"); q_div_haven = Symbol(f"q_dfih_div_{omega_val_py}", SMT_INT_TYPE); r_div_haven = Symbol(f"r_dfih_div_{omega_val_py}", SMT_INT_TYPE); setup_div = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res_div, omega_smt_node) + dfi_constraints_ab; div_constraints_prop = Implies(b["is_finite"], And(Equals(a["val"], q_div_haven * b["val"] + r_div_haven), r_div_haven >= Int(0), r_div_haven < b["val"])); setup_div.append(div_constraints_prop); setup_div.append(avc_div_smt_logic(a,b,res_div,omega_smt_node)); valid_dfi_quot_cond_prop = Implies(b["is_finite"], And(Equals(r_div_haven, Int(0)), q_div_haven >= Int(1), q_div_haven < omega_smt_node)); expected_div_fp = And(Not(res_div["is_zero"]), Not(res_div["is_areo"]), res_div["is_finite"], Equals(res_div["val"], q_div_haven)); expected_div_au = And(Not(res_div["is_zero"]), res_div["is_areo"], Not(res_div["is_finite"])); prop_div_dfi = Ite(valid_dfi_quot_cond_prop, expected_div_fp, expected_div_au); prove_or_find_counterexample_smt(f"{property_name_base} (Division)", omega_val_py, setup_div, prop_div_dfi, [a,b,q_div_haven,r_div_haven], True)

def smt_test_stuck_at_areo(omega_val_py: int): # Already covers both ZU-DFI and AU-DFI
    property_name = "SMT Stuck-at-Areo (Unio - DFI_k ~ AREO_UNIO)"
    if omega_val_py <= 1:
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True)
        print(f"    (Vacuously true for Omega={omega_val_py} as DFI is empty)")
        return
    omega_smt_node = Int(omega_val_py); k_dfi = create_symbolic_avc_val(f"k_dfi_saa_{omega_val_py}"); zu_const = create_symbolic_avc_val(f"ZU_saa_{omega_val_py}"); au_const = create_symbolic_avc_val(f"AU_saa_{omega_val_py}"); res_zu_m_k = create_symbolic_avc_val(f"res_zumk_saa_{omega_val_py}"); res_au_m_k = create_symbolic_avc_val(f"res_aumk_saa_{omega_val_py}")
    setup = get_base_avc_constraints(k_dfi, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node) + get_base_avc_constraints(au_const, omega_smt_node) + get_base_avc_constraints(res_zu_m_k, omega_smt_node) + get_base_avc_constraints(res_au_m_k, omega_smt_node)
    setup.append(k_dfi["is_finite"]); setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"]))); setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))
    setup.append(avc_sub_smt_logic(zu_const, k_dfi, res_zu_m_k, omega_smt_node)); setup.append(avc_sub_smt_logic(au_const, k_dfi, res_au_m_k, omega_smt_node))
    property_formula = And(avc_equiv_smt(res_zu_m_k, au_const), avc_equiv_smt(res_au_m_k, au_const))
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [k_dfi, zu_const, au_const], True)

def smt_test_full_circle_addition(omega_val_py: int): # Already covers ZU+X, AU+X, X+ZU, X+AU
    property_name = "SMT Full-Circle Addition (a + Unio ~ a, Unio + a ~ a)"
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_fca_{omega_val_py}"); zu_const = create_symbolic_avc_val(f"ZU_fca_{omega_val_py}"); au_const = create_symbolic_avc_val(f"AU_fca_{omega_val_py}")
    res_a_p_zu = create_symbolic_avc_val(f"res_apzu_fca_{omega_val_py}"); res_a_p_au = create_symbolic_avc_val(f"res_apau_fca_{omega_val_py}"); res_zu_p_a = create_symbolic_avc_val(f"res_zupa_fca_{omega_val_py}"); res_au_p_a = create_symbolic_avc_val(f"res_aupa_fca_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node) + get_base_avc_constraints(au_const, omega_smt_node) + get_base_avc_constraints(res_a_p_zu, omega_smt_node) + get_base_avc_constraints(res_a_p_au, omega_smt_node) + get_base_avc_constraints(res_zu_p_a, omega_smt_node) + get_base_avc_constraints(res_au_p_a, omega_smt_node)
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"]))); setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))
    setup.append(avc_add_smt_logic(a, zu_const, res_a_p_zu, omega_smt_node)); setup.append(avc_add_smt_logic(a, au_const, res_a_p_au, omega_smt_node))
    setup.append(avc_add_smt_logic(zu_const, a, res_zu_p_a, omega_smt_node)); setup.append(avc_add_smt_logic(au_const, a, res_au_p_a, omega_smt_node))
    property_formula = And(avc_equiv_smt(res_a_p_zu, a), avc_equiv_smt(res_a_p_au, a), avc_equiv_smt(res_zu_p_a, a), avc_equiv_smt(res_au_p_a, a))
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a, zu_const, au_const], True)

def smt_test_omega_1_specifics(omega_val_py: int): # Already covers Unio op Unio for all ops
    property_name = "SMT Omega=1 Specifics (All ops Unio op Unio -> Unio)"
    if omega_val_py != 1:
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True, is_existential=False)
        print(f"    (N/A for Omega={omega_val_py})")
        return
    omega_smt_node = Int(1); a_unio = create_symbolic_avc_val(f"a_o1_{omega_val_py}"); b_unio = create_symbolic_avc_val(f"b_o1_{omega_val_py}")
    res_add = create_symbolic_avc_val(f"res_add_o1_{omega_val_py}"); res_sub = create_symbolic_avc_val(f"res_sub_o1_{omega_val_py}"); res_mul = create_symbolic_avc_val(f"res_mul_o1_{omega_val_py}"); res_div = create_symbolic_avc_val(f"res_div_o1_{omega_val_py}")
    setup = get_base_avc_constraints(a_unio, omega_smt_node) + get_base_avc_constraints(b_unio, omega_smt_node) + get_base_avc_constraints(res_add, omega_smt_node) + get_base_avc_constraints(res_sub, omega_smt_node) + get_base_avc_constraints(res_mul, omega_smt_node) + get_base_avc_constraints(res_div, omega_smt_node)
    setup.append(Or(a_unio["is_zero"], a_unio["is_areo"])); setup.append(Or(b_unio["is_zero"], b_unio["is_areo"]))
    setup.append(avc_add_smt_logic(a_unio, b_unio, res_add, omega_smt_node)); setup.append(avc_sub_smt_logic(a_unio, b_unio, res_sub, omega_smt_node)); setup.append(avc_mul_smt_logic(a_unio, b_unio, res_mul, omega_smt_node)); setup.append(avc_div_smt_logic(a_unio, b_unio, res_div, omega_smt_node))
    prop_add_res_is_unio = Or(res_add["is_zero"], res_add["is_areo"]); prop_sub_res_is_unio = Or(res_sub["is_zero"], res_sub["is_areo"]); prop_mul_res_is_unio = Or(res_mul["is_zero"], res_mul["is_areo"]); prop_div_res_is_unio = Or(res_div["is_zero"], res_div["is_areo"])
    full_omega1_property = And(prop_add_res_is_unio, prop_sub_res_is_unio, prop_mul_res_is_unio, prop_div_res_is_unio)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, full_omega1_property, [a_unio, b_unio], True)

def smt_test_omega_2_algebra(omega_val_py: int): # Already covers 1+1~ZU, 1*1~Fp(1)
    property_name_base = "SMT Omega=2 Algebra"
    if omega_val_py != 2:
        prove_or_find_counterexample_smt(property_name_base, omega_val_py, [], TRUE(), [], True)
        print(f"    (N/A for Omega={omega_val_py})")
        return
    omega_smt_node = Int(2); fp1_const = create_symbolic_avc_val(f"Fp1_o2_{omega_val_py}"); zu_const = create_symbolic_avc_val(f"ZU_o2_{omega_val_py}")
    setup_const = get_base_avc_constraints(fp1_const, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node); setup_const.append(And(fp1_const["is_finite"], Equals(fp1_const["val"], Int(1)))); setup_const.append(zu_const["is_zero"])
    res_1p1 = create_symbolic_avc_val(f"res1p1_o2_{omega_val_py}"); setup_1p1 = setup_const + get_base_avc_constraints(res_1p1, omega_smt_node); setup_1p1.append(avc_add_smt_logic(fp1_const, fp1_const, res_1p1, omega_smt_node)); prop_1p1 = avc_equiv_smt(res_1p1, zu_const); prove_or_find_counterexample_smt(f"{property_name_base} - 1+1~ZU", omega_val_py, setup_1p1, prop_1p1, [fp1_const, zu_const, res_1p1], True)
    res_1x1 = create_symbolic_avc_val(f"res1x1_o2_{omega_val_py}"); setup_1x1 = setup_const + get_base_avc_constraints(res_1x1, omega_smt_node); setup_1x1.append(avc_mul_smt_logic(fp1_const, fp1_const, res_1x1, omega_smt_node)); prop_1x1 = avc_equiv_smt(res_1x1, fp1_const); prove_or_find_counterexample_smt(f"{property_name_base} - 1*1~Fp(1)", omega_val_py, setup_1x1, prop_1x1, [fp1_const, res_1x1], True)

def smt_test_add_right_quasigroup_existence(omega_val_py: int): # Already covers ForAll a,b Exists x: a+x ~ b
    property_name = "SMT Additive Right Quasigroup (Existence: ForAll a,b Exists x: a+x ~ b)"
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_rqg_{omega_val_py}"); b = create_symbolic_avc_val(f"b_rqg_{omega_val_py}"); x = create_symbolic_avc_val(f"x_rqg_{omega_val_py}"); res_ax = create_symbolic_avc_val(f"res_ax_rqg_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(res_ax, omega_smt_node)
    setup.append(avc_add_smt_logic(a, x, res_ax, omega_smt_node)); property_inner_exists = avc_equiv_smt(res_ax, b)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_inner_exists, [a,b,x], expect_property_to_hold=True, is_existential=True)

def smt_test_add_left_quasigroup_existence(omega_val_py: int): # Already covers ForAll a,b Exists y: y+a ~ b
    property_name = "SMT Additive Left Quasigroup (Existence: ForAll a,b Exists y: y+a ~ b)"
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_lqg_{omega_val_py}"); b = create_symbolic_avc_val(f"b_lqg_{omega_val_py}"); y = create_symbolic_avc_val(f"y_lqg_{omega_val_py}"); res_ya = create_symbolic_avc_val(f"res_ya_lqg_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(y, omega_smt_node) + get_base_avc_constraints(res_ya, omega_smt_node)
    setup.append(avc_add_smt_logic(y, a, res_ya, omega_smt_node)); property_inner_exists = avc_equiv_smt(res_ya, b)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_inner_exists, [a,b,y], expect_property_to_hold=True, is_existential=True)

def smt_test_add_right_inverse_existence(omega_val_py: int): # Already covers ForAll a Exists x: a+x ~ ZS
    property_name = "SMT Additive Right Inverse (Existence: ForAll a Exists x: a+x ~ ZS)"
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_rinv_{omega_val_py}"); x = create_symbolic_avc_val(f"x_rinv_{omega_val_py}"); res_ax = create_symbolic_avc_val(f"res_ax_rinv_{omega_val_py}")
    zs_target = create_symbolic_avc_val(f"zs_target_rinv_{omega_val_py}"); setup_zs_target = get_base_avc_constraints(zs_target, omega_smt_node) + [zs_target["is_zero"]]
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(res_ax, omega_smt_node) + setup_zs_target
    setup.append(avc_add_smt_logic(a, x, res_ax, omega_smt_node)); property_inner_exists = avc_equiv_smt(res_ax, zs_target)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_inner_exists, [a,x], expect_property_to_hold=True, is_existential=True)

def smt_test_add_left_alternative_law(omega_val_py: int): # Already covers (a+a)+b ~ a+(a+b)
    property_name = "SMT Additive Left Alternative Law ((a+a)+b ~ a+(a+b))"
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_lal_{omega_val_py}"); b = create_symbolic_avc_val(f"b_lal_{omega_val_py}")
    a_plus_a = create_symbolic_avc_val(f"apa_lal_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_lal_{omega_val_py}"); a_plus_b = create_symbolic_avc_val(f"apb_lal_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_lal_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(a_plus_a, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(a_plus_b, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(a,a,a_plus_a,omega_smt_node)); setup.append(avc_add_smt_logic(a_plus_a,b,lhs,omega_smt_node)); setup.append(avc_add_smt_logic(a,b,a_plus_b,omega_smt_node)); setup.append(avc_add_smt_logic(a,a_plus_b,rhs,omega_smt_node))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b], expect_property_to_hold=(omega_val_py <= 2)) # It fails for Omega >= 3

def smt_test_add_right_alternative_law(omega_val_py: int): # New test
    property_name = f"SMT Additive Right Alternative Law ((b+a)+a ~ b+(a+a))"
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_ral_{omega_val_py}"); b = create_symbolic_avc_val(f"b_ral_{omega_val_py}")
    b_plus_a = create_symbolic_avc_val(f"bpa_ral_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_ral_{omega_val_py}"); a_plus_a = create_symbolic_avc_val(f"apa_ral_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_ral_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(b_plus_a, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(a_plus_a, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(b,a,b_plus_a,omega_smt_node)); setup.append(avc_add_smt_logic(b_plus_a,a,lhs,omega_smt_node)); setup.append(avc_add_smt_logic(a,a,a_plus_a,omega_smt_node)); setup.append(avc_add_smt_logic(b,a_plus_a,rhs,omega_smt_node))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b], expect_property_to_hold=(omega_val_py <= 2)) # It fails for Omega >= 3

def smt_test_add_power_associativity(omega_val_py: int): # Already covers (a+a)+a ~ a+(a+a)
    property_name = f"SMT Additive Power Associativity ((a+a)+a ~ a+(a+a))"
    omega_smt_node = Int(omega_val_py); a = create_symbolic_avc_val(f"a_pa_{omega_val_py}")
    a_plus_a_lhs = create_symbolic_avc_val(f"apa_lhs_pa_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_pa_{omega_val_py}")
    a_plus_a_rhs = create_symbolic_avc_val(f"apa_rhs_pa_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_pa_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(a_plus_a_lhs, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(a_plus_a_rhs, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(a,a,a_plus_a_lhs,omega_smt_node)); setup.append(avc_add_smt_logic(a_plus_a_lhs,a,lhs,omega_smt_node)); setup.append(avc_add_smt_logic(a,a,a_plus_a_rhs,omega_smt_node)); setup.append(avc_add_smt_logic(a,a_plus_a_rhs,rhs,omega_smt_node))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a], expect_property_to_hold=True)

def smt_test_add_right_bol_identity(omega_val_py: int): # Already covers (((x+y)+z)+y ~ x+((y+z)+y))
    property_name = f"SMT Additive Right Bol Identity"
    omega_smt_node = Int(omega_val_py); x = create_symbolic_avc_val(f"x_rbol_{omega_val_py}"); y = create_symbolic_avc_val(f"y_rbol_{omega_val_py}"); z = create_symbolic_avc_val(f"z_rbol_{omega_val_py}")
    xy = create_symbolic_avc_val(f"xy_rbol_{omega_val_py}"); xyz = create_symbolic_avc_val(f"xyz_rbol_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_rbol_{omega_val_py}")
    yz = create_symbolic_avc_val(f"yz_rbol_{omega_val_py}"); yzy = create_symbolic_avc_val(f"yzy_rbol_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_rbol_{omega_val_py}")
    setup = get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(y, omega_smt_node) + get_base_avc_constraints(z, omega_smt_node) + get_base_avc_constraints(xy, omega_smt_node) + get_base_avc_constraints(xyz, omega_smt_node) + get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(yz, omega_smt_node) + get_base_avc_constraints(yzy, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(x,y,xy,omega_smt_node)); setup.append(avc_add_smt_logic(xy,z,xyz,omega_smt_node)); setup.append(avc_add_smt_logic(xyz,y,lhs,omega_smt_node))
    setup.append(avc_add_smt_logic(y,z,yz,omega_smt_node)); setup.append(avc_add_smt_logic(yz,y,yzy,omega_smt_node)); setup.append(avc_add_smt_logic(x,yzy,rhs,omega_smt_node))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [x,y,z], expect_property_to_hold=(omega_val_py <= 2)) # It fails for Omega >= 3

# --- NEW TESTS for missing properties ---

def smt_test_mul_identity_existence(omega_val_py: int):
    property_name = "SMT Multiplicative Identity Existence (Fp(1) is universal for Omega>1)" # Updated property name to reflect new truth
    omega_smt_node = Int(omega_val_py)

    if omega_val_py == 1:
        # For Omega=1, ZU_const is the identity.
        a_sym_test = create_symbolic_avc_val(f"a_mul_id_o1_{omega_val_py}")
        setup_o1 = get_base_avc_constraints(a_sym_test, omega_smt_node) + \
                   get_base_avc_constraints(ZU_const, omega_smt_node) + \
                   get_unio_const_constraints(omega_smt_node)
        
        res_a_zu = create_symbolic_avc_val(f"res_a_zu_o1_{omega_val_py}")
        res_zu_a = create_symbolic_avc_val(f"res_zu_a_o1_{omega_val_py}")
        setup_o1.append(avc_mul_smt_logic(a_sym_test, ZU_const, res_a_zu, omega_smt_node))
        setup_o1.append(avc_mul_smt_logic(ZU_const, a_sym_test, res_zu_a, omega_smt_node))
        
        prop_o1 = And(avc_equiv_smt(res_a_zu, a_sym_test), avc_equiv_smt(res_zu_a, a_sym_test))
        prove_or_find_counterexample_smt(
            "SMT Multiplicative Identity Existence (Omega=1)", omega_val_py, setup_o1, prop_o1,
            [a_sym_test, ZU_const], expect_property_to_hold=True # ZU is identity for Omega=1
        )
    else: # Omega > 1
        # Test that Fp(1) IS a universal identity for Omega > 1. This is the new truth.
        a_sym_test_fp1_id = create_symbolic_avc_val(f"a_is_fp1_id_{omega_val_py}") # Renamed for clarity
        e_fp1_candidate = create_symbolic_avc_val(f"e_fp1_id_cand_{omega_val_py}")
        
        res_a_e_fp1 = create_symbolic_avc_val(f"res_a_e_fp1_{omega_val_py}")
        res_e_a_fp1 = create_symbolic_avc_val(f"res_e_a_fp1_{omega_val_py}")

        setup_fp1 = get_base_avc_constraints(a_sym_test_fp1_id, omega_smt_node) + \
                    get_base_avc_constraints(e_fp1_candidate, omega_smt_node) + \
                    get_base_avc_constraints(res_a_e_fp1, omega_smt_node) + \
                    get_base_avc_constraints(res_e_a_fp1, omega_smt_node) + \
                    get_unio_const_constraints(omega_smt_node) # For ZU_const, AS_const
        
        # Constrain e_fp1_candidate to be Fp(1)
        setup_fp1.append(e_fp1_candidate["is_finite"])
        setup_fp1.append(Equals(e_fp1_candidate["val"], Int(1)))

        setup_fp1.append(avc_mul_smt_logic(a_sym_test_fp1_id, e_fp1_candidate, res_a_e_fp1, omega_smt_node))
        setup_fp1.append(avc_mul_smt_logic(e_fp1_candidate, a_sym_test_fp1_id, res_e_a_fp1, omega_smt_node))

        prop_fp1_is_identity = And(avc_equiv_smt(res_a_e_fp1, a_sym_test_fp1_id),
                                   avc_equiv_smt(res_e_a_fp1, a_sym_test_fp1_id))
        
        # We now expect this to be TRUE (i.e., Fp(1) IS universal identity for Omega > 1)
        prove_or_find_counterexample_smt(
            property_name, omega_val_py, setup_fp1, prop_fp1_is_identity,
            [a_sym_test_fp1_id, e_fp1_candidate, ZU_const, AS_const], expect_property_to_hold=True # Fp(1) IS universal identity for Omega > 1
        )


def smt_test_non_commutativity_sub(omega_val_py: int): # New Test
    property_name = "SMT Non-Commutativity of Subtraction"
    # Subtraction is expected to be non-commutative for Omega >= 2. Trivial for Omega=1.
    expected_to_hold = (omega_val_py == 1) # Only for Omega=1 (commutativity holds trivially)
    
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_ncsub_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_ncsub_{omega_val_py}")
    res1 = create_symbolic_avc_val(f"res1_ncsub_{omega_val_py}")
    res2 = create_symbolic_avc_val(f"res2_ncsub_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(res1, omega_smt_node) + \
            get_base_avc_constraints(res2, omega_smt_node)

    setup.append(avc_sub_smt_logic(a, b, res1, omega_smt_node))
    setup.append(avc_sub_smt_logic(b, a, res2, omega_smt_node))

    property_formula = avc_equiv_smt(res1, res2) # Commutativity
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        property_formula, [a,b], expect_property_to_hold=expected_to_hold
    )


def smt_test_non_associativity_sub(omega_val_py: int): # New Test
    property_name = "SMT Non-Associativity of Subtraction"
    # Subtraction is expected to be non-associative for Omega >= 2. Trivial for Omega=1.
    expected_to_hold = (omega_val_py == 1) # Associativity is trivial for Omega=1
    
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_nasub_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_nasub_{omega_val_py}")
    c = create_symbolic_avc_val(f"c_nasub_{omega_val_py}")
    
    op_ab = create_symbolic_avc_val(f"op_ab_nasub_{omega_val_py}")
    lhs = create_symbolic_avc_val(f"lhs_nasub_{omega_val_py}")
    op_bc = create_symbolic_avc_val(f"op_bc_nasub_{omega_val_py}")
    rhs = create_symbolic_avc_val(f"rhs_nasub_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(op_ab, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(op_bc, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    setup.append(avc_sub_smt_logic(a,b,op_ab,omega_smt_node))
    setup.append(avc_sub_smt_logic(op_ab,c,lhs,omega_smt_node))
    setup.append(avc_sub_smt_logic(b,c,op_bc,omega_smt_node))
    setup.append(avc_sub_smt_logic(a,op_bc,rhs,omega_smt_node))
    
    associativity_formula = avc_equiv_smt(lhs,rhs)
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        associativity_formula, [a,b,c], expect_property_to_hold=expected_to_hold
    )


def smt_test_non_commutativity_div(omega_val_py: int): # New Test
    property_name = "SMT Non-Commutativity of Division"
    # Division is expected to be non-commutative for Omega >= 3. Trivial for Omega=1,2.
    expected_to_hold = (omega_val_py <= 2) # Commutativity is trivial for Omega=1, and holds for Omega=2
    
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_ncdiv_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_ncdiv_{omega_val_py}")
    res1 = create_symbolic_avc_val(f"res1_ncdiv_{omega_val_py}")
    res2 = create_symbolic_avc_val(f"res2_ncdiv_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(res1, omega_smt_node) + \
            get_base_avc_constraints(res2, omega_smt_node)

    setup.append(avc_div_smt_logic(a, b, res1, omega_smt_node))
    setup.append(avc_div_smt_logic(b, a, res2, omega_smt_node))

    property_formula = avc_equiv_smt(res1, res2)
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        property_formula, [a,b], expect_property_to_hold=expected_to_hold
    )


def smt_test_non_associativity_div(omega_val_py: int): # New Test
    property_name = "SMT Non-Associativity of Division"
    # Division is expected to be non-associative for Omega >= 3. Trivial for Omega=1,2.
    expected_to_hold = (omega_val_py <= 2) # Associativity is trivial for Omega=1,2
    
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_nadiv_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_nadiv_{omega_val_py}")
    c = create_symbolic_avc_val(f"c_nadiv_{omega_val_py}")
    
    op_ab = create_symbolic_avc_val(f"op_ab_nadiv_{omega_val_py}")
    lhs = create_symbolic_avc_val(f"lhs_nadiv_{omega_val_py}")
    op_bc = create_symbolic_avc_val(f"op_bc_nadiv_{omega_val_py}")
    rhs = create_symbolic_avc_val(f"rhs_nadiv_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(op_ab, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(op_bc, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    setup.append(avc_div_smt_logic(a,b,op_ab,omega_smt_node))
    setup.append(avc_div_smt_logic(op_ab,c,lhs,omega_smt_node))
    setup.append(avc_div_smt_logic(b,c,op_bc,omega_smt_node))
    setup.append(avc_div_smt_logic(a,op_bc,rhs,omega_smt_node))
    
    associativity_formula = avc_equiv_smt(lhs,rhs)
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup, 
        associativity_formula, [a,b,c], expect_property_to_hold=expected_to_hold
    )


def smt_test_cancellation_laws_add(omega_val_py: int): # New Test (Additive Cancellation)
    property_name = "SMT Additive Cancellation (a+c ~ b+c => a ~ b)"
    # Expected to hold for Omega <= 2. Fail for Omega >= 3.
    expected_to_hold = (omega_val_py <= 2)

    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_acl_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_acl_{omega_val_py}")
    c = create_symbolic_avc_val(f"c_acl_{omega_val_py}")
    
    ac_res = create_symbolic_avc_val(f"ac_res_{omega_val_py}")
    bc_res = create_symbolic_avc_val(f"bc_res_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(ac_res, omega_smt_node) + \
            get_base_avc_constraints(bc_res, omega_smt_node)

    setup.append(avc_add_smt_logic(a, c, ac_res, omega_smt_node))
    setup.append(avc_add_smt_logic(b, c, bc_res, omega_smt_node))
    
    # Property: (a+c ~ b+c) IMPLIES (a ~ b)
    cancellation_formula = Implies(avc_equiv_smt(ac_res, bc_res), avc_equiv_smt(a, b))
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        cancellation_formula, [a,b,c], expect_property_to_hold=expected_to_hold
    )


def smt_test_cancellation_laws_mul(omega_val_py: int): # New Test (Multiplicative Cancellation)
    property_name = "SMT Multiplicative Cancellation (a*c ~ b*c AND c NOT ZU => a ~ b)"
    # Expected to hold for Omega <= 2. Fail for Omega >= 3. (This is the new truth)
    expected_to_hold = (omega_val_py <= 2)

    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_mcl_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_mcl_{omega_val_py}")
    c = create_symbolic_avc_val(f"c_mcl_{omega_val_py}") # The cancellable element
    
    ac_res = create_symbolic_avc_val(f"ac_res_mcl_{omega_val_py}")
    bc_res = create_symbolic_avc_val(f"bc_res_mcl_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + \
            get_base_avc_constraints(ac_res, omega_smt_node) + \
            get_base_avc_constraints(bc_res, omega_smt_node) + \
            get_unio_const_constraints(omega_smt_node) # For ZU_const

    setup.append(avc_mul_smt_logic(a, c, ac_res, omega_smt_node))
    setup.append(avc_mul_smt_logic(b, c, bc_res, omega_smt_node))

    # Property: (a*c ~ b*c AND c NOT ZU) IMPLIES (a ~ b)
    # The 'c NOT ZU' part means 'Not(avc_equiv_smt(c, ZU_const))'
    cancellation_formula = Implies(
        And(avc_equiv_smt(ac_res, bc_res), Not(avc_equiv_smt(c, ZU_const))),
        avc_equiv_smt(a, b)
    )
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        cancellation_formula, [a,b,c, ZU_const], expect_property_to_hold=expected_to_hold
    )


# --- Main SMT Test Execution ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] 
    print(f"\n\n{'='*30} STARTING PySMT TESTS FOR REVISED CORE AVCA (Comprehensive) {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        # Omega_py is set globally within prove_or_find_counterexample_smt
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        # Basic Foundational Properties (already verified)
        smt_test_totality_all_ops(current_omega_py_val)
        smt_test_commutativity(avc_add_smt_logic, "Addition", current_omega_py_val)
        smt_test_commutativity(avc_mul_smt_logic, "Multiplication", current_omega_py_val)
        add_assoc_expected = (current_omega_py_val <= 2)
        smt_test_associativity(avc_add_smt_logic, "Addition", current_omega_py_val, add_assoc_expected)
        smt_test_associativity(avc_mul_smt_logic, "Multiplication", current_omega_py_val, True)
        distrib_mul_over_add_expected = (current_omega_py_val <= 2)
        smt_test_distributivity_mul_over_add(current_omega_py_val)
        smt_test_subtraction_asymmetry(current_omega_py_val)
        smt_test_dfi_haven(current_omega_py_val) # Tests Add, Mul, Sub, Div DFI Haven
        smt_test_stuck_at_areo(current_omega_py_val)
        smt_test_full_circle_addition(current_omega_py_val)
        
        # Omega-Specific Tests
        if current_omega_py_val == 1:
            smt_test_omega_1_specifics(current_omega_py_val)
        if current_omega_py_val == 2:
            smt_test_omega_2_algebra(current_omega_py_val)
        
        # Loop/Quasigroup Properties
        smt_test_add_right_quasigroup_existence(current_omega_py_val)
        smt_test_add_left_quasigroup_existence(current_omega_py_val)
        smt_test_add_right_inverse_existence(current_omega_py_val)
        smt_test_add_left_alternative_law(current_omega_py_val)
        smt_test_add_right_alternative_law(current_omega_py_val)
        smt_test_add_power_associativity(current_omega_py_val)
        smt_test_add_right_bol_identity(current_omega_py_val)

        # --- NEWLY ADDED COMPREHENSIVE TESTS ---
        print(f"\n--- New Comprehensive Tests for Omega={current_omega_py_val} ---")
        smt_test_mul_identity_existence(current_omega_py_val) # Expected False for Omega > 1, True for Omega=1
        smt_test_non_commutativity_sub(current_omega_py_val) # Expected False for Omega >= 2
        smt_test_non_associativity_sub(current_omega_py_val) # Expected False for Omega >= 2
        smt_test_non_commutativity_div(current_omega_py_val) # Expected False for Omega >= 3
        smt_test_non_associativity_div(current_omega_py_val) # Expected False for Omega >= 3
        smt_test_cancellation_laws_add(current_omega_py_val) # Expected False for Omega >= 3
        smt_test_cancellation_laws_mul(current_omega_py_val) # Expected False for Omega >= 2

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
        print("\n🎉🎉🎉 ALL IMPLEMENTED SMT REVISED CORE AVCA TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    else:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT REVISED CORE AVCA TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")