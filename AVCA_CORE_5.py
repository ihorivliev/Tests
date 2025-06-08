from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE,
                             Iff)
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
    if Omega_py == 1: 
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
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_FP_sum_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], sum_val))
    
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(sum_val < omega_smt_node,
                                res_is_FP_sum_formula, 
                                res_is_ZU_formula
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
    case2 = Implies(And(a_is_unio, b["is_finite"]), res_is_AU_formula)
    
    diff_val = a["val"] - b["val"]
    res_is_FP_diff_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], diff_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(a["val"] > b["val"],
                                res_is_FP_diff_formula, 
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
    res_is_FP_prod_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], prod_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), 
                                res_is_FP_prod_formula, 
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

    # If b is DFI, then b["val"] > 0.
    div_constraints = Implies(b["is_finite"], 
                              And(Equals(a["val"], q_sym * b["val"] + r_sym),
                                  r_sym >= Int(0),
                                  r_sym < b["val"])) 
    
    valid_dfi_quotient_cond = Implies(b["is_finite"],
                                      And(Equals(r_sym, Int(0)), 
                                          q_sym >= Int(1), 
                                          q_sym < omega_smt_node))
    res_is_FP_quot_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))

    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            And(div_constraints, 
                                Ite(valid_dfi_quotient_cond,
                                    res_is_FP_quot_formula, 
                                    res_is_AU_formula 
                                )
                            ))
    return And(case1, case2, case3_dfi_dfi)

# --- Symbolic Prover Function (Refined) ---
# ... (prove_or_find_counterexample_smt, initialize_smt_omega_results - same as previous correct version) ...
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

# --- SMT Test Function Implementations (Expanding Coverage) ---

def smt_test_totality_all_ops(omega_val_py: int): # This omega_val_py is the one to use
    global Omega_py # Necessary if you assign to Omega_py INSIDE this function
                    # AND want to affect the global one for helper calls.

    property_name_base = "SMT Operation Totality"
    omega_smt_node = Int(omega_val_py)
    
    # Ensure the global Omega_py is set correctly for calls to get_base_avc_constraints
    # made by THIS function, before calling the prover which might also set it.
    original_omega_py_for_this_func_scope = Omega_py
    Omega_py = omega_val_py

    ops_logic_map = {
        "Add": avc_add_smt_logic, "Sub": avc_sub_smt_logic,
        "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic
    }
    
    all_ops_total_overall = True # Track if all ops pass totality for this Omega

    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a = create_symbolic_avc_val(f"a_tot_{op_name_str}_{omega_val_py}")
        b = create_symbolic_avc_val(f"b_tot_{op_name_str}_{omega_val_py}")
        res = create_symbolic_avc_val(f"res_tot_{op_name_str}_{omega_val_py}")

        # Setup constraints for a, b, and the operation
        setup = get_base_avc_constraints(a, omega_smt_node) + \
                get_base_avc_constraints(b, omega_smt_node)
        setup.append(op_logic_func(a, b, res, omega_smt_node))
        
        # Property: The result 'res' must ALSO satisfy base AVC constraints
        res_constraints = get_base_avc_constraints(res, omega_smt_node) # Omega_py is now omega_val_py
        property_res_is_valid = And(res_constraints)

        # --- Localized Proving Logic for this specific property ---
        holds_observed_for_op = False
        ce_op_str = None
        with Solver(name="z3") as s_tot:
            for f_s in setup: s_tot.add_assertion(f_s)
            # Assert that res is NOT valid
            s_tot.add_assertion(Not(property_res_is_valid))
            if not s_tot.solve(): # If Not(valid) is UNSAT, then valid is TRUE
                holds_observed_for_op = True
            else: # Not(valid) is SAT, so res can be invalid
                model = s_tot.get_model()
                ce_parts_tot = []
                for avc_repr_ce_tot in [a,b,res]:
                    name = avc_repr_ce_tot['name']
                    try:
                        is_z = model.get_value(avc_repr_ce_tot['is_zero'])
                        is_a = model.get_value(avc_repr_ce_tot['is_areo'])
                        is_f = model.get_value(avc_repr_ce_tot['is_finite'])
                        val_smt_ce = model.get_value(avc_repr_ce_tot['val']) # Renamed to avoid conflict
                        state_str = "ZS" if is_z.is_true() else \
                                    ("AS" if is_a.is_true() else \
                                    (f"Fp({val_smt_ce})" if is_f.is_true() else "UnknownState"))
                        ce_parts_tot.append(f"{name}={state_str}")
                    except Exception:
                        ce_parts_tot.append(f"{name}=?")
                ce_op_str = "; ".join(ce_parts_tot)
        
        success_for_op = holds_observed_for_op # Expect totality to hold
        
        # Record using the main recording function if desired, or print directly
        initialize_smt_omega_results(omega_val_py) # Ensure dict entry exists
        status_emoji_op = "✅" if success_for_op else "❌"
        final_message_op = "Operation is total as expected." if success_for_op else f"Operation '{op_name_str}' is NOT total (produced invalid state)."

        print(f"{status_emoji_op} Omega={omega_val_py}: Property '{current_property_name}' - {final_message_op}")
        if ce_op_str and not success_for_op:
            print(f"    Counterexample for {op_name_str}: {ce_op_str}")

        if success_for_op:
            smt_test_results_summary[omega_val_py]["passed"] += 1
        else:
            smt_test_results_summary[omega_val_py]["failed"] += 1
            all_ops_total_overall = False # If one op fails, overall totality for this Omega fails
            smt_test_failures_details.append({
                "property": current_property_name, "omega": omega_val_py,
                "expectation_met": success_for_op,
                "property_held_observed": holds_observed_for_op,
                "expected_to_hold": True,
                "message": final_message_op,
                "counterexample": ce_op_str
            })
    
    Omega_py = original_omega_py_for_this_func_scope # Restore global Omega_py


def smt_test_commutativity(op_logic_func: Callable, op_name_str: str, omega_val_py: int):
    property_name = f"SMT Commutativity of {op_name_str}"
    # ... (definition as in previous correct version)
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
    # ... (definition as in previous correct version) ...
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
    # ... (definition as in previous correct version) ...
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

    setup.append(avc_add_smt_logic(b,c,b_plus_c,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,b_plus_c,lhs,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,b,a_mul_b,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,c,a_mul_c,omega_smt_node))
    setup.append(avc_add_smt_logic(a_mul_b,a_mul_c,rhs,omega_smt_node))

    distributivity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        distributivity_formula, [a,b,c], expect_property_to_hold=expected_to_hold)

def smt_test_subtraction_asymmetry(omega_val_py: int):
    property_name = "SMT Subtraction Asymmetry"
    # ... (definition as in previous script, ensure zu_const and au_const are properly defined and used) ...
    omega_smt_node = Int(omega_val_py)
    x = create_symbolic_avc_val("x_sub_asym")
    zu_const_repr = create_symbolic_avc_val("ZU_sub_asym") 
    au_const_repr = create_symbolic_avc_val("AU_sub_asym")
    
    res_x_m_zu = create_symbolic_avc_val("res_xmzu")
    res_x_m_au = create_symbolic_avc_val("res_xmau")
    res_zu_m_x = create_symbolic_avc_val("res_zumx")
    res_au_m_x = create_symbolic_avc_val("res_aumx")

    setup = get_base_avc_constraints(x, omega_smt_node) + \
            get_base_avc_constraints(zu_const_repr, omega_smt_node) + \
            get_base_avc_constraints(au_const_repr, omega_smt_node) + \
            get_base_avc_constraints(res_x_m_zu, omega_smt_node) + \
            get_base_avc_constraints(res_x_m_au, omega_smt_node) + \
            get_base_avc_constraints(res_zu_m_x, omega_smt_node) + \
            get_base_avc_constraints(res_au_m_x, omega_smt_node)
    
    setup.append(And(zu_const_repr["is_zero"], Not(zu_const_repr["is_areo"]), Not(zu_const_repr["is_finite"]))) # Define ZU
    setup.append(And(Not(au_const_repr["is_zero"]), au_const_repr["is_areo"], Not(au_const_repr["is_finite"]))) # Define AU

    # x - Unio == x
    setup.append(avc_sub_smt_logic(x, zu_const_repr, res_x_m_zu, omega_smt_node))
    setup.append(avc_sub_smt_logic(x, au_const_repr, res_x_m_au, omega_smt_node))
    prop_x_minus_unio_is_x = And(avc_equiv_smt(res_x_m_zu, x), 
                                 avc_equiv_smt(res_x_m_au, x))

    # Unio - x
    setup.append(avc_sub_smt_logic(zu_const_repr, x, res_zu_m_x, omega_smt_node))
    setup.append(avc_sub_smt_logic(au_const_repr, x, res_au_m_x, omega_smt_node))
    
    # Expected: ZU - DFI -> AU; AU - DFI -> AU
    # Expected: ZU - ZU -> ZU; ZU - AU -> ZU
    # Expected: AU - ZU -> AU; AU - AU -> AU (as per python avc_sub: if b is Unio, return a)
    # This needs to be precise according to Revised Core AVCA: `if isinstance(a, Unio): return AREO_UNIO` (when b is DFI)
    # and `if isinstance(b, Unio): return a`
    prop_unio_minus_x_behavior = And(
        Implies(x["is_finite"], And(avc_equiv_smt(res_zu_m_x, au_const_repr), 
                                    avc_equiv_smt(res_au_m_x, au_const_repr))),
        Implies(Or(x["is_zero"], x["is_areo"]), # x is Unio
                And(avc_equiv_smt(res_zu_m_x, zu_const_repr), # ZU - Unio -> ZU
                    avc_equiv_smt(res_au_m_x, au_const_repr)))  # AU - Unio -> AU
    )
    
    full_asymmetry_property = And(prop_x_minus_unio_is_x, prop_unio_minus_x_behavior)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        full_asymmetry_property, [x, zu_const_repr, au_const_repr], expect_property_to_hold=True
    )

def smt_test_dfi_haven(omega_val_py: int):
    property_name_base = "SMT DFI-Haven"
    if omega_val_py <= 1:
        prove_or_find_counterexample_smt(property_name_base, omega_val_py, [], TRUE(), [], True) 
        print(f"    (Vacuously true for Omega={omega_val_py} as DFI is empty or non-existent)")
        return

    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val("a_dfih")
    b = create_symbolic_avc_val("b_dfih")

    dfi_constraints = [ a["is_finite"], b["is_finite"] ] # Base constraints already ensure val bounds

    # --- Addition DFI Haven ---
    res_add = create_symbolic_avc_val("res_add_dfih")
    setup_add = get_base_avc_constraints(a, omega_smt_node) + \
                get_base_avc_constraints(b, omega_smt_node) + \
                get_base_avc_constraints(res_add, omega_smt_node) + \
                dfi_constraints
    setup_add.append(avc_add_smt_logic(a,b,res_add,omega_smt_node))
    sum_val = a["val"] + b["val"]
    expected_add_fp = And(Not(res_add["is_zero"]), Not(res_add["is_areo"]), res_add["is_finite"], Equals(res_add["val"], sum_val))
    expected_add_zu = And(res_add["is_zero"], Not(res_add["is_areo"]), Not(res_add["is_finite"]))
    prop_add_dfi = Ite(sum_val < omega_smt_node, expected_add_fp, expected_add_zu)
    prove_or_find_counterexample_smt(f"{property_name_base} (Addition)", omega_val_py, setup_add, prop_add_dfi, [a,b], True)

    # --- Multiplication DFI Haven ---
    res_mul = create_symbolic_avc_val("res_mul_dfih")
    setup_mul = get_base_avc_constraints(a, omega_smt_node) + \
                get_base_avc_constraints(b, omega_smt_node) + \
                get_base_avc_constraints(res_mul, omega_smt_node) + \
                dfi_constraints
    setup_mul.append(avc_mul_smt_logic(a,b,res_mul,omega_smt_node))
    prod_val = a["val"] * b["val"]
    expected_mul_fp = And(Not(res_mul["is_zero"]), Not(res_mul["is_areo"]), res_mul["is_finite"], Equals(res_mul["val"], prod_val))
    expected_mul_au = And(Not(res_mul["is_zero"]), res_mul["is_areo"], Not(res_mul["is_finite"]))
    prop_mul_dfi = Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), expected_mul_fp, expected_mul_au)
    prove_or_find_counterexample_smt(f"{property_name_base} (Multiplication)", omega_val_py, setup_mul, prop_mul_dfi, [a,b], True)

    # --- Subtraction DFI Haven ---
    res_sub = create_symbolic_avc_val("res_sub_dfih")
    setup_sub = get_base_avc_constraints(a, omega_smt_node) + \
                get_base_avc_constraints(b, omega_smt_node) + \
                get_base_avc_constraints(res_sub, omega_smt_node) + \
                dfi_constraints
    setup_sub.append(avc_sub_smt_logic(a,b,res_sub,omega_smt_node))
    diff_val = a["val"] - b["val"]
    expected_sub_fp = And(Not(res_sub["is_zero"]), Not(res_sub["is_areo"]), res_sub["is_finite"], Equals(res_sub["val"], diff_val))
    expected_sub_au = And(Not(res_sub["is_zero"]), res_sub["is_areo"], Not(res_sub["is_finite"]))
    prop_sub_dfi = Ite(a["val"] > b["val"], expected_sub_fp, expected_sub_au)
    prove_or_find_counterexample_smt(f"{property_name_base} (Subtraction)", omega_val_py, setup_sub, prop_sub_dfi, [a,b], True)

    # --- Division DFI Haven ---
    res_div = create_symbolic_avc_val("res_div_dfih")
    q_div_haven = Symbol(f"q_dfih_div", SMT_INT_TYPE) 
    r_div_haven = Symbol(f"r_dfih_div", SMT_INT_TYPE)
    setup_div = get_base_avc_constraints(a, omega_smt_node) + \
                get_base_avc_constraints(b, omega_smt_node) + \
                get_base_avc_constraints(res_div, omega_smt_node) + \
                dfi_constraints
    setup_div.append(avc_div_smt_logic(a,b,res_div,omega_smt_node)) # This implicitly defines q_sym, r_sym via res_div's name

    # Need to access the q_sym, r_sym defined *inside* avc_div_smt_logic for res_div
    # This requires avc_div_smt_logic to perhaps return them or we re-define them here scoped.
    # For simplicity, we re-state the conditions for the property.
    div_constraints_prop = Implies(b["is_finite"],
                                   And(Equals(a["val"], q_div_haven * b["val"] + r_div_haven),
                                       r_div_haven >= Int(0), r_div_haven < b["val"]))
    valid_dfi_quot_cond_prop = Implies(b["is_finite"],
                                   And(Equals(r_div_haven, Int(0)), q_div_haven >= Int(1), q_div_haven < omega_smt_node))
    
    expected_div_fp = And(Not(res_div["is_zero"]), Not(res_div["is_areo"]), res_div["is_finite"], Equals(res_div["val"], q_div_haven))
    expected_div_au = And(Not(res_div["is_zero"]), res_div["is_areo"], Not(res_div["is_finite"]))
    
    prop_div_dfi = Implies(div_constraints_prop, Ite(valid_dfi_quot_cond_prop, expected_div_fp, expected_div_au))
    prove_or_find_counterexample_smt(f"{property_name_base} (Division)", omega_val_py, setup_div, prop_div_dfi, [a,b], True)


def smt_test_stuck_at_areo(omega_val_py: int):
    property_name = "SMT Stuck-at-Areo (Unio - DFI_k ~ AREO_UNIO)"
    if omega_val_py <= 1: # No DFI
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True)
        print(f"    (Vacuously true for Omega={omega_val_py} as DFI is empty)")
        return

    omega_smt_node = Int(omega_val_py)
    k_dfi = create_symbolic_avc_val("k_dfi_saa")
    zu_const = create_symbolic_avc_val("ZU_saa")
    au_const = create_symbolic_avc_val("AU_saa")
    res_zu_m_k = create_symbolic_avc_val("res_zumk_saa")
    res_au_m_k = create_symbolic_avc_val("res_aumk_saa")

    setup = get_base_avc_constraints(k_dfi, omega_smt_node) + \
            get_base_avc_constraints(zu_const, omega_smt_node) + \
            get_base_avc_constraints(au_const, omega_smt_node) + \
            get_base_avc_constraints(res_zu_m_k, omega_smt_node) + \
            get_base_avc_constraints(res_au_m_k, omega_smt_node)

    setup.append(k_dfi["is_finite"]) # k is DFI
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"])))
    setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))

    setup.append(avc_sub_smt_logic(zu_const, k_dfi, res_zu_m_k, omega_smt_node))
    setup.append(avc_sub_smt_logic(au_const, k_dfi, res_au_m_k, omega_smt_node))

    property_formula = And(avc_equiv_smt(res_zu_m_k, au_const), # ZU - DFI_k -> AU
                             avc_equiv_smt(res_au_m_k, au_const))  # AU - DFI_k -> AU
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_formula, [k_dfi, zu_const, au_const], expect_property_to_hold=True
    )

def smt_test_full_circle_addition(omega_val_py: int):
    property_name = "SMT Full-Circle Addition (a + Unio ~ a, Unio + a ~ a)"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val("a_fca")
    zu_const = create_symbolic_avc_val("ZU_fca")
    au_const = create_symbolic_avc_val("AU_fca")

    res_a_p_zu = create_symbolic_avc_val("res_apzu_fca")
    res_a_p_au = create_symbolic_avc_val("res_apau_fca")
    res_zu_p_a = create_symbolic_avc_val("res_zupa_fca")
    res_au_p_a = create_symbolic_avc_val("res_aupa_fca")
    
    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(zu_const, omega_smt_node) + \
            get_base_avc_constraints(au_const, omega_smt_node) + \
            get_base_avc_constraints(res_a_p_zu, omega_smt_node) + \
            get_base_avc_constraints(res_a_p_au, omega_smt_node) + \
            get_base_avc_constraints(res_zu_p_a, omega_smt_node) + \
            get_base_avc_constraints(res_au_p_a, omega_smt_node)

    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"])))
    setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))

    setup.append(avc_add_smt_logic(a, zu_const, res_a_p_zu, omega_smt_node))
    setup.append(avc_add_smt_logic(a, au_const, res_a_p_au, omega_smt_node))
    setup.append(avc_add_smt_logic(zu_const, a, res_zu_p_a, omega_smt_node))
    setup.append(avc_add_smt_logic(au_const, a, res_au_p_a, omega_smt_node))

    property_formula = And(avc_equiv_smt(res_a_p_zu, a),
                             avc_equiv_smt(res_a_p_au, a),
                             avc_equiv_smt(res_zu_p_a, a),
                             avc_equiv_smt(res_au_p_a, a))
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_formula, [a, zu_const, au_const], expect_property_to_hold=True
    )

def smt_test_omega_1_specifics(omega_val_py: int):
    property_name = "SMT Omega=1 Specifics (All ops Unio op Unio -> Unio)"
    if omega_val_py != 1:
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True) # Vacuously true
        print(f"    (N/A for Omega={omega_val_py})")
        return

    omega_smt_node = Int(1)
    # For Omega=1, all valid inputs are Unio (ZS or AS aspect)
    a_unio = create_symbolic_avc_val("a_o1")
    b_unio = create_symbolic_avc_val("b_o1")
    
    res_add = create_symbolic_avc_val("res_add_o1")
    res_sub = create_symbolic_avc_val("res_sub_o1")
    res_mul = create_symbolic_avc_val("res_mul_o1")
    res_div = create_symbolic_avc_val("res_div_o1")

    setup = get_base_avc_constraints(a_unio, omega_smt_node) + \
            get_base_avc_constraints(b_unio, omega_smt_node) + \
            get_base_avc_constraints(res_add, omega_smt_node) + \
            get_base_avc_constraints(res_sub, omega_smt_node) + \
            get_base_avc_constraints(res_mul, omega_smt_node) + \
            get_base_avc_constraints(res_div, omega_smt_node)
    
    # Constrain a_unio and b_unio to be Unio (since DFI is empty for Omega=1)
    setup.append(Or(a_unio["is_zero"], a_unio["is_areo"]))
    setup.append(Or(b_unio["is_zero"], b_unio["is_areo"]))

    setup.append(avc_add_smt_logic(a_unio, b_unio, res_add, omega_smt_node))
    setup.append(avc_sub_smt_logic(a_unio, b_unio, res_sub, omega_smt_node))
    setup.append(avc_mul_smt_logic(a_unio, b_unio, res_mul, omega_smt_node))
    setup.append(avc_div_smt_logic(a_unio, b_unio, res_div, omega_smt_node))

    # Property: All results must be Unio
    prop_add_res_is_unio = Or(res_add["is_zero"], res_add["is_areo"])
    prop_sub_res_is_unio = Or(res_sub["is_zero"], res_sub["is_areo"])
    prop_mul_res_is_unio = Or(res_mul["is_zero"], res_mul["is_areo"]) # Aspect checked by mul_logic
    prop_div_res_is_unio = Or(res_div["is_zero"], res_div["is_areo"]) # Aspect checked by div_logic

    full_omega1_property = And(prop_add_res_is_unio, prop_sub_res_is_unio, 
                               prop_mul_res_is_unio, prop_div_res_is_unio)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        full_omega1_property, [a_unio, b_unio], expect_property_to_hold=True
    )

def smt_test_omega_2_algebra(omega_val_py: int):
    property_name = "SMT Omega=2 Algebra (1+1~ZU, 1*1~Fp(1), Add Assoc, Mul Distrib)"
    if omega_val_py != 2:
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True)
        print(f"    (N/A for Omega={omega_val_py})")
        return

    omega_smt_node = Int(2)
    # Define constants for ZS_C, AS_C, Fp_C(1) for Omega=2
    fp1_const = create_symbolic_avc_val("Fp1_o2")
    zu_const = create_symbolic_avc_val("ZU_o2")
    
    setup_const = get_base_avc_constraints(fp1_const, omega_smt_node) + \
                  get_base_avc_constraints(zu_const, omega_smt_node)
    setup_const.append(And(fp1_const["is_finite"], Equals(fp1_const["val"], Int(1))))
    setup_const.append(zu_const["is_zero"])

    # Test 1+1 ~ ZU
    res_1p1 = create_symbolic_avc_val("res1p1_o2")
    setup_1p1 = setup_const + get_base_avc_constraints(res_1p1, omega_smt_node)
    setup_1p1.append(avc_add_smt_logic(fp1_const, fp1_const, res_1p1, omega_smt_node))
    prop_1p1 = avc_equiv_smt(res_1p1, zu_const)
    prove_or_find_counterexample_smt(f"{property_name} - 1+1~ZU", omega_val_py, setup_1p1, prop_1p1, [fp1_const, zu_const, res_1p1], True)

    # Test 1*1 ~ Fp(1)
    res_1x1 = create_symbolic_avc_val("res1x1_o2")
    setup_1x1 = setup_const + get_base_avc_constraints(res_1x1, omega_smt_node)
    setup_1x1.append(avc_mul_smt_logic(fp1_const, fp1_const, res_1x1, omega_smt_node))
    prop_1x1 = avc_equiv_smt(res_1x1, fp1_const)
    prove_or_find_counterexample_smt(f"{property_name} - 1*1~Fp(1)", omega_val_py, setup_1x1, prop_1x1, [fp1_const, res_1x1], True)
    
    # Additive Associativity for Omega=2 is expected to HOLD (covered by general test)
    # Distributivity for Omega=2 is expected to HOLD (covered by general test)
    # The general tests smt_test_associativity(avc_add_smt_logic,...) and smt_test_distributivity_mul_over_add
    # already verify these for Omega=2 with expect_property_to_hold=True.

# --- Main SMT Test Execution ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] 
    print(f"\n\n{'='*30} STARTING PySMT TESTS FOR REVISED CORE AVCA {'='*30}")

    for current_omega_py_val in omegas_to_test_smt:
        Omega_py = current_omega_py_val 
        print(f"\n\n{'='*25} SMT TESTING FOR OMEGA = {current_omega_py_val} {'='*25}")
        initialize_smt_omega_results(current_omega_py_val)

        smt_test_totality_all_ops(current_omega_py_val)
        smt_test_commutativity(avc_add_smt_logic, "Addition", current_omega_py_val)
        smt_test_commutativity(avc_mul_smt_logic, "Multiplication", current_omega_py_val)
        
        add_assoc_expected = (current_omega_py_val <= 2)
        smt_test_associativity(avc_add_smt_logic, "Addition", current_omega_py_val, add_assoc_expected)
        smt_test_associativity(avc_mul_smt_logic, "Multiplication", current_omega_py_val, True)
        
        distrib_mul_over_add_expected = (current_omega_py_val <= 2)
        smt_test_distributivity_mul_over_add(current_omega_py_val) # Pass omega_val_py for exp_to_hold logic
        
        smt_test_subtraction_asymmetry(current_omega_py_val)
        smt_test_dfi_haven(current_omega_py_val)
        smt_test_stuck_at_areo(current_omega_py_val)
        smt_test_full_circle_addition(current_omega_py_val)
        
        if current_omega_py_val == 1:
            smt_test_omega_1_specifics(current_omega_py_val)
        if current_omega_py_val == 2:
            smt_test_omega_2_algebra(current_omega_py_val)
        
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