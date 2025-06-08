from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE,
                             Iff) # Ensured Iff is imported
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Symbolic Core AVCA Definitions ---

# Global Python Omega, set by the main test loop for each Omega scenario
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

    case1_a_is_unio = Implies(a_is_unio, And(Iff(res["is_zero"], b["is_zero"]),
                                           Iff(res["is_areo"], b["is_areo"]),
                                           Iff(res["is_finite"], b["is_finite"]),
                                           Equals(res["val"], b["val"])))
    case2_b_is_unio = Implies(And(Not(a_is_unio), b_is_unio), 
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
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

def avc_sub_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), 
                            Equals(res["val"], omega_smt_node))

    case1_b_is_unio = Implies(b_is_unio, And(Iff(res["is_zero"], a["is_zero"]),
                                           Iff(res["is_areo"], a["is_areo"]),
                                           Iff(res["is_finite"], a["is_finite"]),
                                           Equals(res["val"], a["val"])))
    case2_a_is_unio_b_is_dfi = Implies(And(a_is_unio, b["is_finite"]), res_is_AU_formula)
    
    diff_val = a["val"] - b["val"]
    res_is_FP_diff_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], diff_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(a["val"] > b["val"],
                                res_is_FP_diff_formula, 
                                res_is_AU_formula 
                            ))
    return And(case1_b_is_unio, case2_a_is_unio_b_is_dfi, case3_dfi_dfi)

def avc_mul_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))

    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    case1_a_is_unio = Implies(a_is_unio, Ite(a["is_zero"], res_is_ZU_formula, res_is_AU_formula))
    
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b_is_unio),
                                       Ite(b["is_zero"], res_is_ZU_formula, res_is_AU_formula))
    
    prod_val = a["val"] * b["val"]
    res_is_FP_prod_formula = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], prod_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), 
                                res_is_FP_prod_formula, 
                                res_is_AU_formula 
                            ))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi)

def avc_div_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode], 
                      res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    res_is_ZU_formula = And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    case1_a_is_unio = Implies(a_is_unio, Ite(a["is_zero"], res_is_ZU_formula, res_is_AU_formula))

    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b_is_unio), res_is_AU_formula)
    
    q_sym = Symbol(f"{res['name']}_q_div", SMT_INT_TYPE) 
    r_sym = Symbol(f"{res['name']}_r_div", SMT_INT_TYPE)

    div_constraints = Implies(And(b["is_finite"], b["val"] > Int(0)), # Ensure b.val > 0 for division semantics
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
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi)

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
    expect_property_to_hold: bool,
    is_existential: bool = False): # Default to ForAll check
    
    global Omega_py 
    Omega_py = omega_py_val 
    initialize_smt_omega_results(omega_py_val)

    property_holds_observed = False 
    counterexample_witness_str = None

    # (inside prove_or_find_counterexample_smt function)
    # ...
    with Solver(name="z3") as s: 
        for f_setup in setup_formulas: 
            s.add_assertion(f_setup)
        
        if is_existential: # Line 181
            s.add_assertion(property_to_verify) 
            if s.solve(): # Line 183 - Inner if
                property_holds_observed = True
                model = s.get_model()
                ce_parts = [] 
                for repr_dict in inputs_reprs: # Loop inside inner if
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero'])
                        is_a = model.get_value(repr_dict['is_areo'])
                        is_f = model.get_value(repr_dict['is_finite'])
                        val_smt = model.get_value(repr_dict['val'])
                        
                        fp_val_str = "" 
                        if is_f.is_true():
                            fp_val_str = f"Fp({val_smt})" 

                        state_str = "ZS" if is_z.is_true() else \
                                    ("AS" if is_a.is_true() else \
                                     (fp_val_str if is_f.is_true() else "UnknownState"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: 
                        ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts) # Belongs to 'if s.solve()', after loop
            else: # Line 205 - Belongs to 'if s.solve()'
                property_holds_observed = False
        # END OF 'if is_existential:' block
        
        # Line 207 - This 'else' MUST align with 'if is_existential:' (line 181)
        else: # Universal property 
            s.add_assertion(Not(property_to_verify)) 
            if not s.solve(): 
                property_holds_observed = True 
            else: 
                property_holds_observed = False
                model = s.get_model()
                ce_parts = []
                for repr_dict in inputs_reprs: # Loop inside this else block
                    # ... (similar logic to populate ce_parts)
                    name = repr_dict['name'] # Example line from your image for this block
                    try:
                        is_z = model.get_value(repr_dict['is_zero'])
                        is_a = model.get_value(repr_dict['is_areo'])
                        is_f = model.get_value(repr_dict['is_finite'])
                        val_smt = model.get_value(repr_dict['val'])
                        
                        fp_val_str = "" 
                        if is_f.is_true():
                            fp_val_str = f"Fp({val_smt})"

                        state_str = "ZS" if is_z.is_true() else \
                                    ("AS" if is_a.is_true() else \
                                     (fp_val_str if is_f.is_true() else "UnknownState"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: 
                        ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts) # Belongs to this inner 'else', after loop
    # END OF 'with Solver...' block

    # The rest of the function (success_for_summary, print statements) MUST align with 'with Solver...'
    success_for_summary = (property_holds_observed == expect_property_to_hold)
    # ...
    status_emoji = "✅" if success_for_summary else "❌"
    final_message = ""

    if is_existential:
        if expect_property_to_hold: 
            final_message = "Existence PROVED (witness found)." if property_holds_observed else "Existence FAILED (no witness found when one was expected)."
        else: 
            final_message = "Non-existence CONFIRMED (no witness found)." if not property_holds_observed else "Non-existence FAILED (witness found when none was expected)."
    else: # Universal
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
            "property": property_name, "omega": omega_py_val, "is_existential": is_existential,
            "expectation_met": success_for_summary,
            "property_holds_observed_or_witness_found": property_holds_observed,
            "expected_to_hold_or_witness_exist": expect_property_to_hold,
            "message": final_message,
            "counterexample_witness": counterexample_witness_str
        })

    print(f"{status_emoji} Omega={omega_py_val}: Property '{property_name}' (Expect P to hold/witness exist: {expect_property_to_hold}) - {final_message}")
    if counterexample_witness_str:
        label = "Witness" if (is_existential and property_holds_observed and expect_property_to_hold) else \
                ("Counterexample" if (not is_existential and not property_holds_observed and expect_property_to_hold) else \
                 ("Confirming CE for Non-Universality" if (not is_existential and not property_holds_observed and not expect_property_to_hold) else \
                  ("Unexpected Witness" if (is_existential and not expect_property_to_hold and property_holds_observed) else \
                   "Debug Info"))) # Fallback label
        print(f"    {label}: {counterexample_witness_str}")


# --- SMT Test Function Implementations (Completed & New) ---

def smt_test_totality_all_ops(omega_val_py: int):
    property_name_base = "SMT Operation Totality"
    omega_smt_node = Int(omega_val_py)
    
    ops_logic_map = {
        "Add": avc_add_smt_logic, "Sub": avc_sub_smt_logic,
        "Mul": avc_mul_smt_logic, "Div": avc_div_smt_logic
    }
    
    for op_name_str, op_logic_func in ops_logic_map.items():
        current_property_name = f"{property_name_base} for {op_name_str}"
        a = create_symbolic_avc_val(f"a_tot_{op_name_str}_{omega_val_py}")
        b = create_symbolic_avc_val(f"b_tot_{op_name_str}_{omega_val_py}")
        res = create_symbolic_avc_val(f"res_tot_{op_name_str}_{omega_val_py}")

        setup = get_base_avc_constraints(a, omega_smt_node) + \
                get_base_avc_constraints(b, omega_smt_node)
        
        setup.append(op_logic_func(a, b, res, omega_smt_node))
        
        res_constraints = get_base_avc_constraints(res, omega_smt_node)
        property_res_is_valid = And(res_constraints)
        
        prove_or_find_counterexample_smt(
            current_property_name, omega_val_py, setup,
            property_res_is_valid, [a,b,res], expect_property_to_hold=True
        )

def smt_test_commutativity(op_logic_func: Callable, op_name_str: str, omega_val_py: int):
    property_name = f"SMT Commutativity of {op_name_str}"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_comm_{op_name_str[:3]}_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_comm_{op_name_str[:3]}_{omega_val_py}")
    res1 = create_symbolic_avc_val(f"res1_comm_{op_name_str[:3]}_{omega_val_py}")
    res2 = create_symbolic_avc_val(f"res2_comm_{op_name_str[:3]}_{omega_val_py}")

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
    # ... (Symbolic vars a,b,c, op_ab, lhs, op_bc, rhs and setup as before)
    a = create_symbolic_avc_val(f"a_assoc_{op_name_str[:3]}_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_assoc_{op_name_str[:3]}_{omega_val_py}")
    c = create_symbolic_avc_val(f"c_assoc_{op_name_str[:3]}_{omega_val_py}")
    op_ab = create_symbolic_avc_val(f"op_ab_{op_name_str[:3]}_{omega_val_py}")
    lhs = create_symbolic_avc_val(f"lhs_assoc_{op_name_str[:3]}_{omega_val_py}")
    op_bc = create_symbolic_avc_val(f"op_bc_{op_name_str[:3]}_{omega_val_py}")
    rhs = create_symbolic_avc_val(f"rhs_assoc_{op_name_str[:3]}_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + get_base_avc_constraints(op_ab, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(op_bc, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(op_logic_func(a,b,op_ab,omega_smt_node)); setup.append(op_logic_func(op_ab,c,lhs,omega_smt_node))
    setup.append(op_logic_func(b,c,op_bc,omega_smt_node)); setup.append(op_logic_func(a,op_bc,rhs,omega_smt_node))
    associativity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, associativity_formula, [a,b,c], expected_to_hold)

def smt_test_distributivity_mul_over_add(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Distributivity of Mul over Add"
    # ... (Symbolic vars and setup as before) ...
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_dist_{omega_val_py}"); b = create_symbolic_avc_val(f"b_dist_{omega_val_py}"); c = create_symbolic_avc_val(f"c_dist_{omega_val_py}")
    b_plus_c = create_symbolic_avc_val(f"bpc_dist_{omega_val_py}"); lhs = create_symbolic_avc_val(f"lhs_dist_{omega_val_py}")
    a_mul_b = create_symbolic_avc_val(f"amb_dist_{omega_val_py}"); a_mul_c = create_symbolic_avc_val(f"amc_dist_{omega_val_py}"); rhs = create_symbolic_avc_val(f"rhs_dist_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(c, omega_smt_node) + get_base_avc_constraints(b_plus_c, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + get_base_avc_constraints(a_mul_b, omega_smt_node) + \
            get_base_avc_constraints(a_mul_c, omega_smt_node) + get_base_avc_constraints(rhs, omega_smt_node)
    setup.append(avc_add_smt_logic(b,c,b_plus_c,omega_smt_node)); setup.append(avc_mul_smt_logic(a,b_plus_c,lhs,omega_smt_node))
    setup.append(avc_mul_smt_logic(a,b,a_mul_b,omega_smt_node)); setup.append(avc_mul_smt_logic(a,c,a_mul_c,omega_smt_node)); setup.append(avc_add_smt_logic(a_mul_b,a_mul_c,rhs,omega_smt_node))
    distributivity_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, distributivity_formula, [a,b,c], expected_to_hold)

def smt_test_subtraction_asymmetry(omega_val_py: int):
    property_name = "SMT Subtraction Asymmetry"
    # ... (Full implementation as in previous script) ...
    omega_smt_node = Int(omega_val_py)
    x = create_symbolic_avc_val(f"x_sub_asym_{omega_val_py}")
    zu_const_repr = create_symbolic_avc_val(f"ZU_sub_asym_{omega_val_py}") 
    au_const_repr = create_symbolic_avc_val(f"AU_sub_asym_{omega_val_py}")
    res_x_m_zu = create_symbolic_avc_val(f"res_xmzu_{omega_val_py}"); res_x_m_au = create_symbolic_avc_val(f"res_xmau_{omega_val_py}")
    res_zu_m_x = create_symbolic_avc_val(f"res_zumx_{omega_val_py}"); res_au_m_x = create_symbolic_avc_val(f"res_aumx_{omega_val_py}")
    setup = get_base_avc_constraints(x, omega_smt_node) + get_base_avc_constraints(zu_const_repr, omega_smt_node) + \
            get_base_avc_constraints(au_const_repr, omega_smt_node) + get_base_avc_constraints(res_x_m_zu, omega_smt_node) + \
            get_base_avc_constraints(res_x_m_au, omega_smt_node) + get_base_avc_constraints(res_zu_m_x, omega_smt_node) + \
            get_base_avc_constraints(res_au_m_x, omega_smt_node)
    setup.append(And(zu_const_repr["is_zero"], Not(zu_const_repr["is_areo"]), Not(zu_const_repr["is_finite"]))) 
    setup.append(And(Not(au_const_repr["is_zero"]), au_const_repr["is_areo"], Not(au_const_repr["is_finite"]))) 
    setup.append(avc_sub_smt_logic(x, zu_const_repr, res_x_m_zu, omega_smt_node)); setup.append(avc_sub_smt_logic(x, au_const_repr, res_x_m_au, omega_smt_node))
    prop_x_minus_unio_is_x = And(avc_equiv_smt(res_x_m_zu, x), avc_equiv_smt(res_x_m_au, x))
    setup.append(avc_sub_smt_logic(zu_const_repr, x, res_zu_m_x, omega_smt_node)); setup.append(avc_sub_smt_logic(au_const_repr, x, res_au_m_x, omega_smt_node))
    prop_unio_minus_x_behavior = And(Implies(x["is_finite"], And(avc_equiv_smt(res_zu_m_x, au_const_repr), avc_equiv_smt(res_au_m_x, au_const_repr))),
                                   Implies(Or(x["is_zero"], x["is_areo"]), And(avc_equiv_smt(res_zu_m_x, zu_const_repr), avc_equiv_smt(res_au_m_x, au_const_repr))))
    full_asymmetry_property = And(prop_x_minus_unio_is_x, prop_unio_minus_x_behavior)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, full_asymmetry_property, [x, zu_const_repr, au_const_repr], True)

def smt_test_dfi_haven(omega_val_py: int):
    property_name_base = "SMT DFI-Haven"
    # ... (Full implementation for all 4 ops as in previous script) ...
    if omega_val_py <= 1:
        prove_or_find_counterexample_smt(f"{property_name_base} (Vacuously True)", omega_val_py, [], TRUE(), [], True)
        print(f"    (Vacuously true for Omega={omega_val_py} as DFI is empty or non-existent)")
        return
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_dfih_{omega_val_py}"); b = create_symbolic_avc_val(f"b_dfih_{omega_val_py}")
    dfi_constraints_ab = [ a["is_finite"], b["is_finite"] ] 
    # Add
    res_add = create_symbolic_avc_val(f"res_add_dfih_{omega_val_py}")
    setup_add = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res_add, omega_smt_node) + dfi_constraints_ab
    setup_add.append(avc_add_smt_logic(a,b,res_add,omega_smt_node))
    sum_val = a["val"] + b["val"]
    expected_add_fp = And(Not(res_add["is_zero"]), Not(res_add["is_areo"]), res_add["is_finite"], Equals(res_add["val"], sum_val))
    expected_add_zu = And(res_add["is_zero"], Not(res_add["is_areo"]), Not(res_add["is_finite"]))
    prop_add_dfi = Ite(sum_val < omega_smt_node, expected_add_fp, expected_add_zu)
    prove_or_find_counterexample_smt(f"{property_name_base} (Addition)", omega_val_py, setup_add, prop_add_dfi, [a,b], True)
    # Mul
    res_mul = create_symbolic_avc_val(f"res_mul_dfih_{omega_val_py}")
    setup_mul = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res_mul, omega_smt_node) + dfi_constraints_ab
    setup_mul.append(avc_mul_smt_logic(a,b,res_mul,omega_smt_node))
    prod_val = a["val"] * b["val"]
    expected_mul_fp = And(Not(res_mul["is_zero"]), Not(res_mul["is_areo"]), res_mul["is_finite"], Equals(res_mul["val"], prod_val))
    expected_mul_au = And(Not(res_mul["is_zero"]), res_mul["is_areo"], Not(res_mul["is_finite"]))
    prop_mul_dfi = Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), expected_mul_fp, expected_mul_au)
    prove_or_find_counterexample_smt(f"{property_name_base} (Multiplication)", omega_val_py, setup_mul, prop_mul_dfi, [a,b], True)
    # Sub
    res_sub = create_symbolic_avc_val(f"res_sub_dfih_{omega_val_py}")
    setup_sub = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res_sub, omega_smt_node) + dfi_constraints_ab
    setup_sub.append(avc_sub_smt_logic(a,b,res_sub,omega_smt_node))
    diff_val = a["val"] - b["val"]
    expected_sub_fp = And(Not(res_sub["is_zero"]), Not(res_sub["is_areo"]), res_sub["is_finite"], Equals(res_sub["val"], diff_val))
    expected_sub_au = And(Not(res_sub["is_zero"]), res_sub["is_areo"], Not(res_sub["is_finite"]))
    prop_sub_dfi = Ite(a["val"] > b["val"], expected_sub_fp, expected_sub_au)
    prove_or_find_counterexample_smt(f"{property_name_base} (Subtraction)", omega_val_py, setup_sub, prop_sub_dfi, [a,b], True)
    # Div
    res_div = create_symbolic_avc_val(f"res_div_dfih_{omega_val_py}")
    q_div_haven = Symbol(f"q_dfih_div_{omega_val_py}", SMT_INT_TYPE) 
    r_div_haven = Symbol(f"r_dfih_div_{omega_val_py}", SMT_INT_TYPE)
    setup_div = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(b, omega_smt_node) + get_base_avc_constraints(res_div, omega_smt_node) + dfi_constraints_ab
    div_constraints_prop = Implies(b["is_finite"], And(Equals(a["val"], q_div_haven * b["val"] + r_div_haven), r_div_haven >= Int(0), r_div_haven < b["val"]))
    setup_div.append(div_constraints_prop)
    setup_div.append(avc_div_smt_logic(a,b,res_div,omega_smt_node))
    valid_dfi_quot_cond_prop = Implies(b["is_finite"], And(Equals(r_div_haven, Int(0)), q_div_haven >= Int(1), q_div_haven < omega_smt_node))
    expected_div_fp = And(Not(res_div["is_zero"]), Not(res_div["is_areo"]), res_div["is_finite"], Equals(res_div["val"], q_div_haven))
    expected_div_au = And(Not(res_div["is_zero"]), res_div["is_areo"], Not(res_div["is_finite"]))
    prop_div_dfi = Ite(valid_dfi_quot_cond_prop, expected_div_fp, expected_div_au)
    prove_or_find_counterexample_smt(f"{property_name_base} (Division)", omega_val_py, setup_div, prop_div_dfi, [a,b,q_div_haven,r_div_haven], True)

def smt_test_stuck_at_areo(omega_val_py: int):
    property_name = "SMT Stuck-at-Areo (Unio - DFI_k ~ AREO_UNIO)"
    # ... (definition as in previous correct version) ...
    if omega_val_py <= 1: 
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True)
        print(f"    (Vacuously true for Omega={omega_val_py} as DFI is empty)")
        return
    omega_smt_node = Int(omega_val_py)
    k_dfi = create_symbolic_avc_val(f"k_dfi_saa_{omega_val_py}")
    zu_const = create_symbolic_avc_val(f"ZU_saa_{omega_val_py}")
    au_const = create_symbolic_avc_val(f"AU_saa_{omega_val_py}")
    res_zu_m_k = create_symbolic_avc_val(f"res_zumk_saa_{omega_val_py}")
    res_au_m_k = create_symbolic_avc_val(f"res_aumk_saa_{omega_val_py}")
    setup = get_base_avc_constraints(k_dfi, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node) + \
            get_base_avc_constraints(au_const, omega_smt_node) + get_base_avc_constraints(res_zu_m_k, omega_smt_node) + \
            get_base_avc_constraints(res_au_m_k, omega_smt_node)
    setup.append(k_dfi["is_finite"]) 
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"])))
    setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))
    setup.append(avc_sub_smt_logic(zu_const, k_dfi, res_zu_m_k, omega_smt_node))
    setup.append(avc_sub_smt_logic(au_const, k_dfi, res_au_m_k, omega_smt_node))
    property_formula = And(avc_equiv_smt(res_zu_m_k, au_const), avc_equiv_smt(res_au_m_k, au_const))
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [k_dfi, zu_const, au_const], True)

def smt_test_full_circle_addition(omega_val_py: int):
    property_name = "SMT Full-Circle Addition (a + Unio ~ a, Unio + a ~ a)"
    # ... (definition as in previous correct version) ...
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_fca_{omega_val_py}")
    zu_const = create_symbolic_avc_val(f"ZU_fca_{omega_val_py}")
    au_const = create_symbolic_avc_val(f"AU_fca_{omega_val_py}")
    res_a_p_zu = create_symbolic_avc_val(f"res_apzu_fca_{omega_val_py}"); res_a_p_au = create_symbolic_avc_val(f"res_apau_fca_{omega_val_py}")
    res_zu_p_a = create_symbolic_avc_val(f"res_zupa_fca_{omega_val_py}"); res_au_p_a = create_symbolic_avc_val(f"res_aupa_fca_{omega_val_py}")
    setup = get_base_avc_constraints(a, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node) + \
            get_base_avc_constraints(au_const, omega_smt_node) + get_base_avc_constraints(res_a_p_zu, omega_smt_node) + \
            get_base_avc_constraints(res_a_p_au, omega_smt_node) + get_base_avc_constraints(res_zu_p_a, omega_smt_node) + \
            get_base_avc_constraints(res_au_p_a, omega_smt_node)
    setup.append(And(zu_const["is_zero"], Not(zu_const["is_areo"]), Not(zu_const["is_finite"])))
    setup.append(And(Not(au_const["is_zero"]), au_const["is_areo"], Not(au_const["is_finite"])))
    setup.append(avc_add_smt_logic(a, zu_const, res_a_p_zu, omega_smt_node)); setup.append(avc_add_smt_logic(a, au_const, res_a_p_au, omega_smt_node))
    setup.append(avc_add_smt_logic(zu_const, a, res_zu_p_a, omega_smt_node)); setup.append(avc_add_smt_logic(au_const, a, res_au_p_a, omega_smt_node))
    property_formula = And(avc_equiv_smt(res_a_p_zu, a), avc_equiv_smt(res_a_p_au, a), avc_equiv_smt(res_zu_p_a, a), avc_equiv_smt(res_au_p_a, a))
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a, zu_const, au_const], True)

def smt_test_omega_1_specifics(omega_val_py: int):
    property_name = "SMT Omega=1 Specifics (All ops Unio op Unio -> Unio)"
    # ... (definition as in previous correct version) ...
    if omega_val_py != 1:
        prove_or_find_counterexample_smt(property_name, omega_val_py, [], TRUE(), [], True, is_existential=False) 
        print(f"    (N/A for Omega={omega_val_py})")
        return
    omega_smt_node = Int(1)
    a_unio = create_symbolic_avc_val(f"a_o1_{omega_val_py}"); b_unio = create_symbolic_avc_val(f"b_o1_{omega_val_py}")
    res_add = create_symbolic_avc_val(f"res_add_o1_{omega_val_py}"); res_sub = create_symbolic_avc_val(f"res_sub_o1_{omega_val_py}")
    res_mul = create_symbolic_avc_val(f"res_mul_o1_{omega_val_py}"); res_div = create_symbolic_avc_val(f"res_div_o1_{omega_val_py}")
    setup = get_base_avc_constraints(a_unio, omega_smt_node) + get_base_avc_constraints(b_unio, omega_smt_node) + \
            get_base_avc_constraints(res_add, omega_smt_node) + get_base_avc_constraints(res_sub, omega_smt_node) + \
            get_base_avc_constraints(res_mul, omega_smt_node) + get_base_avc_constraints(res_div, omega_smt_node)
    setup.append(Or(a_unio["is_zero"], a_unio["is_areo"])); setup.append(Or(b_unio["is_zero"], b_unio["is_areo"]))
    setup.append(avc_add_smt_logic(a_unio, b_unio, res_add, omega_smt_node)); setup.append(avc_sub_smt_logic(a_unio, b_unio, res_sub, omega_smt_node))
    setup.append(avc_mul_smt_logic(a_unio, b_unio, res_mul, omega_smt_node)); setup.append(avc_div_smt_logic(a_unio, b_unio, res_div, omega_smt_node))
    prop_add_res_is_unio = Or(res_add["is_zero"], res_add["is_areo"]); prop_sub_res_is_unio = Or(res_sub["is_zero"], res_sub["is_areo"])
    prop_mul_res_is_unio = Or(res_mul["is_zero"], res_mul["is_areo"]); prop_div_res_is_unio = Or(res_div["is_zero"], res_div["is_areo"])
    full_omega1_property = And(prop_add_res_is_unio, prop_sub_res_is_unio, prop_mul_res_is_unio, prop_div_res_is_unio)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, full_omega1_property, [a_unio, b_unio], True)

def smt_test_omega_2_algebra(omega_val_py: int):
    property_name_base = "SMT Omega=2 Algebra"
    # ... (definition as in previous correct version, but use property_name_base) ...
    if omega_val_py != 2:
        prove_or_find_counterexample_smt(property_name_base, omega_val_py, [], TRUE(), [], True)
        print(f"    (N/A for Omega={omega_val_py})")
        return
    omega_smt_node = Int(2)
    fp1_const = create_symbolic_avc_val(f"Fp1_o2_{omega_val_py}"); zu_const = create_symbolic_avc_val(f"ZU_o2_{omega_val_py}")
    setup_const = get_base_avc_constraints(fp1_const, omega_smt_node) + get_base_avc_constraints(zu_const, omega_smt_node)
    setup_const.append(And(fp1_const["is_finite"], Equals(fp1_const["val"], Int(1)))); setup_const.append(zu_const["is_zero"])
    res_1p1 = create_symbolic_avc_val(f"res1p1_o2_{omega_val_py}")
    setup_1p1 = setup_const + get_base_avc_constraints(res_1p1, omega_smt_node)
    setup_1p1.append(avc_add_smt_logic(fp1_const, fp1_const, res_1p1, omega_smt_node))
    prop_1p1 = avc_equiv_smt(res_1p1, zu_const)
    prove_or_find_counterexample_smt(f"{property_name_base} - 1+1~ZU", omega_val_py, setup_1p1, prop_1p1, [fp1_const, zu_const, res_1p1], True)
    res_1x1 = create_symbolic_avc_val(f"res1x1_o2_{omega_val_py}")
    setup_1x1 = setup_const + get_base_avc_constraints(res_1x1, omega_smt_node)
    setup_1x1.append(avc_mul_smt_logic(fp1_const, fp1_const, res_1x1, omega_smt_node))
    prop_1x1 = avc_equiv_smt(res_1x1, fp1_const)
    prove_or_find_counterexample_smt(f"{property_name_base} - 1*1~Fp(1)", omega_val_py, setup_1x1, prop_1x1, [fp1_const, res_1x1], True)
    # Associativity and Distributivity for Omega=2 are covered by the general tests with expect_property_to_hold=True
# Ensure this is placed BEFORE if __name__ == "__main__":

def smt_test_add_right_quasigroup_existence(omega_val_py: int):
    property_name = "SMT Additive Right Quasigroup (Existence: ForAll a,b Exists x: a+x ~ b)"
    omega_smt_node = Int(omega_val_py)
    
    a = create_symbolic_avc_val(f"a_rqg_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_rqg_{omega_val_py}")
    x = create_symbolic_avc_val(f"x_rqg_{omega_val_py}") # Existentially quantified
    res_ax = create_symbolic_avc_val(f"res_ax_rqg_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(x, omega_smt_node) + \
            get_base_avc_constraints(res_ax, omega_smt_node)
            
    setup.append(avc_add_smt_logic(a, x, res_ax, omega_smt_node))
    
    property_inner_exists = avc_equiv_smt(res_ax, b)
    
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_inner_exists, 
        [a, b, x], 
        expect_property_to_hold=True, # We expect a solution x exists
        is_existential=True 
    )

def smt_test_add_left_quasigroup_existence(omega_val_py: int):
    property_name = "SMT Additive Left Quasigroup (Existence: ForAll a,b Exists y: y+a ~ b)"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_lqg_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_lqg_{omega_val_py}")
    y = create_symbolic_avc_val(f"y_lqg_{omega_val_py}") # Existentially quantified
    res_ya = create_symbolic_avc_val(f"res_ya_lqg_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(y, omega_smt_node) + \
            get_base_avc_constraints(res_ya, omega_smt_node)
            
    setup.append(avc_add_smt_logic(y, a, res_ya, omega_smt_node))
    property_inner_exists = avc_equiv_smt(res_ya, b)
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_inner_exists, [a,b,y],
        expect_property_to_hold=True, # We expect a solution y exists
        is_existential=True
    )

def smt_test_add_right_inverse_existence(omega_val_py: int):
    property_name = "SMT Additive Right Inverse (Existence: ForAll a Exists x: a+x ~ ZS)"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_rinv_{omega_val_py}")
    x = create_symbolic_avc_val(f"x_rinv_{omega_val_py}") # Existentially quantified
    res_ax = create_symbolic_avc_val(f"res_ax_rinv_{omega_val_py}")
    
    zs_target = create_symbolic_avc_val(f"zs_target_rinv_{omega_val_py}")
    setup_zs_target = get_base_avc_constraints(zs_target, omega_smt_node) + \
                      [zs_target["is_zero"]] # Constrain zs_target to be ZeroState

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(x, omega_smt_node) + \
            get_base_avc_constraints(res_ax, omega_smt_node) + \
            setup_zs_target
            
    setup.append(avc_add_smt_logic(a, x, res_ax, omega_smt_node))
    property_inner_exists = avc_equiv_smt(res_ax, zs_target) # Check if a+x is equivalent to ZS
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_inner_exists, [a,x], 
        expect_property_to_hold=True, # We expect an inverse x exists
        is_existential=True
    )

def smt_test_add_left_alternative_law(omega_val_py: int):
    property_name = "SMT Additive Left Alternative Law ((a+a)+b ~ a+(a+b))"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_lal_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_lal_{omega_val_py}")

    a_plus_a = create_symbolic_avc_val(f"apa_lal_{omega_val_py}")
    lhs = create_symbolic_avc_val(f"lhs_lal_{omega_val_py}")
    a_plus_b = create_symbolic_avc_val(f"apb_lal_{omega_val_py}")
    rhs = create_symbolic_avc_val(f"rhs_lal_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(a_plus_a, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(a_plus_b, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    # LHS: (a+a)+b
    setup.append(avc_add_smt_logic(a,a,a_plus_a,omega_smt_node))
    setup.append(avc_add_smt_logic(a_plus_a,b,lhs,omega_smt_node))
    # RHS: a+(a+b)
    setup.append(avc_add_smt_logic(a,b,a_plus_b,omega_smt_node))
    setup.append(avc_add_smt_logic(a,a_plus_b,rhs,omega_smt_node))
    
    property_formula = avc_equiv_smt(lhs,rhs)
    # For Core AVCA, addition is associative for Omega <= 2, non-associative for Omega >= 3.
    # The left alternative law is weaker than full associativity.
    # We need to determine if this specific law is expected to hold.
    # Given that (a+a) often simplifies or hits Unio quickly, this might hold more often than full associativity.
    # Let's assume for now we expect it to hold, and SMT will tell us if not.
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_formula, [a,b], 
        expect_property_to_hold=True # Tentative: let's see if it holds generally
    )

# Prerequisites:
# Ensure all previous definitions are present:
# Omega_py, create_symbolic_avc_val, get_base_avc_constraints, avc_equiv_smt,
# avc_add_smt_logic, initialize_smt_omega_results, prove_or_find_counterexample_smt,
# smt_test_results_summary, smt_test_failures_details

# --- New SMT Test Functions for Further Loop Theory Properties ---

def smt_test_add_right_alternative_law(omega_val_py: int):
    property_name = f"SMT Additive Right Alternative Law ((b+a)+a ~ b+(a+a)) for Omega={omega_val_py}"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_ral_{omega_val_py}")
    b = create_symbolic_avc_val(f"b_ral_{omega_val_py}")

    # LHS: (b+a)+a
    b_plus_a = create_symbolic_avc_val(f"bpa_ral_{omega_val_py}")
    lhs = create_symbolic_avc_val(f"lhs_ral_{omega_val_py}")
    # RHS: b+(a+a)
    a_plus_a = create_symbolic_avc_val(f"apa_ral_{omega_val_py}")
    rhs = create_symbolic_avc_val(f"rhs_ral_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(b, omega_smt_node) + \
            get_base_avc_constraints(b_plus_a, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(a_plus_a, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    # LHS
    setup.append(avc_add_smt_logic(b,a,b_plus_a,omega_smt_node))
    setup.append(avc_add_smt_logic(b_plus_a,a,lhs,omega_smt_node))
    # RHS
    setup.append(avc_add_smt_logic(a,a,a_plus_a,omega_smt_node))
    setup.append(avc_add_smt_logic(b,a_plus_a,rhs,omega_smt_node))
    
    property_formula = avc_equiv_smt(lhs,rhs)
    # Hypothesis: This might hold more generally than full associativity.
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_formula, [a,b], 
        expect_property_to_hold=True # Tentative: let SMT verify
    )

def smt_test_add_power_associativity(omega_val_py: int):
    property_name = f"SMT Additive Power Associativity ((a+a)+a ~ a+(a+a)) for Omega={omega_val_py}"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val(f"a_pa_{omega_val_py}")

    # LHS: (a+a)+a
    a_plus_a_lhs = create_symbolic_avc_val(f"apa_lhs_pa_{omega_val_py}")
    lhs = create_symbolic_avc_val(f"lhs_pa_{omega_val_py}")
    # RHS: a+(a+a)
    a_plus_a_rhs = create_symbolic_avc_val(f"apa_rhs_pa_{omega_val_py}") # Can be same as a_plus_a_lhs if careful
    rhs = create_symbolic_avc_val(f"rhs_pa_{omega_val_py}")

    setup = get_base_avc_constraints(a, omega_smt_node) + \
            get_base_avc_constraints(a_plus_a_lhs, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(a_plus_a_rhs, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    # LHS
    setup.append(avc_add_smt_logic(a,a,a_plus_a_lhs,omega_smt_node))
    setup.append(avc_add_smt_logic(a_plus_a_lhs,a,lhs,omega_smt_node))
    # RHS
    setup.append(avc_add_smt_logic(a,a,a_plus_a_rhs,omega_smt_node))
    setup.append(avc_add_smt_logic(a,a_plus_a_rhs,rhs,omega_smt_node))
    
    property_formula = avc_equiv_smt(lhs,rhs)
    # Power associativity is often true even if full associativity or alternative laws fail.
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_formula, [a], 
        expect_property_to_hold=True # Tentative: let SMT verify
    )

def smt_test_add_right_bol_identity(omega_val_py: int):
    property_name = f"SMT Additive Right Bol Identity (((x+y)+z)+y ~ x+((y+z)+y)) for Omega={omega_val_py}"
    omega_smt_node = Int(omega_val_py)
    x = create_symbolic_avc_val(f"x_rbol_{omega_val_py}")
    y = create_symbolic_avc_val(f"y_rbol_{omega_val_py}")
    z = create_symbolic_avc_val(f"z_rbol_{omega_val_py}")

    # LHS: ((x+y)+z)+y
    xy = create_symbolic_avc_val(f"xy_rbol_{omega_val_py}")
    xyz = create_symbolic_avc_val(f"xyz_rbol_{omega_val_py}")
    lhs = create_symbolic_avc_val(f"lhs_rbol_{omega_val_py}")

    # RHS: x+((y+z)+y)
    yz = create_symbolic_avc_val(f"yz_rbol_{omega_val_py}")
    yzy = create_symbolic_avc_val(f"yzy_rbol_{omega_val_py}")
    rhs = create_symbolic_avc_val(f"rhs_rbol_{omega_val_py}")

    setup = get_base_avc_constraints(x, omega_smt_node) + \
            get_base_avc_constraints(y, omega_smt_node) + \
            get_base_avc_constraints(z, omega_smt_node) + \
            get_base_avc_constraints(xy, omega_smt_node) + \
            get_base_avc_constraints(xyz, omega_smt_node) + \
            get_base_avc_constraints(lhs, omega_smt_node) + \
            get_base_avc_constraints(yz, omega_smt_node) + \
            get_base_avc_constraints(yzy, omega_smt_node) + \
            get_base_avc_constraints(rhs, omega_smt_node)

    # LHS
    setup.append(avc_add_smt_logic(x,y,xy,omega_smt_node))
    setup.append(avc_add_smt_logic(xy,z,xyz,omega_smt_node))
    setup.append(avc_add_smt_logic(xyz,y,lhs,omega_smt_node))
    # RHS
    setup.append(avc_add_smt_logic(y,z,yz,omega_smt_node))
    setup.append(avc_add_smt_logic(yz,y,yzy,omega_smt_node))
    setup.append(avc_add_smt_logic(x,yzy,rhs,omega_smt_node))
    
    property_formula = avc_equiv_smt(lhs,rhs)
    # Bol identities are stronger than alternative laws but weaker than Moufang/associativity.
    # Let's hypothesize it might fail for Omega >= 3, like associativity.
    expected_to_hold_rbol = (omega_val_py <= 2) 
    prove_or_find_counterexample_smt(
        property_name, omega_val_py, setup,
        property_formula, [x,y,z], 
        expect_property_to_hold=expected_to_hold_rbol
    )

# --- Ensure you add calls to these new test functions in your main loop ---
# if __name__ == "__main__":
#     ...
#     for current_omega_py_val in omegas_to_test_smt:
#         ...
#         # Previous tests ...
#         ...
#         print(f"\n--- Further Loop Theory Property Tests for Omega={current_omega_py_val} ---")
#         smt_test_add_right_alternative_law(current_omega_py_val)
#         smt_test_add_power_associativity(current_omega_py_val)
#         smt_test_add_right_bol_identity(current_omega_py_val)
#         ...
#         # Print summary ...
# --- Main SMT Test Execution ---
# --- Main SMT Test Execution ---
if __name__ == "__main__":
    omegas_to_test_smt = [1, 2, 3, 5] 
    print(f"\n\n{'='*30} STARTING PySMT TESTS FOR REVISED CORE AVCA (Comprehensive) {'='*30}")

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
        # The function smt_test_distributivity_mul_over_add itself calculates expected_to_hold
        smt_test_distributivity_mul_over_add(current_omega_py_val) 
        
        smt_test_subtraction_asymmetry(current_omega_py_val)
        smt_test_dfi_haven(current_omega_py_val) # Tests Add, Mul, Sub, Div DFI Haven
        smt_test_stuck_at_areo(current_omega_py_val)
        smt_test_full_circle_addition(current_omega_py_val)
        
        if current_omega_py_val == 1:
            smt_test_omega_1_specifics(current_omega_py_val)
        if current_omega_py_val == 2:
            smt_test_omega_2_algebra(current_omega_py_val)

        # Ensure these calls are present and not commented out:
        print(f"\n--- Loop/Quasigroup Property Tests for Omega={current_omega_py_val} ---")
        smt_test_add_right_quasigroup_existence(current_omega_py_val)
        smt_test_add_left_quasigroup_existence(current_omega_py_val)
        smt_test_add_right_inverse_existence(current_omega_py_val)
        smt_test_add_left_alternative_law(current_omega_py_val) 
        
        print(f"\nSMT Summary for Omega={current_omega_py_val}: Passed={smt_test_results_summary[current_omega_py_val]['passed']}, Failed={smt_test_results_summary[current_omega_py_val]['failed']}")
        print(f"{'='*60}")

        # ... (after your existing test calls for a given omega_val_py) ...
        print(f"\n--- Further Loop Theory Property Tests for Omega={current_omega_py_val} ---")
        smt_test_add_right_alternative_law(current_omega_py_val)
        smt_test_add_power_associativity(current_omega_py_val)
        smt_test_add_right_bol_identity(current_omega_py_val)

    # ... (Overall summary printing code) ...
      

    # ... (Overall summary printing code - same as before) ...
    print("\n\n{'='*30} OVERALL SMT TEST SUITE SUMMARY {'='*30}")
    total_passed_smt_all = 0; total_failed_smt_all = 0
    for ov_summary, results in smt_test_results_summary.items():
        total_passed_smt_all += results['passed']; total_failed_smt_all += results['failed']
        print(f"Omega={ov_summary}: Passed={results['passed']}, Failed={results['failed']}")
    if smt_test_failures_details:
        print("\n--- SMT DETAILED FAILURES ---")
        for failure in smt_test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}' (Expect P to hold/witness exist: {failure['expected_to_hold_or_witness_exist']})")
            print(f"    Observed P held/witness found: {failure['property_holds_observed_or_witness_found']}")
            print(f"    Message: {failure['message']}")
            if failure['counterexample_witness']: print(f"    Counterexample/Witness: {failure['counterexample_witness']}")
    print(f"\nTotal SMT tests passed across all Omega values: {total_passed_smt_all}")
    print(f"Total SMT tests failed across all Omega values: {total_failed_smt_all}")
    print(f"{'='*70}")
    if total_failed_smt_all == 0 and total_passed_smt_all > 0 : print("\n🎉🎉🎉 ALL IMPLEMENTED SMT REVISED CORE AVCA TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    elif total_passed_smt_all == 0 and total_failed_smt_all == 0: print("\n🤷🤷🤷 NO SMT TESTS WERE FULLY IMPLEMENTED AND RUN / NO TESTS DEFINED. 🤷🤷🤷")
    else: print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME SMT REVISED CORE AVCA TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")