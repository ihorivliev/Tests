import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- PySMT Imports ---
try:
    from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                                 ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals,
                                 GT, GE, LT, LE, Times, Div) # Added Times, Div
    from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
    from pysmt.fnode import FNode
    SMT_MODE_AVAILABLE = True
except ImportError:
    SMT_MODE_AVAILABLE = False
    # Print warning during SMT test execution

# --- Configuration ---
SMT_SOLVER_NAME = "z3"

# --- SMT Harness Components (Embedded for self-containment) ---
# These model the Core AVCA-Ω v1.2b specification from Appendix A of AVCA Core DraftV4

smt_test_summary_6B = {}
Omega_py_smt_6B: int = 0 # Global Omega for SMT builder context if needed by base constraints

# Symbolic Representation (aspect-aware for v1.2b)
def create_symbolic_avc_val_v12b(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_Zaspect", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_Aaspect", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_F", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints_v12b(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    is_unio = Or(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"])
    constraints = [
        Iff(is_unio, Not(avc_repr["is_finite"])),
        Implies(avc_repr["is_zero_aspect"], Not(avc_repr["is_areo_aspect"])),
        
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], omega_smt_node))
    ]
    if current_omega_py == 1:
        constraints.append(Not(avc_repr["is_finite"]))
        constraints.append(Implies(is_unio, Or(Equals(avc_repr["val"], Int(0)), Equals(avc_repr["val"], omega_smt_node))))
    return constraints

def avc_equiv_smt_v12b(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    avc1_is_unio = Or(avc1["is_zero_aspect"], avc1["is_areo_aspect"])
    avc2_is_unio = Or(avc2["is_zero_aspect"], avc2["is_areo_aspect"])
    both_unio = And(avc1_is_unio, avc2_is_unio)
    both_dfi_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_dfi_equal_val)

# SMT Logic Builders for Core AVCA-Ω v1.2b operations
def avc_add_smt_logic_v11(a: Dict[str, FNode], b: Dict[str, FNode],
                          res: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    res_becomes_a = And(Iff(res["is_zero_aspect"],a["is_zero_aspect"]), Iff(res["is_areo_aspect"],a["is_areo_aspect"]), Iff(res["is_finite"],a["is_finite"]), Equals(res["val"],a["val"]))
    res_becomes_b = And(Iff(res["is_zero_aspect"],b["is_zero_aspect"]), Iff(res["is_areo_aspect"],b["is_areo_aspect"]), Iff(res["is_finite"],b["is_finite"]), Equals(res["val"],b["val"]))
    case1 = Implies(a_is_unio, res_becomes_b)
    case2 = Implies(And(a["is_finite"], b_is_unio), res_becomes_a)
    s_val = Plus(a["val"], b["val"])
    res_is_dfi = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), Equals(res["val"], s_val))
    res_is_areo = And(Not(res["is_finite"]), res["is_areo_aspect"], Not(res["is_zero_aspect"]), Equals(res["val"], omega_smt_node))
    case3 = Implies(And(a["is_finite"], b["is_finite"]), Ite(s_val < omega_smt_node, res_is_dfi, res_is_areo))
    return And(case1, case2, case3)

def avc_mul_smt_logic_v12(a: Dict[str, FNode], b: Dict[str, FNode],
                          res: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    a_is_areo_aspected = a["is_areo_aspect"]
    b_is_areo_aspected = b["is_areo_aspect"]
    cond_any_unio_areo = Or(a_is_areo_aspected, b_is_areo_aspected)
    res_is_zero_unio = And(Not(res["is_finite"]), res["is_zero_aspect"], Not(res["is_areo_aspect"]), Equals(res["val"], Int(0)))
    res_is_areo_unio = And(Not(res["is_finite"]), res["is_areo_aspect"], Not(res["is_zero_aspect"]), Equals(res["val"], omega_smt_node))
    unio_case = Ite(cond_any_unio_areo, res_is_areo_unio, res_is_zero_unio)
    p_val = Times(a["val"], b["val"]) # Changed from Python '*' to SMT 'Times'
    res_is_dfi = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), Equals(res["val"], p_val))
    dfi_case = Ite(And(p_val >= Int(1), p_val < omega_smt_node), res_is_dfi, res_is_areo_unio)
    return Ite(Or(a_is_unio, b_is_unio), unio_case, dfi_case)

def avc_div_smt_logic_v12B(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    res_is_zero_unio = And(Not(res["is_finite"]), res["is_zero_aspect"], Not(res["is_areo_aspect"]), Equals(res["val"], Int(0)))
    res_is_areo_unio = And(Not(res["is_finite"]), res["is_areo_aspect"], Not(res["is_zero_aspect"]), Equals(res["val"], omega_smt_node))

    # Rule B1: Divisor b is Unio -> AREO_UNIO
    rule_b1_consequent = res_is_areo_unio
    
    # Rule B2: Dividend a is Unio AND Divisor b is DFI -> Preserves Dividend's Unio aspect
    # (b is DFI is implicit if not b_is_unio)
    rule_b2_consequent = Ite(a["is_zero_aspect"], res_is_zero_unio, res_is_areo_unio)

    # Rule B3: Both DFI
    # Need to model divmod carefully for SMT. Standard SMT integer division is often truncated.
    # We need quotient and remainder.
    # SMT typically provides `div` (integer division, truncates towards zero) and `mod` or `rem`.
    # Python's `divmod(x, y)` gives `(x // y, x % y)`. `x % y` has same sign as `y`.
    # Since DFI values are positive, SMT `div` and `mod` should be okay.
    q_sym = Symbol(f"{res['name']}_q_div_b3", SMT_INT_TYPE)
    r_sym = Symbol(f"{res['name']}_r_div_b3", SMT_INT_TYPE)

    # Constraints for q_sym and r_sym if using them explicitly
    # If b["val"] could be 0, this would be an issue, but _check_val ensures DFI b["val"] >= 1
    # For DFI a,b: a_val = q_val * b_val + r_val AND 0 <= r_val < b_val
    # We can use Ite to define q_sym and r_sym based on b["val"] != 0
    # However, simpler is to directly express conditions on a["val"] and b["val"] for the result.
    
    # If b_val is 0, division is undefined (SMT might allow it or give error if not guarded)
    # Here, b["is_finite"] implies b["val"] >= 1 for Omega > 1.
    # If Omega=1, b must be Unio, handled by b_is_unio.
    
    # Condition for exact division: a_val % b_val == 0
    # We can express a_val % b_val == 0 as Exists k_mult: a_val == k_mult * b_val
    # Or rely on SMT's mod operator if available and matches Python's positive divisor behavior
    # Let's use SMT's div and derive remainder: q_temp = Div(a["val"], b["val"]), r_derived = Minus(a["val"], Times(q_temp, b["val"]))
    
    q_derived = Div(a["val"], b["val"]) # SMT integer division
    r_derived = (a["val"] - (q_derived * b["val"])) # Remainder derived like Python

    quotient_is_valid_dfi_cond = And(Equals(r_derived, Int(0)), # exact division
                                     q_derived >= Int(1),
                                     q_derived < omega_smt_node)
    
    res_is_FP_quotient = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]),
                             Equals(res["val"], q_derived))
    
    dfi_dfi_case = Ite(And(a["is_finite"], b["is_finite"]), # Only if both are DFI
                       Ite(quotient_is_valid_dfi_cond,
                           res_is_FP_quotient,
                           res_is_areo_unio), # Not exact or quotient not valid DFI
                       TRUE() # Should not be reached if logic covers all cases
                      )
    
    return Ite(b_is_unio, rule_b1_consequent,                                       # If b is Unio
               Ite(a_is_unio, rule_b2_consequent,                                   # Else if a is Unio (b must be DFI)
                   dfi_dfi_case))                                                   # Else (both a and b are DFI)

def prove_or_find_counterexample_smt_6B(
    property_name: str, omega_py_val: int, setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    
    global smt_test_summary_6B, Omega_py_smt_6B
    Omega_py_smt_6B = omega_py_val
    
    if not SMT_MODE_AVAILABLE:
        print(f"SKIPPED (SMT Mode Unavailable) for {property_name} Ω={omega_py_val}")
        if omega_py_val not in smt_test_summary_6B:
            smt_test_summary_6B[omega_py_val] = {"passed": 0, "failed": 0, "skipped": 0}
        smt_test_summary_6B[omega_py_val]["skipped"] += 1
        return

    if omega_py_val not in smt_test_summary_6B:
        smt_test_summary_6B[omega_py_val] = {"passed": 0, "failed": 0, "skipped": 0}

    print(f"  SMT Test (6B): '{property_name}' for Ω={omega_py_val} (Expect: {'Hold/Exist' if expect_property_to_hold else 'Fail/Not Exist'})", end=" ... ")
    
    property_holds_observed = False; counterexample_witness_str = None
    try:
        with Solver(name=SMT_SOLVER_NAME, logic="LIA") as s:
            for f_setup in setup_formulas: s.add_assertion(f_setup)
            formula_to_check = Not(property_to_verify) if not is_existential else property_to_verify
            if s.solve([formula_to_check]):
                if is_existential: property_holds_observed = True
                else: property_holds_observed = False
                model = s.get_model(); ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z = model.get_value(repr_dict['is_zero_aspect']).is_true()
                        is_a = model.get_value(repr_dict['is_areo_aspect']).is_true()
                        is_f = model.get_value(repr_dict['is_finite']).is_true()
                        val_smt = model.get_value(repr_dict['val'])
                        state_str = "Unknown"
                        if is_f: state_str = f"Fp({val_smt})"
                        elif is_z: state_str = "ZERO_UNIO"
                        elif is_a: state_str = "AREO_UNIO"
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts)
            else: # UNSAT
                if is_existential: property_holds_observed = False
                else: property_holds_observed = True
        
        success = (property_holds_observed == expect_property_to_hold)
        if success:
            print("PASS")
            smt_test_summary_6B[omega_py_val]["passed"] += 1
            if counterexample_witness_str and is_existential and expect_property_to_hold: print(f"    Witness (as expected): {counterexample_witness_str}")
            elif counterexample_witness_str and not is_existential and not expect_property_to_hold: print(f"    Counterexample (as expected for failure): {counterexample_witness_str}")
        else:
            print(f"FAIL (Observed: {'Holds/Exists' if property_holds_observed else 'Fails/Not Exist'})")
            smt_test_summary_6B[omega_py_val]["failed"] += 1
            if counterexample_witness_str:
                 label = "Unexpected Witness" if is_existential and property_holds_observed else \
                         "Counterexample (property unexpectedly failed)" if not is_existential and not property_holds_observed else \
                         "Witness NOT Found (but was expected)" if is_existential and not property_holds_observed else \
                         "No Counterexample Found (property unexpectedly held)"
                 print(f"    {label}: {counterexample_witness_str if counterexample_witness_str else '(No model value)'}")
            elif not property_holds_observed and expect_property_to_hold and is_existential: print(f"    Witness NOT Found (but was expected)")
            elif property_holds_observed and not expect_property_to_hold and not is_existential: print(f"    No Counterexample Found (property unexpectedly held)")
    except Exception as e:
        print(f"ERROR ({e})")
        smt_test_summary_6B[omega_py_val]["failed"] += 1

# --- Test Definitions for Suite 6.B ---
def test_div_round_trip_unconstrained(omega_val_py: int):
    prop_name = "6.B.1: Division Round-Trip Unconstrained ((a⊘b)⊗b == a)"
    omega_smt = Int(omega_val_py)
    a = create_symbolic_avc_val_v12b("a_rtu")
    b = create_symbolic_avc_val_v12b("b_rtu")
    q = create_symbolic_avc_val_v12b("q_rtu") # q = a ⊘ b
    lhs = create_symbolic_avc_val_v12b("lhs_rtu") # lhs = q ⊗ b

    setup = get_base_avc_constraints_v12b(a, omega_smt, omega_val_py) + \
            get_base_avc_constraints_v12b(b, omega_smt, omega_val_py) + \
            get_base_avc_constraints_v12b(q, omega_smt, omega_val_py) + \
            get_base_avc_constraints_v12b(lhs, omega_smt, omega_val_py)
    
    setup.append(avc_div_smt_logic_v12B(a, b, q, omega_smt, omega_val_py))
    setup.append(avc_mul_smt_logic_v12(q, b, lhs, omega_smt, omega_val_py))
    
    property_formula = avc_equiv_smt_v12b(lhs, a)
    # Expected to FAIL for many cases (e.g. if b is Unio, q=AREO_UNIO, lhs=AREO_UNIO, may not equal original 'a')
    prove_or_find_counterexample_smt_6B(prop_name, omega_val_py, setup, property_formula, [a,b], expect_property_to_hold=False)

def test_div_round_trip_b_is_dfi(omega_val_py: int):
    prop_name = "6.B.2: Division Round-Trip (b is DFI)"
    if omega_val_py == 1: # No DFI
        prove_or_find_counterexample_smt_6B(prop_name + " (SKIPPED)", omega_val_py, [], TRUE(), [], True)
        return
    omega_smt = Int(omega_val_py)
    a=create_symbolic_avc_val_v12b("a_rt_bdfi"); b=create_symbolic_avc_val_v12b("b_rt_bdfi")
    q=create_symbolic_avc_val_v12b("q_rt_bdfi"); lhs=create_symbolic_avc_val_v12b("lhs_rt_bdfi")
    setup = get_base_avc_constraints_v12b(a,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(b,omega_smt,omega_val_py) + \
            get_base_avc_constraints_v12b(q,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(lhs,omega_smt,omega_val_py)
    setup.append(b["is_finite"]) # Constraint: b is DFI
    setup.append(avc_div_smt_logic_v12B(a,b,q,omega_smt,omega_val_py))
    setup.append(avc_mul_smt_logic_v12(q,b,lhs,omega_smt,omega_val_py))
    property_formula = avc_equiv_smt_v12b(lhs,a)
    prove_or_find_counterexample_smt_6B(prop_name, omega_val_py, setup, property_formula, [a,b], expect_property_to_hold=False) # Still expect fails

def test_div_round_trip_b_dfi_q_dfi(omega_val_py: int):
    prop_name = "6.B.3: Division Round-Trip (b is DFI, q=a⊘b is DFI)"
    if omega_val_py == 1: prove_or_find_counterexample_smt_6B(prop_name + " (SKIPPED)", omega_val_py, [], TRUE(), [], True); return
    omega_smt=Int(omega_val_py); a=create_symbolic_avc_val_v12b("a_rt_bqdfi"); b=create_symbolic_avc_val_v12b("b_rt_bqdfi")
    q=create_symbolic_avc_val_v12b("q_rt_bqdfi"); lhs=create_symbolic_avc_val_v12b("lhs_rt_bqdfi")
    setup = get_base_avc_constraints_v12b(a,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(b,omega_smt,omega_val_py) + \
            get_base_avc_constraints_v12b(q,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(lhs,omega_smt,omega_val_py)
    setup.append(b["is_finite"]); setup.append(q["is_finite"]) # Constraints
    setup.append(avc_div_smt_logic_v12B(a,b,q,omega_smt,omega_val_py))
    setup.append(avc_mul_smt_logic_v12(q,b,lhs,omega_smt,omega_val_py))
    property_formula = avc_equiv_smt_v12b(lhs,a)
    prove_or_find_counterexample_smt_6B(prop_name, omega_val_py, setup, property_formula, [a,b], expect_property_to_hold=False) # Still expect fails if q*b overflows

def test_div_round_trip_clean_dfi(omega_val_py: int):
    prop_name = "6.B.4: Division Round-Trip (b DFI, q=a⊘b DFI, r=(q⊗b) DFI)"
    if omega_val_py == 1: prove_or_find_counterexample_smt_6B(prop_name + " (SKIPPED)", omega_val_py, [], TRUE(), [], True); return
    omega_smt=Int(omega_val_py); a=create_symbolic_avc_val_v12b("a_rt_cdf"); b=create_symbolic_avc_val_v12b("b_rt_cdf")
    q=create_symbolic_avc_val_v12b("q_rt_cdf"); lhs=create_symbolic_avc_val_v12b("lhs_rt_cdf")
    setup = get_base_avc_constraints_v12b(a,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(b,omega_smt,omega_val_py) + \
            get_base_avc_constraints_v12b(q,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(lhs,omega_smt,omega_val_py)
    setup.append(b["is_finite"]); setup.append(q["is_finite"]); setup.append(lhs["is_finite"]) # All DFI
    # We also need to ensure 'a' itself is DFI for this 'clean DFI' case
    setup.append(a["is_finite"])
    setup.append(avc_div_smt_logic_v12B(a,b,q,omega_smt,omega_val_py))
    setup.append(avc_mul_smt_logic_v12(q,b,lhs,omega_smt,omega_val_py))
    property_formula = avc_equiv_smt_v12b(lhs,a)
    prove_or_find_counterexample_smt_6B(prop_name, omega_val_py, setup, property_formula, [a,b], expect_property_to_hold=True)

def test_div_round_trip_a_is_ZU_b_is_DFI(omega_val_py: int):
    prop_name = "6.B.5: Division Round-Trip (a=ZERO_UNIO, b=DFI)"
    if omega_val_py == 1: prove_or_find_counterexample_smt_6B(prop_name + " (SKIPPED)", omega_val_py, [], TRUE(), [], True); return
    omega_smt=Int(omega_val_py); a=create_symbolic_avc_val_v12b("a_rt_zudfi"); b=create_symbolic_avc_val_v12b("b_rt_zudfi")
    q=create_symbolic_avc_val_v12b("q_rt_zudfi"); lhs=create_symbolic_avc_val_v12b("lhs_rt_zudfi")
    setup = get_base_avc_constraints_v12b(a,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(b,omega_smt,omega_val_py) + \
            get_base_avc_constraints_v12b(q,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(lhs,omega_smt,omega_val_py)
    setup.append(a["is_zero_aspect"]); setup.append(b["is_finite"]) # Constraints
    setup.append(avc_div_smt_logic_v12B(a,b,q,omega_smt,omega_val_py)) # q should be ZU
    setup.append(avc_mul_smt_logic_v12(q,b,lhs,omega_smt,omega_val_py)) # ZU * DFI should be ZU
    property_formula = avc_equiv_smt_v12b(lhs,a) # Should be ZU == ZU
    prove_or_find_counterexample_smt_6B(prop_name, omega_val_py, setup, property_formula, [a,b], expect_property_to_hold=True)

def test_div_round_trip_a_is_AU_b_is_DFI(omega_val_py: int):
    prop_name = "6.B.6: Division Round-Trip (a=AREO_UNIO, b=DFI)"
    if omega_val_py == 1: prove_or_find_counterexample_smt_6B(prop_name + " (SKIPPED)", omega_val_py, [], TRUE(), [], True); return
    omega_smt=Int(omega_val_py); a=create_symbolic_avc_val_v12b("a_rt_audfi"); b=create_symbolic_avc_val_v12b("b_rt_audfi")
    q=create_symbolic_avc_val_v12b("q_rt_audfi"); lhs=create_symbolic_avc_val_v12b("lhs_rt_audfi")
    setup = get_base_avc_constraints_v12b(a,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(b,omega_smt,omega_val_py) + \
            get_base_avc_constraints_v12b(q,omega_smt,omega_val_py) + get_base_avc_constraints_v12b(lhs,omega_smt,omega_val_py)
    setup.append(a["is_areo_aspect"]); setup.append(b["is_finite"]) # Constraints
    setup.append(avc_div_smt_logic_v12B(a,b,q,omega_smt,omega_val_py)) # q should be AU
    setup.append(avc_mul_smt_logic_v12(q,b,lhs,omega_smt,omega_val_py)) # AU * DFI should be AU
    property_formula = avc_equiv_smt_v12b(lhs,a) # Should be AU == AU
    prove_or_find_counterexample_smt_6B(prop_name, omega_val_py, setup, property_formula, [a,b], expect_property_to_hold=True)

# Main execution block
if __name__ == "__main__":
    print("====== AVCA Suite 6.B: Division Round-Trip Law Tests (⊘_v1.2B, ⊗_v1.2) ======")
    omegas_for_smt_6B = [2, 3, 5, 7] # As per plan

    if not SMT_MODE_AVAILABLE:
        print("\nSKIPPING SMT-based tests for Suite 6.B as PySMT is not available.")
    else:
        print("\n--- Running SMT-based Tests for Suite 6.B ---")
        for omega_test in omegas_for_smt_6B:
            print(f"\n-- SMT Tests for Ω = {omega_test} --")
            Omega_py_smt_6B = omega_test # Set global for SMT base constraints if needed

            test_div_round_trip_unconstrained(omega_test)
            test_div_round_trip_b_is_dfi(omega_test)
            test_div_round_trip_b_dfi_q_dfi(omega_test)
            test_div_round_trip_clean_dfi(omega_test)
            test_div_round_trip_a_is_ZU_b_is_DFI(omega_test)
            test_div_round_trip_a_is_AU_b_is_DFI(omega_test)

        print("\n--- SMT Test Summary (Suite 6.B) ---")
        for o, res in sorted(smt_test_summary_6B.items()):
            print(f"  Ω={o}: Passed={res['passed']}, Failed={res['failed']}, Skipped={res['skipped']}")
    
    print("\n====== Suite 6.B Finished ======")