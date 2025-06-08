# PoC Script 3.1: Enhanced Multi-Scale Frame Mappings Test (Python+SMT) - Corrected

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Xor)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Global Variables ---
Omega_py_context: int = 0 # Context for get_base_avc_constraints
smt_test_results_summary: Dict[str, Dict[str, int]] = {} # omega_key -> pass/fail
smt_test_failures_details: List[Dict[str, Any]] = []

# --- Symbolic Core AVCA Definitions (Re-used) ---
def create_symbolic_avc_val(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_zero_aspect", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_areo_aspect", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], current_omega_for_constraints: int, omega_smt_node: FNode) -> List[FNode]:
    global Omega_py_context
    original_omega_py_context = Omega_py_context
    Omega_py_context = current_omega_for_constraints

    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], omega_smt_node))
    ]
    if current_omega_for_constraints == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    
    Omega_py_context = original_omega_py_context
    return constraints

def avc_algebraic_unio_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    avc1_is_unio = Or(avc1["is_zero_aspect"], avc1["is_areo_aspect"])
    avc2_is_unio = Or(avc2["is_zero_aspect"], avc2["is_areo_aspect"])
    both_unio = And(avc1_is_unio, avc2_is_unio)
    # For Unio equivalence, aspects don't matter if both are Unio.
    # This PoC previously used a stricter check for modal Unio. For algebraic, this is fine.

    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_fp_equal_val)

def avc_add_core_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    # Standard Core AVCA-Ω addition logic
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    
    res_is_val_of_b = And(Iff(res["is_zero_aspect"], b["is_zero_aspect"]), Iff(res["is_areo_aspect"], b["is_areo_aspect"]), 
                          Iff(res["is_finite"], b["is_finite"]), Equals(res["val"], b["val"]))
    res_is_val_of_a = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), Iff(res["is_areo_aspect"], a["is_areo_aspect"]), 
                          Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"]))

    case1_a_is_unio = Implies(a_is_unio, res_is_val_of_b)
    case2_b_is_unio = Implies(And(Not(a_is_unio), b_is_unio), res_is_val_of_a)
    
    sum_val = a["val"] + b["val"]
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_FP_sum_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], sum_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(sum_val < omega_smt_node, res_is_FP_sum_formula, res_is_ZU_formula))
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

# --- Mapping Function Logic Builders (Minimal & Principled) ---
def map_S2_to_S3_smt_logic(s2_val: Dict[str, FNode], s3_val: Dict[str, FNode],
                           omega2_smt_node: FNode, omega3_smt_node: FNode) -> FNode: # Added omega nodes for clarity
    s2_is_unio = Or(s2_val["is_zero_aspect"], s2_val["is_areo_aspect"])
    
    # Define s3_val as Unio (Zero aspect) for S3
    s3_is_ZU_s3 = And(s3_val["is_zero_aspect"], Not(s3_val["is_areo_aspect"]), Not(s3_val["is_finite"]), Equals(s3_val["val"], Int(0)))
    # Define s3_val as Fp(1) for S3
    s3_is_FP1_s3 = And(Not(s3_val["is_zero_aspect"]), Not(s3_val["is_areo_aspect"]), s3_val["is_finite"], Equals(s3_val["val"], Int(1)))

    map_unio_case = Implies(s2_is_unio, s3_is_ZU_s3) # Map S2 Unio to S3 Zero-Unio
    map_fp1_case = Implies(And(s2_val["is_finite"], Equals(s2_val["val"], Int(1))), s3_is_FP1_s3)
    
    return And(map_unio_case, map_fp1_case)


def map_S3_to_S2_smt_logic(s3_val: Dict[str, FNode], s2_val: Dict[str, FNode],
                           omega3_smt_node: FNode, omega2_smt_node: FNode) -> FNode: # Added omega nodes
    s3_is_unio = Or(s3_val["is_zero_aspect"], s3_val["is_areo_aspect"])

    # Define s2_val as Unio (Zero aspect) for S2
    s2_is_ZU_s2 = And(s2_val["is_zero_aspect"], Not(s2_val["is_areo_aspect"]), Not(s2_val["is_finite"]), Equals(s2_val["val"], Int(0)))
    # Define s2_val as Fp(1) for S2
    s2_is_FP1_s2 = And(Not(s2_val["is_zero_aspect"]), Not(s2_val["is_areo_aspect"]), s2_val["is_finite"], Equals(s2_val["val"], Int(1)))

    map_unio_case = Implies(s3_is_unio, s2_is_ZU_s2) # Map S3 Unio to S2 Zero-Unio
    map_fp1_case = Implies(And(s3_val["is_finite"], Equals(s3_val["val"], Int(1))), s2_is_FP1_s2)
    # Fp(2)_S3 collapses to Unio_S2 (Zero aspect) due to DFI constraint of S2
    map_fp2_case = Implies(And(s3_val["is_finite"], Equals(s3_val["val"], Int(2))), s2_is_ZU_s2) 

    return And(map_unio_case, map_fp1_case, map_fp2_case)


# SMT Prover function
def prove_multiscale_poc(property_name: str,
                         setup_formulas: List[FNode],
                         property_to_verify: FNode,
                         relevant_vars_for_ce: List[Dict[str, Any]],
                         expect_property_to_hold: bool,
                         omega_context_for_report: str ): # Added for clarity in output
    global Omega_py_context # Relies on global context if not passed to base_constraints

    # Use a unique key for the summary for each test run
    test_key = f"{property_name}_OmegaContext_{omega_context_for_report}"
    if test_key not in smt_test_results_summary:
        smt_test_results_summary[test_key] = {"passed": 0, "failed": 0}

    print(f"\n--- Testing ({omega_context_for_report}): {property_name} (Expect Property to Hold: {expect_property_to_hold}) ---")
    with Solver(name="z3") as s:
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)
        
        # Standard way for universal properties: Add Not(Property). If UNSAT, Property HOLDS. If SAT, Property FAILS (model is CE).
        s.add_assertion(Not(property_to_verify))
        
        ce_found = s.solve() # True if a counterexample to property_to_verify is found

        property_actually_held = not ce_found 
        success_for_summary = (property_actually_held == expect_property_to_hold)
        status_emoji = "✅" if success_for_summary else "❌"
        final_message = ""

        if success_for_summary:
            final_message = f"Expectation met. Property was {'PROVED universally' if property_actually_held else 'correctly SHOWN NON-UNIVERSAL (CE found)'}."
        else:
            final_message = f"Expectation NOT met. Property was {'expected to hold but FAILED (CE found)' if expect_property_to_hold else 'expected to be non-universal but HELD universally (no CE found)'}."

        print(f"{status_emoji} {final_message}")

        if ce_found: # A counterexample to property_to_verify was found
            model = s.get_model(); ce_parts = []
            for repr_dict in relevant_vars_for_ce:
                name = repr_dict['name']
                is_z_smt = model.get_value(repr_dict['is_zero_aspect'], None)
                is_a_smt = model.get_value(repr_dict['is_areo_aspect'], None)
                is_f_smt = model.get_value(repr_dict['is_finite'], None)
                val_smt = model.get_value(repr_dict['val'], None)

                is_z = is_z_smt.is_true() if is_z_smt is not None else False
                is_a = is_a_smt.is_true() if is_a_smt is not None else False
                is_f = is_f_smt.is_true() if is_f_smt is not None else False
                val = val_smt.constant_value() if val_smt is not None else '?'
                
                state_str = f"U({val},{'Z' if is_z else 'A'})" if is_z or is_a else (f"Fp({val})" if is_f else "InvalidState")
                ce_parts.append(f"{name}={state_str}")
            label = "Counterexample (confirming non-universality or property failure)"
            print(f"     {label}: {'; '.join(ce_parts)}")
            smt_test_failures_details.append({
                "property": property_name, "omega_context": omega_context_for_report,
                "expectation_met": success_for_summary, "message": final_message,
                "counterexample": '; '.join(ce_parts)
            })
        
        if success_for_summary:
            smt_test_results_summary[test_key]["passed"] += 1
        else:
            smt_test_results_summary[test_key]["failed"] += 1


# --- PoC Test 1 (from original PoC3): Associativity Transformation ---
def test_poc_multiscale_add_associativity_transformation():
    omega_s2_py = 2
    omega_s3_py = 3
    omega_s2_smt = Int(omega_s2_py)
    omega_s3_smt = Int(omega_s3_py)

    property_name = f"PoC3.1 Test 1: (a+b)+c in S2 vs Mapped S2->S3->S2"

    a_s2 = create_symbolic_avc_val("a_s2"); b_s2 = create_symbolic_avc_val("b_s2"); c_s2 = create_symbolic_avc_val("c_s2")
    ab_s2_direct = create_symbolic_avc_val("ab_s2_direct"); lhs_s2_direct = create_symbolic_avc_val("lhs_s2_direct")
    
    a_s3 = create_symbolic_avc_val("a_s3"); b_s3 = create_symbolic_avc_val("b_s3"); c_s3 = create_symbolic_avc_val("c_s3")
    ab_s3_mapped = create_symbolic_avc_val("ab_s3_mapped"); lhs_s3_mapped = create_symbolic_avc_val("lhs_s3_mapped")
    lhs_s2_via_s3 = create_symbolic_avc_val("lhs_s2_via_s3")

    setup = \
        get_base_avc_constraints(a_s2, omega_s2_py, omega_s2_smt) + \
        get_base_avc_constraints(b_s2, omega_s2_py, omega_s2_smt) + \
        get_base_avc_constraints(c_s2, omega_s2_py, omega_s2_smt) + \
        get_base_avc_constraints(ab_s2_direct, omega_s2_py, omega_s2_smt) + \
        get_base_avc_constraints(lhs_s2_direct, omega_s2_py, omega_s2_smt) + \
        get_base_avc_constraints(a_s3, omega_s3_py, omega_s3_smt) + \
        get_base_avc_constraints(b_s3, omega_s3_py, omega_s3_smt) + \
        get_base_avc_constraints(c_s3, omega_s3_py, omega_s3_smt) + \
        get_base_avc_constraints(ab_s3_mapped, omega_s3_py, omega_s3_smt) + \
        get_base_avc_constraints(lhs_s3_mapped, omega_s3_py, omega_s3_smt) + \
        get_base_avc_constraints(lhs_s2_via_s3, omega_s2_py, omega_s2_smt)

    setup.append(avc_add_core_smt_logic(a_s2, b_s2, ab_s2_direct, omega_s2_smt))
    setup.append(avc_add_core_smt_logic(ab_s2_direct, c_s2, lhs_s2_direct, omega_s2_smt))

    setup.append(map_S2_to_S3_smt_logic(a_s2, a_s3, omega_s2_smt, omega_s3_smt))
    setup.append(map_S2_to_S3_smt_logic(b_s2, b_s3, omega_s2_smt, omega_s3_smt))
    setup.append(map_S2_to_S3_smt_logic(c_s2, c_s3, omega_s2_smt, omega_s3_smt))
    setup.append(avc_add_core_smt_logic(a_s3, b_s3, ab_s3_mapped, omega_s3_smt))
    setup.append(avc_add_core_smt_logic(ab_s3_mapped, c_s3, lhs_s3_mapped, omega_s3_smt))
    setup.append(map_S3_to_S2_smt_logic(lhs_s3_mapped, lhs_s2_via_s3, omega_s3_smt, omega_s2_smt))

    property_formula = avc_algebraic_unio_equiv_smt(lhs_s2_direct, lhs_s2_via_s3)
    relevant_vars = [a_s2, b_s2, c_s2, ab_s2_direct, lhs_s2_direct, 
                     a_s3, b_s3, c_s3, ab_s3_mapped, lhs_s3_mapped, 
                     lhs_s2_via_s3]
    prove_multiscale_poc(property_name, setup, property_formula, relevant_vars,
                         expect_property_to_hold=False, omega_context_for_report="S2 vs S2->S3->S2")

# --- PoC Test 2: Information Loss and Operational Equivalence Breakdown ---
def test_poc_multiscale_information_loss():
    omega_s2_py = 2
    omega_s3_py = 3
    omega_s2_smt = Int(omega_s2_py)
    omega_s3_smt = Int(omega_s3_py)
    property_name = "PoC3.1 Test 2: Info Loss (Fp(2)_S3 -> U_S2) & Op Equivalence"

    # Values in S3
    val1_s3 = create_symbolic_avc_val("val1_s3") # To be Fp(2)_S3
    val2_s3 = create_symbolic_avc_val("val2_s3") # To be Fp(1)_S3
    res_s3  = create_symbolic_avc_val("res_s3")  # val1_s3 + val2_s3

    # Mapped values to S2
    val1_s2_mapped = create_symbolic_avc_val("val1_s2_mapped")
    val2_s2_mapped = create_symbolic_avc_val("val2_s2_mapped")
    res_s2_from_mapped_inputs = create_symbolic_avc_val("res_s2_from_mapped_inputs")
    
    # Result from S3 mapped to S2
    res_s3_mapped_to_s2 = create_symbolic_avc_val("res_s3_mapped_to_s2")

    setup = \
        get_base_avc_constraints(val1_s3, omega_s3_py, omega_s3_smt) + \
        get_base_avc_constraints(val2_s3, omega_s3_py, omega_s3_smt) + \
        get_base_avc_constraints(res_s3, omega_s3_py, omega_s3_smt) + \
        get_base_avc_constraints(val1_s2_mapped, omega_s2_py, omega_s2_smt) + \
        get_base_avc_constraints(val2_s2_mapped, omega_s2_py, omega_s2_smt) + \
        get_base_avc_constraints(res_s2_from_mapped_inputs, omega_s2_py, omega_s2_smt) + \
        get_base_avc_constraints(res_s3_mapped_to_s2, omega_s2_py, omega_s2_smt)

    # Constrain val1_s3 to be Fp(2)_S3 and val2_s3 to be Fp(1)_S3
    setup.append(val1_s3["is_finite"]); setup.append(Equals(val1_s3["val"], Int(2)))
    setup.append(val2_s3["is_finite"]); setup.append(Equals(val2_s3["val"], Int(1)))

    # Operation in S3: res_s3 = Fp(2)_S3 + Fp(1)_S3 
    # In S3 (Omega=3), 2+1=3, so res_s3 should be ZERO_UNIO_S3
    setup.append(avc_add_core_smt_logic(val1_s3, val2_s3, res_s3, omega_s3_smt))

    # Map S3 inputs to S2
    setup.append(map_S3_to_S2_smt_logic(val1_s3, val1_s2_mapped, omega_s3_smt, omega_s2_smt)) # Fp(2)_S3 -> Unio_S2
    setup.append(map_S3_to_S2_smt_logic(val2_s3, val2_s2_mapped, omega_s3_smt, omega_s2_smt)) # Fp(1)_S3 -> Fp(1)_S2

    # Operation in S2 with mapped inputs: res_s2_from_mapped_inputs = val1_s2_mapped + val2_s2_mapped
    # Should be Unio_S2 + Fp(1)_S2 -> Fp(1)_S2
    setup.append(avc_add_core_smt_logic(val1_s2_mapped, val2_s2_mapped, res_s2_from_mapped_inputs, omega_s2_smt))
    
    # Map S3 result to S2: res_s3_mapped_to_s2 = map(res_s3)
    # res_s3 was ZERO_UNIO_S3, so this should be ZERO_UNIO_S2
    setup.append(map_S3_to_S2_smt_logic(res_s3, res_s3_mapped_to_s2, omega_s3_smt, omega_s2_smt))

    # Property to verify: Does map(val1_s3 + val2_s3) == map(val1_s3) + map(val2_s3) ?
    # i.e. res_s3_mapped_to_s2 == res_s2_from_mapped_inputs
    # Expect FAIL: ZERO_UNIO_S2 vs Fp(1)_S2
    property_formula = avc_algebraic_unio_equiv_smt(res_s3_mapped_to_s2, res_s2_from_mapped_inputs)
    relevant_vars = [val1_s3, val2_s3, res_s3, 
                     val1_s2_mapped, val2_s2_mapped, res_s2_from_mapped_inputs,
                     res_s3_mapped_to_s2]
    
    prove_multiscale_poc(property_name, setup, property_formula, relevant_vars,
                         expect_property_to_hold=False, omega_context_for_report="S3 vs S3->S2 ops")


if __name__ == "__main__":
    print("Starting PoC Script 3.1: Enhanced Multi-Scale Frame Mappings Test...")
    
    # Test 1 (Original PoC3 test)
    # Set global Omega_py context for get_base_avc_constraints if needed by some path.
    # Here, each call to get_base_avc_constraints specifies its omega.
    test_poc_multiscale_add_associativity_transformation()

    # Test 2 (New test for information loss)
    test_poc_multiscale_information_loss()

    print("\n--- PoC 3.1 Summary ---")
    if not smt_test_failures_details:
         print("PoC tests completed. Check output for PASSED/FAILED status and counterexamples.")
    else:
        print("PoC tests completed with failures or expected counterexamples found. Review details above.")
        for failure in smt_test_failures_details:
            print(f"  Detail: Omega Context: {failure['omega_context']}, Property: '{failure['property']}'")
            print(f"    Message: {failure['message']}")
            if failure['counterexample']:
                print(f"    Counterexample: {failure['counterexample']}")