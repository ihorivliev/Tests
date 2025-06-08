# PoC Script 3: Minimal Multi-Scale Frame Mappings (Python+SMT) - Corrected

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Xor)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Global Variables (from your SMT script) ---
Omega_py: int = 0 # Used by get_base_avc_constraints to know current Omega context
smt_test_results_summary: Dict[int, Dict[str, int]] = {}
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

def get_base_avc_constraints(avc_repr: Dict[str, FNode], current_omega_val_for_constraints: int, omega_smt_node: FNode) -> List[FNode]:
    # Pass python int for Omega_py context for this constraint generation
    global Omega_py
    original_omega_py = Omega_py
    Omega_py = current_omega_val_for_constraints # Temporarily set for this call

    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], omega_smt_node))
    ]
    if current_omega_val_for_constraints == 1: # Use passed omega for this logic
        constraints.append(Not(avc_repr["is_finite"]))
    
    Omega_py = original_omega_py # Restore global Omega_py
    return constraints

def avc_algebraic_unio_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    avc1_is_unio = Or(avc1["is_zero_aspect"], avc1["is_areo_aspect"])
    avc2_is_unio = Or(avc2["is_zero_aspect"], avc2["is_areo_aspect"])
    both_unio = And(avc1_is_unio, avc2_is_unio)
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_fp_equal_val)

def avc_add_core_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    
    res_is_val_of_b = And(Iff(res["is_zero_aspect"], b["is_zero_aspect"]), Iff(res["is_areo_aspect"], b["is_areo_aspect"]), 
                          Iff(res["is_finite"], b["is_finite"]), Equals(res["val"], b["val"]))
    res_is_val_of_a = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), Iff(res["is_areo_aspect"], a["is_areo_aspect"]), 
                          Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"]))

    case1_a_is_unio = Implies(a_is_unio, res_is_val_of_b)
    case2_b_is_unio = Implies(And(Not(a_is_unio), b_is_unio), res_is_val_of_a)
    
    sum_val = a["val"] + b["val"]
    # Additive DFI overflow yields Unio (Zero aspect for Core AVCA)
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_FP_sum_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], sum_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(sum_val < omega_smt_node, res_is_FP_sum_formula, res_is_ZU_formula))
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

# --- Mapping Function Logic Builders ---
def map_S2_to_S3_smt_logic(s2_val: Dict[str, FNode], s3_val: Dict[str, FNode],
                           omega2_smt: FNode, omega3_smt: FNode) -> FNode:
    """ Maps val from AVCA-Omega=2 to AVCA-Omega=3.
        Unio_S2 (any aspect) -> Unio_S3 (Zero aspect for simplicity in mapping)
        Fp(1)_S2 -> Fp(1)_S3
    """
    s2_is_unio = Or(s2_val["is_zero_aspect"], s2_val["is_areo_aspect"])
    
    # Define s3_val as Unio(Zero aspect) for S3
    s3_is_ZU_s3 = And(s3_val["is_zero_aspect"], Not(s3_val["is_areo_aspect"]), Not(s3_val["is_finite"]), Equals(s3_val["val"], Int(0)))
    # Define s3_val as Fp(1) for S3
    s3_is_FP1_s3 = And(Not(s3_val["is_zero_aspect"]), Not(s3_val["is_areo_aspect"]), s3_val["is_finite"], Equals(s3_val["val"], Int(1)))

    map_unio_case = Implies(s2_is_unio, s3_is_ZU_s3)
    map_fp1_case = Implies(And(s2_val["is_finite"], Equals(s2_val["val"], Int(1))), s3_is_FP1_s3)
    
    # Ensure s2_val is one of these two cases for Omega=2 (Unio or Fp(1))
    # This is implicitly handled by base constraints on s2_val for Omega=2.
    return And(map_unio_case, map_fp1_case)


def map_S3_to_S2_smt_logic(s3_val: Dict[str, FNode], s2_val: Dict[str, FNode],
                           omega3_smt: FNode, omega2_smt: FNode) -> FNode:
    """ Maps val from AVCA-Omega=3 to AVCA-Omega=2.
        Unio_S3 (any aspect) -> Unio_S2 (Zero aspect for simplicity)
        Fp(1)_S3 -> Fp(1)_S2
        Fp(2)_S3 -> Unio_S2 (Zero aspect - information loss/collapse)
    """
    s3_is_unio = Or(s3_val["is_zero_aspect"], s3_val["is_areo_aspect"])

    # Define s2_val as Unio(Zero aspect) for S2
    s2_is_ZU_s2 = And(s2_val["is_zero_aspect"], Not(s2_val["is_areo_aspect"]), Not(s2_val["is_finite"]), Equals(s2_val["val"], Int(0)))
    # Define s2_val as Fp(1) for S2
    s2_is_FP1_s2 = And(Not(s2_val["is_zero_aspect"]), Not(s2_val["is_areo_aspect"]), s2_val["is_finite"], Equals(s2_val["val"], Int(1)))

    map_unio_case = Implies(s3_is_unio, s2_is_ZU_s2)
    map_fp1_case = Implies(And(s3_val["is_finite"], Equals(s3_val["val"], Int(1))), s2_is_FP1_s2)
    map_fp2_case = Implies(And(s3_val["is_finite"], Equals(s3_val["val"], Int(2))), s2_is_ZU_s2) # Fp(2)_S3 collapses to Unio_S2

    return And(map_unio_case, map_fp1_case, map_fp2_case)


# SMT Prover function (simplified for PoC output)
def prove_multiscale_poc(property_name: str,
                         setup_formulas: List[FNode],
                         property_to_verify: FNode,
                         relevant_vars_for_ce: List[Dict[str, Any]],
                         expect_property_to_hold: bool):
    # Omega_py is set by the calling test function for base constraints of initial values
    print(f"\n--- Testing (Multi-Scale PoC): {property_name} (Expect: {'Holds' if expect_property_to_hold else 'Fails/CE'}) ---")
    with Solver(name="z3") as s:
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)
        
        s.add_assertion(Not(property_to_verify)) # We are checking for counterexamples to the property
        
        ce_found = s.solve() # True if a counterexample is found

        property_actually_held = not ce_found
        
        if property_actually_held == expect_property_to_hold:
            print(f"✅ PASSED: Expectation met. Property {'universally holds' if property_actually_held else 'found counterexample as expected'}.")
            if not property_actually_held and ce_found: # Expected CE, and found CE
                model = s.get_model(); ce_parts = []
                for repr_dict in relevant_vars_for_ce:
                    name = repr_dict['name']
                    # (Simplified CE printing - actual model value extraction is complex)
                    is_z = model.get_value(repr_dict['is_zero_aspect']).is_true()
                    is_a = model.get_value(repr_dict['is_areo_aspect']).is_true()
                    is_f = model.get_value(repr_dict['is_finite']).is_true()
                    val_smt = model.get_value(repr_dict['val'])
                    val = val_smt.constant_value() if val_smt is not None else '?'
                    state_str = f"U({val},{'Z' if is_z else 'A'})" if is_z or is_a else f"Fp({val})"
                    ce_parts.append(f"{name}={state_str}")
                print(f"     Counterexample (confirming non-universality or expected failure): {'; '.join(ce_parts)}")
        else:
            print(f"❌ FAILED: Expectation NOT met. Property {'was expected to hold but found CE' if expect_property_to_hold else 'was expected to have CE but held universally'}.")
            if ce_found: 
                model = s.get_model(); ce_parts = []
                for repr_dict in relevant_vars_for_ce:
                    name = repr_dict['name']
                    is_z = model.get_value(repr_dict['is_zero_aspect']).is_true()
                    is_a = model.get_value(repr_dict['is_areo_aspect']).is_true()
                    is_f = model.get_value(repr_dict['is_finite']).is_true()
                    val_smt = model.get_value(repr_dict['val'])
                    val = val_smt.constant_value() if val_smt is not None else '?'
                    state_str = f"U({val},{'Z' if is_z else 'A'})" if is_z or is_a else f"Fp({val})"
                    ce_parts.append(f"{name}={state_str}")
                print(f"     Counterexample (property failed): {'; '.join(ce_parts)}")


# --- PoC Test: Associativity of Addition Across Scales ---
def test_poc_multiscale_add_associativity():
    omega_s2_py = 2
    omega_s3_py = 3
    omega_s2_smt = Int(omega_s2_py)
    omega_s3_smt = Int(omega_s3_py)

    property_name = f"PoC Test: Add Associativity S2 vs S2->S3->S2"

    # Symbolic values in S2
    a_s2 = create_symbolic_avc_val("a_s2")
    b_s2 = create_symbolic_avc_val("b_s2")
    c_s2 = create_symbolic_avc_val("c_s2")

    # --- Path 1: Direct computation in S2: (a_s2 + b_s2) + c_s2 ---
    ab_s2_direct = create_symbolic_avc_val("ab_s2_direct")
    lhs_s2_direct = create_symbolic_avc_val("lhs_s2_direct")
    
    # --- Path 2: Map to S3, compute, map back to S2 ---
    # Mapped values in S3
    a_s3 = create_symbolic_avc_val("a_s3")
    b_s3 = create_symbolic_avc_val("b_s3")
    c_s3 = create_symbolic_avc_val("c_s3")
    # Intermediate results in S3
    ab_s3_mapped = create_symbolic_avc_val("ab_s3_mapped")
    lhs_s3_mapped = create_symbolic_avc_val("lhs_s3_mapped")
    # Result mapped back to S2
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

    # Path 1 logic (direct in S2)
    setup.append(avc_add_core_smt_logic(a_s2, b_s2, ab_s2_direct, omega_s2_smt))
    setup.append(avc_add_core_smt_logic(ab_s2_direct, c_s2, lhs_s2_direct, omega_s2_smt))

    # Path 2 logic (S2 -> S3 -> S2)
    # Mapping S2 inputs to S3
    setup.append(map_S2_to_S3_smt_logic(a_s2, a_s3, omega_s2_smt, omega_s3_smt))
    setup.append(map_S2_to_S3_smt_logic(b_s2, b_s3, omega_s2_smt, omega_s3_smt))
    setup.append(map_S2_to_S3_smt_logic(c_s2, c_s3, omega_s2_smt, omega_s3_smt))
    # Computation in S3
    setup.append(avc_add_core_smt_logic(a_s3, b_s3, ab_s3_mapped, omega_s3_smt))
    setup.append(avc_add_core_smt_logic(ab_s3_mapped, c_s3, lhs_s3_mapped, omega_s3_smt))
    # Mapping S3 result back to S2
    setup.append(map_S3_to_S2_smt_logic(lhs_s3_mapped, lhs_s2_via_s3, omega_s3_smt, omega_s2_smt))

    # Property to verify: Does lhs_s2_direct == lhs_s2_via_s3?
    # We expect this to FAIL due to information loss and different algebra.
    property_formula = avc_algebraic_unio_equiv_smt(lhs_s2_direct, lhs_s2_via_s3)
    
    # For the PoC, list all intermediate and final values for potential CE output
    relevant_vars = [a_s2, b_s2, c_s2, ab_s2_direct, lhs_s2_direct, 
                     a_s3, b_s3, c_s3, ab_s3_mapped, lhs_s3_mapped, 
                     lhs_s2_via_s3]

    prove_multiscale_poc(property_name, setup, property_formula, relevant_vars,
                         expect_property_to_hold=False) # Expect False (i.e., expect a CE showing they differ)

if __name__ == "__main__":
    print("Starting PoC Script 3: Minimal Multi-Scale Frame Mappings...")
    # Set global Omega_py context for base constraints if not passed directly
    # In this script, get_base_avc_constraints takes current_omega_val_for_constraints
    
    test_poc_multiscale_add_associativity()

    print("\n--- PoC Summary ---")
    if not smt_test_failures_details: # Assuming prove_multiscale_poc populates these globals
         print("PoC tests completed. Check output for PASSED/FAILED status and counterexamples.")
    else:
        print("PoC tests completed with failures or expected counterexamples found. Review details above.")