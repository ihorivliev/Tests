# PoC Script 2: Binary Winding Number Arithmetic (Python+SMT) - Corrected for Unhashable List

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Xor)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Global Variables (from your SMT script) ---
Omega_py: int = 0
smt_test_results_summary: Dict[int, Dict[str, int]] = {}
smt_test_failures_details: List[Dict[str, Any]] = []

# --- Symbolic Core AVCA Definitions (from your SMT script) ---
def create_symbolic_avc_val(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_zero_aspect", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_areo_aspect", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], omega_smt_node: FNode) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], omega_smt_node))
    ]
    if Omega_py == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_algebraic_unio_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    avc1_is_unio = Or(avc1["is_zero_aspect"], avc1["is_areo_aspect"])
    avc2_is_unio = Or(avc2["is_zero_aspect"], avc2["is_areo_aspect"])
    both_unio = And(avc1_is_unio, avc2_is_unio)
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_fp_equal_val)

# SMT Logic Builders for Core AVCA-Ω operations (from your SMT script - slightly adapted for clarity)
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
    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_FP_sum_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], sum_val))
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]), Ite(sum_val < omega_smt_node, res_is_FP_sum_formula, res_is_ZU_formula))
    return And(case1_a_is_unio, case2_b_is_unio, case3_dfi_dfi)

# (Simplified avc_mul_core_smt_logic for PoC brevity - assumes ZU annihilates, AU from overflow)
def avc_mul_core_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_zu = a["is_zero_aspect"]
    b_is_zu = b["is_zero_aspect"]
    # Unused a_is_au = a["is_areo_aspect"]
    # Unused b_is_au = b["is_areo_aspect"]

    res_is_ZU_formula = And(res["is_zero_aspect"], Not(res["is_areo_aspect"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_AU_formula = And(Not(res["is_zero_aspect"]), res["is_areo_aspect"], Not(res["is_finite"]), Equals(res["val"], omega_smt_node))

    case_annihilation = Implies(Or(a_is_zu, b_is_zu), res_is_ZU_formula)
    
    prod_val = a["val"] * b["val"]
    res_is_FP_prod_formula = And(Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"], Equals(res["val"], prod_val))
    case_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                           Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), # DFI product must be > 0
                               res_is_FP_prod_formula,
                               res_is_AU_formula)) # DFI Mul overflow to AU

    # Simplified Unio * DFI (non-ZU) or Unio * Unio (non-ZU) -> AU for this PoC
    # This part of the logic was a bit hand-wavy in the original and needs to be consistent with avc_mul_sets_mode
    # For now, let's assume aspect propagation if not ZU.
    # Core AVCA aspect propagation for mul: if a is Unio, res aspect = a's aspect (unless ZU).
    # If a is Areo, b is DFI -> res is Areo
    a_is_areo_aspect_unio = a["is_areo_aspect"]
    b_is_areo_aspect_unio = b["is_areo_aspect"]

    case_a_is_au = Implies(And(a_is_areo_aspect_unio, Not(b_is_zu)), res_is_AU_formula)
    case_b_is_au_and_a_is_dfi = Implies(And(b_is_areo_aspect_unio, a["is_finite"]), res_is_AU_formula)


    return And(case_annihilation, case_dfi_dfi, case_a_is_au, case_b_is_au_and_a_is_dfi)


# --- Symbolic Winding Number AVCA Definitions ---
def create_symbolic_winding_avc_val(name_prefix: str) -> Dict[str, Any]:
    """Creates symbolic components for a Winding AVCVal (v_avc, n_bool)."""
    return {
        "v_avc": create_symbolic_avc_val(f"{name_prefix}_v"), # Core AVCA part
        "n_bool": Symbol(f"{name_prefix}_n", SMT_BOOL_TYPE),   # Winding bit (False=0, True=1)
        "name": name_prefix
    }

def get_base_winding_avc_constraints(w_avc_repr: Dict[str, Any], omega_smt_node: FNode) -> List[FNode]:
    """Basic constraints for a well-formed symbolic Winding AVCVal."""
    return get_base_avc_constraints(w_avc_repr["v_avc"], omega_smt_node) # n_bool needs no further constraints

def winding_avc_equiv_smt(w_avc1: Dict[str, Any], w_avc2: Dict[str, Any]) -> FNode:
    """SMT formula for equivalence of two symbolic Winding AVCVals."""
    v_equiv = avc_algebraic_unio_equiv_smt(w_avc1["v_avc"], w_avc2["v_avc"])
    n_equiv = Iff(w_avc1["n_bool"], w_avc2["n_bool"])
    return And(v_equiv, n_equiv)

# SMT Logic Builder for Winding Addition
def add_winding_smt_logic(wa: Dict[str, Any], wb: Dict[str, Any],
                          wres: Dict[str, Any], omega_smt_node: FNode) -> FNode:
    a_v = wa["v_avc"]; a_n = wa["n_bool"]
    b_v = wb["v_avc"]; b_n = wb["n_bool"]
    res_v = wres["v_avc"]; res_n = wres["n_bool"]

    # Intermediate symbolic variable for the core AVCA addition result for the v_avc parts
    temp_v_res = create_symbolic_avc_val(f"{wres['name']}_temp_v_add")
    
    # Formula defining temp_v_res based on a_v and b_v using core AVCA addition
    core_add_logic = avc_add_core_smt_logic(a_v, b_v, temp_v_res, omega_smt_node)
    
    # Constrain res_v (the v_avc part of the winding result) to be identical to temp_v_res
    res_v_logic = And(
        Iff(res_v["is_zero_aspect"], temp_v_res["is_zero_aspect"]),
        Iff(res_v["is_areo_aspect"], temp_v_res["is_areo_aspect"]),
        Iff(res_v["is_finite"], temp_v_res["is_finite"]),
        Equals(res_v["val"], temp_v_res["val"])
    )

    # Define winding number logic for res_n
    # PoC Rule:
    # - If core_add resulted in ZU (typically from DFI overflow, or Unio+Unio=Unio(ZU aspect)),
    #   it indicates a cycle completion/boundary interaction, toggle combined winding.
    # - Else (result is DFI or AU), XOR windings.
    n_res_final_logic = Ite(
        temp_v_res["is_zero_aspect"],       # If core AVCA result's v-part is Zero-Unio
        Iff(res_n, Not(Xor(a_n, b_n))),     # Toggle/flip the XORed winding of inputs
        Iff(res_n, Xor(a_n, b_n))           # Else, XOR the winding of inputs
    )
    
    # The final logic for add_winding is the conjunction of:
    # 1. The definition of the intermediate core AVCA sum (core_add_logic for temp_v_res).
    # 2. The definition of the final v-part of the result (res_v_logic).
    # 3. The definition of the final n-part of the result (n_res_final_logic).
    # Base constraints for temp_v_res are implicitly handled if avc_add_core_smt_logic is total
    # and correctly defines its output structure, which it should.
    return And(core_add_logic, res_v_logic, n_res_final_logic)


# SMT Prover function (simplified from your full SMT script)
def prove_winding_poc(property_name: str, omega_val: int, setup_formulas: List[FNode],
                      property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
                      expect_property_to_hold: bool):
    global Omega_py # Ensure global Omega_py is used by get_base_avc_constraints if called within
    Omega_py = omega_val
    print(f"\n--- Testing Omega={omega_val}: {property_name} (Expect: {'Holds' if expect_property_to_hold else 'Fails/CE'}) ---")
    with Solver(name="z3") as s:
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)
        
        # If expect_property_to_hold is True, we want to prove P. So we check if NOT P is UNSAT.
        # If expect_property_to_hold is False, we want to prove NOT P (i.e., find a CE for P). So we check if P is SAT.
        query = Not(property_to_verify) if expect_property_to_hold else property_to_verify
        
        solve_result_is_sat = s.solve() # Check if current assertions + query are SAT

        # Determine if the original property_to_verify holds based on solve_result_is_sat and expectation
        observed_property_holds: bool
        if expect_property_to_hold:
            observed_property_holds = not solve_result_is_sat # If Not(P) is UNSAT (false), then P holds
        else:
            observed_property_holds = solve_result_is_sat     # If P is SAT, then P can be true (CE to Not P found), so P fails to hold universally

        # This logic seems off. Let's simplify:
        # We add Not(P) to solver. If UNSAT -> P holds. If SAT -> P fails (CE found).
        # OR we add P to solver. If SAT -> P can be true (witness for existential). If UNSAT -> P is false.

        # Let's use the standard way for universal properties:
        # Add Not(Property). If UNSAT, Property HOLDS. If SAT, Property FAILS (model is CE).
        s.reset_assertions() # Clear previous assertions including the query
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)
        s.add_assertion(Not(property_to_verify))
        
        ce_found = s.solve() # True if counterexample to property_to_verify is found

        property_actually_held = not ce_found # Property held if no CE was found
        
        if property_actually_held == expect_property_to_hold:
            print(f"✅ PASSED: Expectation met. Property {'universally holds' if property_actually_held else 'found counterexample as expected'}.")
            if not property_actually_held and ce_found: # Expected CE, and found CE
                model = s.get_model(); ce_parts = []
                for w_repr_dict in inputs_reprs: # Ensure this list includes all relevant vars in property_to_verify
                    name = w_repr_dict['name']
                    v_avc = w_repr_dict['v_avc']
                    # Safe get_value
                    is_z_smt = model.get_value(v_avc['is_zero_aspect'], None)
                    is_a_smt = model.get_value(v_avc['is_areo_aspect'], None)
                    is_f_smt = model.get_value(v_avc['is_finite'], None)
                    val_smt = model.get_value(v_avc['val'], None)
                    n_val_smt = model.get_value(w_repr_dict['n_bool'], None)

                    is_z = is_z_smt.is_true() if is_z_smt else False
                    is_a = is_a_smt.is_true() if is_a_smt else False
                    is_f = is_f_smt.is_true() if is_f_smt else False
                    val = val_smt.constant_value() if val_smt else '?'
                    n_val = n_val_smt.is_true() if n_val_smt else False
                    
                    state_str = f"U({val},{'Z' if is_z else 'A'})" if is_z or is_a else f"Fp({val})"
                    ce_parts.append(f"{name}=({state_str}, n={1 if n_val else 0})")
                print(f"     Counterexample (confirming non-universality): {'; '.join(ce_parts)}")
        else:
            print(f"❌ FAILED: Expectation NOT met. Property {'was expected to hold but found CE' if expect_property_to_hold else 'was expected to have CE but held universally'}.")
            if ce_found: # A counterexample was found (but property was expected to hold)
                model = s.get_model(); ce_parts = []
                for w_repr_dict in inputs_reprs:
                    name = w_repr_dict['name']
                    v_avc = w_repr_dict['v_avc']
                    is_z_smt = model.get_value(v_avc['is_zero_aspect'], None)
                    is_a_smt = model.get_value(v_avc['is_areo_aspect'], None)
                    is_f_smt = model.get_value(v_avc['is_finite'], None)
                    val_smt = model.get_value(v_avc['val'], None)
                    n_val_smt = model.get_value(w_repr_dict['n_bool'], None)

                    is_z = is_z_smt.is_true() if is_z_smt else False
                    is_a = is_a_smt.is_true() if is_a_smt else False
                    is_f = is_f_smt.is_true() if is_f_smt else False
                    val = val_smt.constant_value() if val_smt else '?'
                    n_val = n_val_smt.is_true() if n_val_smt else False
                    state_str = f"U({val},{'Z' if is_z else 'A'})" if is_z or is_a else f"Fp({val})"
                    ce_parts.append(f"{name}=({state_str}, n={1 if n_val else 0})")
                print(f"     Counterexample (property failed): {'; '.join(ce_parts)}")

# --- PoC Test: Associativity of Winding Addition ---
def test_poc_winding_add_associativity(omega_val_py: int):
    expected_to_hold_assoc = (omega_val_py == 1) 
    property_name = "PoC Test: Associativity of Winding Addition ((wa+wb)+wc == wa+(wb+wc))"
    omega_smt_node = Int(omega_val_py)

    wa = create_symbolic_winding_avc_val("wa")
    wb = create_symbolic_winding_avc_val("wb")
    wc = create_symbolic_winding_avc_val("wc")
    
    w_ab = create_symbolic_winding_avc_val("w_ab") 
    w_lhs = create_symbolic_winding_avc_val("w_lhs")
    w_bc = create_symbolic_winding_avc_val("w_bc") 
    w_rhs = create_symbolic_winding_avc_val("w_rhs")

    # Intermediate core results (needed if their constraints are separate)
    # However, add_winding_smt_logic encapsulates these.

    setup = get_base_winding_avc_constraints(wa, omega_smt_node) + \
            get_base_winding_avc_constraints(wb, omega_smt_node) + \
            get_base_winding_avc_constraints(wc, omega_smt_node) + \
            get_base_winding_avc_constraints(w_ab, omega_smt_node) + \
            get_base_winding_avc_constraints(w_lhs, omega_smt_node) + \
            get_base_winding_avc_constraints(w_bc, omega_smt_node) + \
            get_base_winding_avc_constraints(w_rhs, omega_smt_node)
            
    # LHS
    setup.append(add_winding_smt_logic(wa, wb, w_ab, omega_smt_node))
    setup.append(add_winding_smt_logic(w_ab, wc, w_lhs, omega_smt_node))
    # RHS
    setup.append(add_winding_smt_logic(wb, wc, w_bc, omega_smt_node))
    setup.append(add_winding_smt_logic(wa, w_bc, w_rhs, omega_smt_node))

    associativity_formula = winding_avc_equiv_smt(w_lhs, w_rhs)
    
    prove_winding_poc(property_name, omega_val_py, setup, associativity_formula,
                      [wa, wb, wc, w_lhs, w_rhs], # Pass all relevant symbolic objects for CE printing
                      expect_property_to_hold=expected_to_hold_assoc)

if __name__ == "__main__":
    omegas_to_test_winding_poc = [1, 2, 3] 
    print("Starting PoC Script 2: Binary Winding Number Arithmetic...")
    for omega_val in omegas_to_test_winding_poc:
        # Initialize results for this Omega for this PoC run if using global summary
        if omega_val not in smt_test_results_summary:
             smt_test_results_summary[omega_val] = {"passed": 0, "failed": 0}

        test_poc_winding_add_associativity(omega_val)

    print("\n--- PoC Summary ---")
    if not smt_test_failures_details:
         print("PoC tests completed. Check output for PASSED/FAILED status and counterexamples.")
    else:
        print("PoC tests completed with failures. Review details above.")
        # Could print smt_test_failures_details here if populated by prove_winding_poc