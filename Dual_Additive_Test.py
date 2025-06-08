# PoC Script 1: Minimal Mode-Switching Unio (Python+SMT) - Corrected

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, And, Or, Not, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, ForAll, Exists)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Literal

# --- Global Variables ---
Omega_py: int = 0 # Set by test runner
smt_test_results_summary: Dict[int, Dict[str, int]] = {} # For PoC, keep it simple
smt_test_failures_details: List[Dict[str, Any]] = []    # For PoC, keep it simple


# --- Symbolic Modal AVCA Definitions ---
def create_symbolic_modal_avc_val(name_prefix: str) -> Dict[str, Any]:
    """Creates symbolic components for a Modal AVCVal."""
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_zero_aspect", SMT_BOOL_TYPE), # Conceptual Zero-aspect
        "is_areo_aspect": Symbol(f"{name_prefix}_is_areo_aspect", SMT_BOOL_TYPE), # Conceptual Areo-aspect
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE), # Underlying integer value
        "is_identity_mode": Symbol(f"{name_prefix}_is_identity_mode", SMT_BOOL_TYPE), # True if Unio is in identity mode for add
        "is_absorb_mode": Symbol(f"{name_prefix}_is_absorb_mode", SMT_BOOL_TYPE),  # True if Unio is in absorb mode for add
        "name": name_prefix
    }

def get_base_modal_avc_constraints(avc_repr: Dict[str, FNode], omega_smt_node: FNode) -> List[FNode]:
    """Basic constraints for a well-formed symbolic Modal AVCVal."""
    constraints = [
        # Element type: Unio (via aspect) or Finite
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        # DFI value constraints
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        # Unio value conventions (aspect related)
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], omega_smt_node)), # Areo aspect means val is Omega
        # Mode constraints: Only Unio has a mode; DFI does not. Unio must be in one mode.
        Implies(avc_repr["is_finite"], And(Not(avc_repr["is_identity_mode"]), Not(avc_repr["is_absorb_mode"]))),
        Implies(Or(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"]),
                ExactlyOne(avc_repr["is_identity_mode"], avc_repr["is_absorb_mode"]))
    ]
    if Omega_py == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_modal_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    """
    SMT formula for equivalence of two symbolic Modal AVCVals.
    For this PoC, two Unios are only equivalent if their aspects AND modes are the same.
    This differs from Core AVCA-Ω's ZS~AS if we want to track modal effects.
    Alternatively, one could define algebraic equivalence ignoring mode for some tests.
    Let's start with strict equivalence (aspect and mode must match for Unios).
    """
    both_zs_id_mode = And(avc1["is_zero_aspect"], avc1["is_identity_mode"], avc2["is_zero_aspect"], avc2["is_identity_mode"])
    both_zs_ab_mode = And(avc1["is_zero_aspect"], avc1["is_absorb_mode"], avc2["is_zero_aspect"], avc2["is_absorb_mode"])
    both_as_id_mode = And(avc1["is_areo_aspect"], avc1["is_identity_mode"], avc2["is_areo_aspect"], avc2["is_identity_mode"])
    both_as_ab_mode = And(avc1["is_areo_aspect"], avc1["is_absorb_mode"], avc2["is_areo_aspect"], avc2["is_absorb_mode"])
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_zs_id_mode, both_zs_ab_mode, both_as_id_mode, both_as_ab_mode, both_fp_equal_val)

def avc_algebraic_unio_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    """ Equivalence where all Unios are one, regardless of aspect or mode (like Core AVCA). """
    avc1_is_unio = Or(avc1["is_zero_aspect"], avc1["is_areo_aspect"])
    avc2_is_unio = Or(avc2["is_zero_aspect"], avc2["is_areo_aspect"])
    both_unio = And(avc1_is_unio, avc2_is_unio)
    both_fp_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_fp_equal_val)


# --- SMT Logic Builders for Modal AVCA ---

# For this PoC, sub, mul, div results will set Unio modes. Add will respect modes.

def set_unio_result_state(res: Dict[str, FNode], aspect_is_zero: bool, mode_is_identity: bool, omega_smt_node: FNode) -> FNode:
    """Helper to constrain a Unio result's aspect and mode."""
    aspect_val_formula = Int(0) if aspect_is_zero else omega_smt_node # aspect_val is FNode
    return And(
        res["is_zero_aspect"] if aspect_is_zero else Not(res["is_zero_aspect"]),
        res["is_areo_aspect"] if not aspect_is_zero else Not(res["is_areo_aspect"]),
        Not(res["is_finite"]),
        Equals(res["val"], aspect_val_formula),
        res["is_identity_mode"] if mode_is_identity else Not(res["is_identity_mode"]),
        res["is_absorb_mode"] if not mode_is_identity else Not(res["is_absorb_mode"])
    )

def set_dfi_result_state(res: Dict[str, FNode], value_node: FNode) -> FNode:
    """Helper to constrain a DFI result."""
    return And(
        Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), res["is_finite"],
        Equals(res["val"], value_node),
        Not(res["is_identity_mode"]), Not(res["is_absorb_mode"]) # DFIs have no mode
    )

def avc_add_modal_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                            res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])

    # Case 1: 'a' is Unio
    a_is_identity_mode_unio = And(a_is_unio, a["is_identity_mode"])
    a_is_absorb_mode_unio = And(a_is_unio, a["is_absorb_mode"])

    # Result is b (DFI or Unio - copy b's full state including mode if b is Unio)
    res_eq_b_full_state = And(
        Iff(res["is_zero_aspect"], b["is_zero_aspect"]),
        Iff(res["is_areo_aspect"], b["is_areo_aspect"]),
        Iff(res["is_finite"], b["is_finite"]),
        Equals(res["val"], b["val"]),
        Iff(res["is_identity_mode"], b["is_identity_mode"]), # if b is Unio, copy its mode
        Iff(res["is_absorb_mode"], b["is_absorb_mode"])
    )
    
    # Result is a (Unio - copy a's full state)
    res_eq_a_full_state = And(
        Iff(res["is_zero_aspect"], a["is_zero_aspect"]),
        Iff(res["is_areo_aspect"], a["is_areo_aspect"]),
        Iff(res["is_finite"], a["is_finite"]),
        Equals(res["val"], a["val"]),
        Iff(res["is_identity_mode"], a["is_identity_mode"]), # Preserve a's mode
        Iff(res["is_absorb_mode"], a["is_absorb_mode"])
    )

    case1_a_unio = Implies(a_is_identity_mode_unio, res_eq_b_full_state)
    case1b_a_unio = Implies(a_is_absorb_mode_unio, res_eq_a_full_state)

    # Case 2: 'b' is Unio (and 'a' is DFI)
    b_is_identity_mode_unio = And(b_is_unio, b["is_identity_mode"])
    b_is_absorb_mode_unio = And(b_is_unio, b["is_absorb_mode"])

    # Result is a (DFI - no mode)
    res_eq_a_dfi_state = And(
        Iff(res["is_zero_aspect"], a["is_zero_aspect"]), # Will be False as 'a' is DFI
        Iff(res["is_areo_aspect"], a["is_areo_aspect"]), # Will be False
        Iff(res["is_finite"], a["is_finite"]),           # Will be True
        Equals(res["val"], a["val"]),
        Not(res["is_identity_mode"]), Not(res["is_absorb_mode"]) # DFI result has no mode
    )
    
    # Result is b (Unio - copy b's full state)
    res_eq_b_full_state = And(
        Iff(res["is_zero_aspect"], b["is_zero_aspect"]),
        Iff(res["is_areo_aspect"], b["is_areo_aspect"]),
        Iff(res["is_finite"], b["is_finite"]),
        Equals(res["val"], b["val"]),
        Iff(res["is_identity_mode"], b["is_identity_mode"]), # Preserve b's mode
        Iff(res["is_absorb_mode"], b["is_absorb_mode"])
    )

    case2_b_unio = Implies(And(a["is_finite"], b_is_identity_mode_unio), res_eq_a_dfi_state)
    case2b_b_unio = Implies(And(a["is_finite"], b_is_absorb_mode_unio), res_eq_b_full_state)

    # Case 3: Both 'a' and 'b' are DFI
    sum_val = a["val"] + b["val"]
    # Additive DFI overflow yields Unio(aspect='zero', mode='identity')
    res_is_ZU_id_mode = set_unio_result_state(res, aspect_is_zero=True, mode_is_identity=True, omega_smt_node=omega_smt_node)
    res_is_FP_sum = set_dfi_result_state(res, sum_val)
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(sum_val < omega_smt_node,
                                res_is_FP_sum,
                                res_is_ZU_id_mode))
    return And(case1_a_unio, case1b_a_unio, case2_b_unio, case2b_b_unio, case3_dfi_dfi)

# --- Core AVCA-Ω ops (for setting modes based on their results) ---
# These are simplified versions from "AVCA_CORE_1_revised" logic builders,
# adapted to produce a modal Unio result for this PoC.

def avc_mul_core_sets_mode_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                                     res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])

    # Case 1: a is Unio - result aspect from 'a', mode depends on aspect
    # PoC: Zero-aspect Unio multiplication yields identity_mode Unio
    # PoC: Areo-aspect Unio multiplication yields absorb_mode Unio
    res_a_is_ZU_id = set_unio_result_state(res, aspect_is_zero=True, mode_is_identity=True, omega_smt_node=omega_smt_node)
    res_a_is_AS_ab = set_unio_result_state(res, aspect_is_zero=False, mode_is_identity=False, omega_smt_node=omega_smt_node)
    case1_a_unio = Implies(a_is_unio, Ite(a["is_zero_aspect"], res_a_is_ZU_id, res_a_is_AS_ab))

    # Case 2: b is Unio (and a is DFI) - result aspect from 'b', mode depends on aspect
    res_b_is_ZU_id = set_unio_result_state(res, aspect_is_zero=True, mode_is_identity=True, omega_smt_node=omega_smt_node)
    res_b_is_AS_ab = set_unio_result_state(res, aspect_is_zero=False, mode_is_identity=False, omega_smt_node=omega_smt_node)
    case2_b_unio = Implies(And(a["is_finite"], b_is_unio), Ite(b["is_zero_aspect"], res_b_is_ZU_id, res_b_is_AS_ab))

    # Case 3: DFI * DFI
    prod_val = a["val"] * b["val"]
    res_is_FP_prod = set_dfi_result_state(res, prod_val)
    # DFI Mul overflow yields Unio(aspect='areo', mode='absorb')
    res_is_AS_ab_overflow = set_unio_result_state(res, aspect_is_zero=False, mode_is_identity=False, omega_smt_node=omega_smt_node)
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(And(prod_val < omega_smt_node, prod_val > Int(0)), # DFI product must be > 0
                                res_is_FP_prod,
                                res_is_AS_ab_overflow))
    return And(case1_a_unio, case2_b_unio, case3_dfi_dfi)

def avc_sub_core_smt_logic_for_mode_reset(a: Dict[str, FNode], b: Dict[str, FNode],
                                          res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])

    # Result 'a' state (if DFI, no mode; if Unio, copy mode from 'a')
    res_eq_a_dfi_no_mode = set_dfi_result_state(res, a["val"]) # Assumes a is DFI for this path
    res_eq_a_unio_id_mode = set_unio_result_state(res, aspect_is_zero=True, mode_is_identity=True, omega_smt_node=omega_smt_node) # Placeholder, aspect needs to be from 'a'
    res_eq_a_unio_ab_mode = set_unio_result_state(res, aspect_is_zero=True, mode_is_identity=False, omega_smt_node=omega_smt_node) # Placeholder

    # More precise state copy for 'a' if it's Unio
    res_a_copy_logic = Ite(a["is_zero_aspect"],
                           Ite(a["is_identity_mode"],
                               set_unio_result_state(res, aspect_is_zero=True, mode_is_identity=True, omega_smt_node=omega_smt_node),
                               set_unio_result_state(res, aspect_is_zero=True, mode_is_identity=False, omega_smt_node=omega_smt_node)),
                           Ite(a["is_identity_mode"],
                               set_unio_result_state(res, aspect_is_zero=False, mode_is_identity=True, omega_smt_node=omega_smt_node),
                               set_unio_result_state(res, aspect_is_zero=False, mode_is_identity=False, omega_smt_node=omega_smt_node))
                          )

    # Case 1: b is Unio (any mode/aspect) -> result is 'a' (copying its aspect and mode if Unio, no mode if DFI)
    case1_b_unio = Implies(b_is_unio,
                           Ite(a_is_unio,
                               res_a_copy_logic, # res is Unio, copies a's aspect and mode
                               set_dfi_result_state(res, a["val"]) # res is DFI, copies a's DFI val
                           ))

    # Case 2: a is Unio, b is DFI
    # PoC Rule: Unio(any_aspect, mode='absorb') - DFI_k -> Unio(aspect='areo', mode='identity') -- RESET!
    res_is_AS_id_mode_reset = set_unio_result_state(res, aspect_is_zero=False, mode_is_identity=True, omega_smt_node=omega_smt_node)
    # Standard Core AVCA like: Unio(any_aspect, mode='identity') - DFI_k -> Unio(aspect='areo', mode='absorb' by default from underflow)
    res_is_AS_ab_mode_stuck = set_unio_result_state(res, aspect_is_zero=False, mode_is_identity=False, omega_smt_node=omega_smt_node)

    case2_a_unio_b_dfi = Implies(And(a_is_unio, b["is_finite"]),
                                 Ite(a["is_absorb_mode"], # If a is in absorb_mode
                                     res_is_AS_id_mode_reset,  # Then RESET to identity mode
                                     res_is_AS_ab_mode_stuck   # Else (identity mode a) standard 'stuck-at-areo' (becomes absorb mode)
                                 ))

    # Case 3: DFI - DFI
    diff_val = a["val"] - b["val"]
    res_is_FP_diff = set_dfi_result_state(res, diff_val)
    # DFI Sub underflow/cancellation yields Unio(aspect='areo', mode='absorb' by default)
    res_is_AS_ab_mode_underflow = set_unio_result_state(res, aspect_is_zero=False, mode_is_identity=False, omega_smt_node=omega_smt_node)
    case3_dfi_dfi = Implies(And(a["is_finite"], b["is_finite"]),
                            Ite(a["val"] > b["val"],
                                res_is_FP_diff,
                                res_is_AS_ab_mode_underflow))
    return And(case1_b_unio, case2_a_unio_b_dfi, case3_dfi_dfi)


# SMT Prover function (simplified for PoC output)
def prove_modal_poc(property_name: str, omega_val: int, setup_formulas: List[FNode],
                    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
                    expect_property_to_hold: bool):
    global Omega_py
    Omega_py = omega_val # Set global for base_modal_avc_constraints
    print(f"\n--- Testing Omega={omega_val}: {property_name} (Expect: {'Holds' if expect_property_to_hold else 'Fails/Counterexample'}) ---")
    with Solver(name="z3") as s:
        for f_setup in setup_formulas:
            s.add_assertion(f_setup)
        
        # If expecting property to hold, we check if its negation is UNSAT
        # If expecting property to fail, we check if property itself is SAT (meaning a CE to its universality)
        query = Not(property_to_verify) if expect_property_to_hold else property_to_verify
        
        # For this PoC, let's assume property_to_verify IS the "stuck_condition"
        # So if expect_property_to_hold is False (expect NOT stuck), we want query to be UNSAT
        # If query = stuck_condition, and it's SAT, then we found "stuck", which is a "failure" if we expect not stuck.

        solve_result = s.solve() # Check if current assertions (including query if it's a condition) are SAT

        # Interpretation logic:
        # If expect_property_to_hold = True: we want property_to_verify to be a tautology.
        #     So, Not(property_to_verify) should be UNSAT. solve_result on Not(P) should be False.
        #     observed_holds = (s.solve([Not(property_to_verify)]) == False)
        # If expect_property_to_hold = False: we want property_to_verify to be NOT a tautology (i.e. CE exists).
        #     So, Not(property_to_verify) should be SAT. solve_result on Not(P) should be True.
        #     observed_holds = (s.solve([Not(property_to_verify)]) == True) -> this means CE to P exists, so P doesn't hold.

        # Simplified for this PoC's specific "stuck_condition" test:
        # property_to_verify IS the "stuck_condition".
        # expect_property_to_hold = False means we expect "stuck_condition" to be FALSE (no model).
        
        s.add_assertion(property_to_verify) # Add the actual condition we are testing for existence
        found_model_for_condition = s.solve()

        # If expect_property_to_hold is True, means condition should always be true. Then found_model_for_condition should be true.
        # If expect_property_to_hold is False, means condition should be false (no model). Then found_model_for_condition should be false.
        observed_as_expected = (found_model_for_condition == expect_property_to_hold)
        
        if observed_as_expected:
            print(f"✅ PASSED: Expectation met. Condition evaluated to {found_model_for_condition} as expected.")
            if found_model_for_condition and expect_property_to_hold: # Expected condition to be true, and it was
                model = s.get_model(); ce_parts = []
                # (Code to print witness similar to previous version)
                print(f"     Witness for condition holding: ... ") # Simplified for brevity
        else:
            print(f"❌ FAILED: Expectation NOT met. Condition evaluated to {found_model_for_condition}, expected {expect_property_to_hold}.")
            if found_model_for_condition : # A model was found
                model = s.get_model(); ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    is_z = model.get_value(repr_dict['is_zero_aspect']).is_true()
                    is_a = model.get_value(repr_dict['is_areo_aspect']).is_true()
                    is_f = model.get_value(repr_dict['is_finite']).is_true()
                    val_smt = model.get_value(repr_dict['val'])
                    val = val_smt.constant_value() if val_smt is not None else '?'
                    
                    id_m_smt = model.get_value(repr_dict['is_identity_mode'])
                    ab_m_smt = model.get_value(repr_dict['is_absorb_mode'])
                    id_m = id_m_smt.is_true() if id_m_smt is not None else False
                    ab_m = ab_m_smt.is_true() if ab_m_smt is not None else False

                    mode_str = "Id" if id_m else ("Ab" if ab_m else "--")
                    state_str = f"U({val},{'Z' if is_z else 'A'},{mode_str})" if is_z or is_a else f"Fp({val})"
                    ce_parts.append(f"{name}={state_str}")
                print(f"     Instance (violates expectation): {'; '.join(ce_parts)}")


# --- PoC Test: Can we get stuck in Absorb mode? ---
def test_poc_stuck_in_absorb_mode(omega_val_py: int):
    property_name = "PoC Test: Avoid Indefinite Stuck in Absorb Mode via Add/Mul/Sub Sequence"
    omega_smt_node = Int(omega_val_py)
    if omega_val_py <= 1: # DFI interactions are trivial or non-existent
        # This test relies on DFI interaction, so it's less meaningful for Omega=1
        print(f"\n--- Skipping Omega={omega_val_py}: {property_name} (needs DFI > 0) ---")
        return

    u_start = create_symbolic_modal_avc_val("u_start")
    dfi1    = create_symbolic_modal_avc_val("dfi1")
    res_mul1 = create_symbolic_modal_avc_val("res_mul1") # u_start * dfi1
    res_add1 = create_symbolic_modal_avc_val("res_add1") # res_mul1 + dfi1
    res_sub1 = create_symbolic_modal_avc_val("res_sub1") # res_add1 - dfi1 (should reset mode)
    res_add2 = create_symbolic_modal_avc_val("res_add2") # res_sub1 + dfi1 (should emerge)

    setup = get_base_modal_avc_constraints(u_start, omega_smt_node) + \
            get_base_modal_avc_constraints(dfi1, omega_smt_node) + \
            get_base_modal_avc_constraints(res_mul1, omega_smt_node) + \
            get_base_modal_avc_constraints(res_add1, omega_smt_node) + \
            get_base_modal_avc_constraints(res_sub1, omega_smt_node) + \
            get_base_modal_avc_constraints(res_add2, omega_smt_node)

    # Start u_start as Unio(aspect='areo', mode='identity') - e.g. after a prior reset or initial state
    setup.append(u_start["is_areo_aspect"]); setup.append(u_start["is_identity_mode"])
    # DFI value, for Omega > 1 ensure it's Fp(1)
    setup.append(dfi1["is_finite"])
    if omega_val_py > 1:
         setup.append(Equals(dfi1["val"], Int(1))) # Use Fp(1) for simplicity if DFI exists
    else: # Should have been skipped, but to be safe
         pass


    # Sequence:
    # 1. u_start * dfi1 -> res_mul1 (PoC rule: Areo-aspect Unio * DFI -> Unio(aspect=Areo, mode=Absorb) )
    setup.append(avc_mul_core_sets_mode_smt_logic(u_start, dfi1, res_mul1, omega_smt_node))
    # 2. res_mul1 + dfi1 -> res_add1 (if res_mul1 is Unio(mode='absorb'), this should be res_mul1)
    setup.append(avc_add_modal_smt_logic(res_mul1, dfi1, res_add1, omega_smt_node))
    # 3. res_add1 - dfi1 -> res_sub1 (PoC rule: Unio(mode='absorb') - DFI -> Unio(aspect=Areo, mode='identity') -- RESET!)
    setup.append(avc_sub_core_smt_logic_for_mode_reset(res_add1, dfi1, res_sub1, omega_smt_node))
    # 4. res_sub1 + dfi1 -> res_add2 (if res_sub1 is Unio(mode='identity'), this should be DFI value of dfi1)
    setup.append(avc_add_modal_smt_logic(res_sub1, dfi1, res_add2, omega_smt_node))

    # Property to test: Is it possible that the system *fails* to emerge?
    # i.e., res_mul1 became absorb_mode, res_add1 was absorbed,
    # res_sub1 FAILED to reset to identity_mode, OR res_add2 is NOT DFI.
    
    # Condition for being "stuck" or not emerging as expected:
    # We want to find if there's ANY assignment such that this sequence leads to non-emergence.
    # Successful emergence means res_add2 is finite. Failure is res_add2 is NOT finite.
    fails_to_emerge_condition = And(
        res_mul1["is_absorb_mode"],       # Check: mul correctly sets absorb mode
        # avc_modal_equiv_smt(res_add1, res_mul1), # Check: add was absorbed (optional check for debugging)
        # Not(res_sub1["is_identity_mode"]),      # Check: sub FAILED to reset (this makes it stricter)
        Not(res_add2["is_finite"])        # The ultimate failure: final result is not DFI
    )
    
    # We expect this "fails_to_emerge_condition" to be FALSE (i.e., no model for it, emergence always happens)
    prove_modal_poc(property_name, omega_val_py, setup, fails_to_emerge_condition,
                    [u_start, dfi1, res_mul1, res_add1, res_sub1, res_add2],
                    expect_property_to_hold=False) # False = we expect NO such "stuck" model to satisfy the condition

if __name__ == "__main__":
    omegas_to_test_modal_poc = [2, 3, 5] # Test for non-trivial DFI
    print("Starting PoC Script 1: Minimal Mode-Switching Unio...")
    for omega_val in omegas_to_test_modal_poc:
        test_poc_stuck_in_absorb_mode(omega_val)

    print("\n--- PoC Summary ---")
    # This summary logic would need to be adapted if using the global smt_test_results_summary
    # For this PoC, direct print output from prove_modal_poc is the primary result.
    if not smt_test_failures_details:
        print("PoC tests completed. Check output for PASSED/FAILED status and counterexamples.")
    else:
        print("PoC tests completed with failures. Review details above.")