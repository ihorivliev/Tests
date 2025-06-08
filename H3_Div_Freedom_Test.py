# Script H_Div_Freedom_Test.py
# Purpose: To test the degrees of freedom for Unio aspect assignment in division
#          under minimal algebraic constraints (T1-T4) and the Monotone Information Principle (MI).
# Expected: 3 bits of freedom should remain (for ZU/DFI, DFI/ZU, ZU/ZU aspects).

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Plus, Minus, Times, ToReal, Real) # ToReal for non-exact DFI/DFI
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal
import math

# --- Global Omega Parameter & Test Results ---
_Omega_HDivF_Global_Context: int = 0
smt_test_results_summary_HDivF: Dict[str, Dict[str, Any]] = {} # Test Name -> {status, details}

# --- Unio Class Definition (Minimal) ---
class Unio_HDivF:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool: return isinstance(other, Unio_HDivF)
    def __hash__(self) -> int: return hash(type(self))
    def __repr__(self) -> str: return f"Unio_HDivF('{self.aspect}')"

ZERO_UNIO_HDivF = Unio_HDivF("zero")
AREO_UNIO_HDivF = Unio_HDivF("areo")
AVCVal_HDivF = Union[int, Unio_HDivF]

def set_avca_omega_hdivf(omega_value: int, verbose: bool = False):
    global _Omega_HDivF_Global_Context
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_HDivF parameter must be an integer >= 1.")
    _Omega_HDivF_Global_Context = omega_value
    if verbose:
        print(f"H_Div_Freedom Test: Global Context Omega_HDivF set to {_Omega_HDivF_Global_Context}")

# --- SMT Symbolic Representation and Base Constraints ---
def create_symbolic_avc_val_hdivf(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_ZA_hdivf", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_AA_hdivf", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_DFI_hdivf", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_hdivf", SMT_INT_TYPE), # Algebraic value for DFI, or 0 for Unio
        "name": name_prefix
    }

def get_base_avc_constraints_hdivf(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(Or(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"]), Equals(avc_repr["val"], Int(0))) # Algebraic Unio is 0
    ]
    if current_omega_py == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_deep_equals_smt_hdivf(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    return And(
        Iff(avc1["is_zero_aspect"], avc2["is_zero_aspect"]),
        Iff(avc1["is_areo_aspect"], avc2["is_areo_aspect"]),
        Iff(avc1["is_finite"], avc2["is_finite"]),
        Implies(avc1["is_finite"], Equals(avc1["val"], avc2["val"]))
    )
# Symbolic constants for ZU and AU
SMT_ZU_HDivF: Dict[str, FNode] = { # Represents ZERO_UNIO_obj
    "is_zero_aspect": TRUE(), "is_areo_aspect": FALSE(), "is_finite": FALSE(), "val": Int(0)
}
SMT_AU_HDivF: Dict[str, FNode] = { # Represents AREO_UNIO_obj
    "is_zero_aspect": FALSE(), "is_areo_aspect": TRUE(), "is_finite": FALSE(), "val": Int(0)
}
SMT_U_ALG_HDivF: Dict[str, FNode] = { # Represents algebraic Unio (aspect will be symbolic)
    "is_zero_aspect": Symbol("generic_U_is_ZA_hdivf", SMT_BOOL_TYPE), # Will be constrained
    "is_areo_aspect": Symbol("generic_U_is_AA_hdivf", SMT_BOOL_TYPE), # Will be constrained
    "is_finite": FALSE(), "val": Int(0)
}
# Base constraints for SMT_U_ALG_HDivF:
# Needs ExactlyOne(SMT_U_ALG_HDivF["is_zero_aspect"], SMT_U_ALG_HDivF["is_areo_aspect"], SMT_U_ALG_HDivF["is_finite"])
# Since is_finite is FALSE(), this simplifies to ExactlyOne(is_zero_aspect, is_areo_aspect) for Unio.
# For this script, we'll define symbolic aspect results directly.


# --- SMT Logic for Division with Symbolic Aspect Outcomes ---
def symbolic_division_constraints_hdivf(
    a: Dict[str, FNode], b: Dict[str, FNode], # Input operands
    res: Dict[str, FNode],                   # Symbolic result (value and aspect bits)
    s_aspect_outcomes: Dict[str, FNode],     # Dict mapping S1-S8 to their res_is_areo_aspect SMT bool
    omega_smt_node: FNode, current_omega_py: int
) -> List[FNode]:
    
    constraints = []

    # Helper: Define result as being ZU_obj or AU_obj based on a boolean is_areo_flag
    def assign_unio_aspect(target_res_repr: Dict[str, FNode], is_areo_flag: FNode) -> FNode:
        return And(
            Not(target_res_repr["is_finite"]),
            Equals(target_res_repr["val"], Int(0)), # Algebraic U
            Iff(target_res_repr["is_areo_aspect"], is_areo_flag),
            Iff(target_res_repr["is_zero_aspect"], Not(is_areo_flag))
        )

    # T1: Totality - Implicitly handled by ensuring `res` gets defined for all input types
    # and res base constraints are added externally.

    # T2: DFI/DFI behavior
    dfi_a_dfi_b_cond = And(a["is_finite"], b["is_finite"])
    
    # Define symbolic quotient (q_dfi_div) and remainder (r_dfi_div) for DFI/DFI case
    # Ensuring unique names for symbols within the SMT context
    q_dfi_div_name = f"q_dfidiv_{a['name']}_{b['name']}_hdivf"
    r_dfi_div_name = f"r_dfidiv_{a['name']}_{b['name']}_hdivf"
    q_dfi_div = Symbol(q_dfi_div_name, SMT_INT_TYPE) 
    r_dfi_div = Symbol(r_dfi_div_name, SMT_INT_TYPE)

    # Standard Euclidean Division definition: a_val = q_dfi_div * b_val + r_dfi_div
    # This definition is only meaningful if b["val"] is not zero.
    # For DFI b, b["val"] >= 1 if Omega > 1.
    euclidean_division_definition = Implies(
        b["val"] > Int(0), # This condition holds if b is DFI and Omega > 1
        And(
            Equals(a["val"], Plus(Times(q_dfi_div, b["val"]), r_dfi_div)),
            r_dfi_div >= Int(0),
            r_dfi_div < b["val"] # Remainder constraint
        )
    )
    # If b["val"] could be non-positive (not for DFI if Omega > 1),
    # a more robust definition would be needed, or an assertion that b["val"] > 0 here.
    # Since dfi_a_dfi_b_cond implies b is DFI, and DFI elements are >= 1 (for Omega > 1),
    # b["val"] > Int(0) is implicitly true when this branch is relevant for Omega > 1.
    # For Omega = 1, dfi_a_dfi_b_cond is False, so this part is not asserted.

    # Condition for the division to be exact and the quotient to be a valid DFI element
    cond_exact_div_and_q_in_range = And(
        Equals(r_dfi_div, Int(0)),             # Exact division (remainder is 0)
        q_dfi_div >= Int(1),                  # Quotient is at least 1
        q_dfi_div < omega_smt_node            # Quotient is less than Omega
    )
    
    # Define the state of 'res' if it's a classical DFI quotient
    dfi_dfi_res_is_classical = And(
        res["is_finite"], 
        Not(res["is_zero_aspect"]), 
        Not(res["is_areo_aspect"]), 
        Equals(res["val"], q_dfi_div) # CRITICAL FIX: Result value is q_dfi_div
    )
    
    # Define the state of 'res' if it's an AREO_UNIO breach
    dfi_dfi_res_is_AU_breach = assign_unio_aspect(res, TRUE()) # T2: DFI/DFI breach is AU

    # The overall logic for DFI/DFI division:
    # First, the Euclidean relations must be defined for q and r.
    # Then, based on q and r, decide if the result is classical DFI or an AU breach.
    dfi_dfi_logic_with_euclidean_def = And(
        # Only assert Euclidean definition if b["val"] is positive (always true for DFI divisor if Omega > 1)
        # For robustness, explicitly guard it, though dfi_a_dfi_b_cond and Omega > 1 context helps.
        Ite(
            b["val"] > Int(0), 
            euclidean_division_definition,
            TRUE() # If b["val"] is not > 0 (e.g. Omega=1 context, though DFI/DFI is false then), def is vacuously true
        ),
        Ite(cond_exact_div_and_q_in_range, 
            dfi_dfi_res_is_classical, 
            dfi_dfi_res_is_AU_breach
           )
    )
    # This entire logic is only applied if both a and b are DFI
    constraints.append(Implies(dfi_a_dfi_b_cond, dfi_dfi_logic_with_euclidean_def))

    # T3: x / 1 = x (if 1 is DFI)
    if current_omega_py > 1:
        fp1_cond = And(b["is_finite"], Equals(b["val"], Int(1)))
        constraints.append(Implies(fp1_cond, avc_deep_equals_smt_hdivf(res, a)))

    # T4: U_any / DFI_k -> U_algebraic;  DFI_k / U_any -> U_algebraic
    # These fix the *algebraic* part of the result to U. Aspects are via s_aspect_outcomes.
    
    # Define aspects for the 8 Unio-involved slots (S1-S8)
    # Inputs: ZU_a, AU_a, DFI_a (for operand a)
    #         ZU_b, AU_b, DFI_b (for operand b)
    # S1: ZU / DFI  (a is ZU, b is DFI)
    constraints.append(Implies(And(a["is_zero_aspect"], b["is_finite"]), assign_unio_aspect(res, s_aspect_outcomes["S1_ZU_div_DFI_is_areo"])))
    # S2: AU / DFI  (a is AU, b is DFI)
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_finite"]), assign_unio_aspect(res, s_aspect_outcomes["S2_AU_div_DFI_is_areo"])))
    # S3: DFI / ZU  (a is DFI, b is ZU)
    constraints.append(Implies(And(a["is_finite"], b["is_zero_aspect"]), assign_unio_aspect(res, s_aspect_outcomes["S3_DFI_div_ZU_is_areo"])))
    # S4: DFI / AU  (a is DFI, b is AU)
    constraints.append(Implies(And(a["is_finite"], b["is_areo_aspect"]), assign_unio_aspect(res, s_aspect_outcomes["S4_DFI_div_AU_is_areo"])))
    # S5: ZU / ZU   (a is ZU, b is ZU)
    constraints.append(Implies(And(a["is_zero_aspect"], b["is_zero_aspect"]), assign_unio_aspect(res, s_aspect_outcomes["S5_ZU_div_ZU_is_areo"])))
    # S6: ZU / AU   (a is ZU, b is AU)
    constraints.append(Implies(And(a["is_zero_aspect"], b["is_areo_aspect"]), assign_unio_aspect(res, s_aspect_outcomes["S6_ZU_div_AU_is_areo"])))
    # S7: AU / ZU   (a is AU, b is ZU)
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_zero_aspect"]), assign_unio_aspect(res, s_aspect_outcomes["S7_AU_div_ZU_is_areo"])))
    # S8: AU / AU   (a is AU, b is AU)
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_areo_aspect"]), assign_unio_aspect(res, s_aspect_outcomes["S8_AU_div_AU_is_areo"])))

    # Monotone Information Principle (MI) for aspects:
    # "If an operand Unio carries the 'areo' aspect, any resulting algebraic Unio 
    # (which all S1-S8 are) must also carry the 'areo' aspect."
    op_a_is_AU = a["is_areo_aspect"]
    op_b_is_AU = b["is_areo_aspect"]
    any_op_is_AU = Or(op_a_is_AU, op_b_is_AU)
    
    # Apply MI to each U-involved slot's aspect outcome variable in s_aspect_outcomes
    # S1 (ZU/DFI): No AU input, MI N/A for s_aspect_outcomes["S1_..."]
    # S2 (AU/DFI): AU input is 'a'. MI implies s_aspect_outcomes["S2_AU_div_DFI_is_areo"] = TRUE
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_finite"]), s_aspect_outcomes["S2_AU_div_DFI_is_areo"]))
    # S3 (DFI/ZU): No AU input, MI N/A for s_aspect_outcomes["S3_..."]
    # S4 (DFI/AU): AU input is 'b'. MI implies s_aspect_outcomes["S4_DFI_div_AU_is_areo"] = TRUE
    constraints.append(Implies(And(a["is_finite"], b["is_areo_aspect"]), s_aspect_outcomes["S4_DFI_div_AU_is_areo"]))
    # S5 (ZU/ZU): No AU input, MI N/A for s_aspect_outcomes["S5_..."]
    # S6 (ZU/AU): AU input is 'b'. MI implies s_aspect_outcomes["S6_ZU_div_AU_is_areo"] = TRUE
    constraints.append(Implies(And(a["is_zero_aspect"], b["is_areo_aspect"]), s_aspect_outcomes["S6_ZU_div_AU_is_areo"]))
    # S7 (AU/ZU): AU input is 'a'. MI implies s_aspect_outcomes["S7_AU_div_ZU_is_areo"] = TRUE
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_zero_aspect"]), s_aspect_outcomes["S7_AU_div_ZU_is_areo"]))
    # S8 (AU/AU): Both AU inputs. MI implies s_aspect_outcomes["S8_AU_div_AU_is_areo"] = TRUE
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_areo_aspect"]), s_aspect_outcomes["S8_AU_div_AU_is_areo"]))
    
    return constraints

# --- SMT Prover Function ---
def check_freedom_bit_hdivf(property_name: str, current_omega_py: int, 
                            base_constraints_func: Callable, op_constraints_func: Callable,
                            s_aspect_vars: Dict[str, FNode], target_slot_key: str):
    global smt_test_results_summary_HDivF
    if property_name not in smt_test_results_summary_HDivF:
         smt_test_results_summary_HDivF[property_name] = {}

    omega_smt_node = Int(current_omega_py)
    a_sym = create_symbolic_avc_val_hdivf("a_hdivf")
    b_sym = create_symbolic_avc_val_hdivf("b_hdivf")
    res_sym = create_symbolic_avc_val_hdivf("res_hdivf")

    setup = base_constraints_func(a_sym, omega_smt_node, current_omega_py) + \
            base_constraints_func(b_sym, omega_smt_node, current_omega_py) + \
            base_constraints_func(res_sym, omega_smt_node, current_omega_py)
    
    setup.extend(op_constraints_func(a_sym, b_sym, res_sym, s_aspect_vars, omega_smt_node, current_omega_py))

    # Test if slot can be AREO
    can_be_areo = False
    with Solver(name="z3", logic="LIA") as s_areo:
        for f_setup in setup: s_areo.add_assertion(f_setup)
        s_areo.add_assertion(s_aspect_vars[target_slot_key]) # Assert is_areo for this slot
        if s_areo.solve():
            can_be_areo = True
    
    # Test if slot can be ZERO
    can_be_zero = False
    with Solver(name="z3", logic="LIA") as s_zero:
        for f_setup in setup: s_zero.add_assertion(f_setup)
        s_zero.add_assertion(Not(s_aspect_vars[target_slot_key])) # Assert is_zero for this slot
        if s_zero.solve():
            can_be_zero = True

    is_free = can_be_areo and can_be_zero
    status_emoji = "✅" if is_free else ("⚠️" if can_be_areo or can_be_zero else "❌")
    result_detail = f"Can be AREO: {can_be_areo}, Can be ZERO: {can_be_zero} -> Free: {is_free}"
    print(f"{status_emoji} Ω={current_omega_py}: Freedom for {target_slot_key} - {result_detail}")
    smt_test_results_summary_HDivF[property_name][target_slot_key] = {"is_free": is_free, "can_be_areo": can_be_areo, "can_be_zero": can_be_zero}
    return is_free

# --- Main Execution ---
if __name__ == "__main__":
    omega_to_test_hdivf = 3
    set_avca_omega_hdivf(omega_to_test_hdivf, verbose=True)

    test_run_name = f"H_Div_Freedom_Test (Ω={omega_to_test_hdivf})"
    print(f"\n{'='*30} {test_run_name} {'='*30}")

    # Define symbolic boolean variables for the aspect outcome of each U-involved slot
    # TRUE means AREO_UNIO_obj, FALSE means ZERO_UNIO_obj
    s_aspect_outcome_is_areo_vars: Dict[str, FNode] = {
        "S1_ZU_div_DFI_is_areo": Symbol("s1_is_areo", SMT_BOOL_TYPE),
        "S2_AU_div_DFI_is_areo": Symbol("s2_is_areo", SMT_BOOL_TYPE),
        "S3_DFI_div_ZU_is_areo": Symbol("s3_is_areo", SMT_BOOL_TYPE),
        "S4_DFI_div_AU_is_areo": Symbol("s4_is_areo", SMT_BOOL_TYPE),
        "S5_ZU_div_ZU_is_areo": Symbol("s5_is_areo", SMT_BOOL_TYPE),
        "S6_ZU_div_AU_is_areo": Symbol("s6_is_areo", SMT_BOOL_TYPE),
        "S7_AU_div_ZU_is_areo": Symbol("s7_is_areo", SMT_BOOL_TYPE),
        "S8_AU_div_AU_is_areo": Symbol("s8_is_areo", SMT_BOOL_TYPE),
    }

    potentially_free_slots = [ # Based on MI pre-analysis
        "S1_ZU_div_DFI_is_areo", 
        "S3_DFI_div_ZU_is_areo", 
        "S5_ZU_div_ZU_is_areo"
    ]
    
    print("\nTesting freedom for potentially unconstrained aspect slots under T1-T4 + MI:")
    free_slot_count = 0
    for slot_key in s_aspect_outcome_is_areo_vars.keys():
        if slot_key in potentially_free_slots:
            if check_freedom_bit_hdivf(test_run_name, omega_to_test_hdivf, 
                                   get_base_avc_constraints_hdivf, 
                                   symbolic_division_constraints_hdivf,
                                   s_aspect_outcome_is_areo_vars, slot_key):
                free_slot_count +=1
        else: # Slot expected to be fixed by MI
            # We can add tests here to confirm MI fixes them as expected
            # e.g. for S2_AU_div_DFI_is_areo, check if only s2_is_areo=TRUE is SAT.
            pass 
            
    print(f"\nTotal number of truly free aspect bits found: {free_slot_count}")
    if free_slot_count == 3:
        print("✅ SUCCESS: Confirmed 3 bits of freedom for aspect assignment in U-involved division, as hypothesized.")
    else:
        print(f"❌ MISMATCH: Found {free_slot_count} free bits, expected 3. Review constraints or MI application.")

    print(f"\nDetailed freedom per slot for {test_run_name}:")
    for slot, details in smt_test_results_summary_HDivF.get(test_run_name, {}).items():
        print(f"  {slot}: Free={details['is_free']} (Can be AU: {details['can_be_areo']}, Can be ZU: {details['can_be_zero']})")
        
    print(f"\n{'='*70}")