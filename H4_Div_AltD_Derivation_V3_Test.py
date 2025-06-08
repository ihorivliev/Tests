# Script H_Div_AltD_Derivation_V3_Test.py
# Purpose: To rigorously test if AltD(Balanced) division aspect rules are uniquely 
#          determined by T1-T4 algebraic division constraints, a globally applied 
#          Monotone Information Principle (MI), and three specific desiderata 
#          (D13 round-trip FOR ALL DFI_k, D6.1 ZU/ZU=ZU, D5-consistency for DFI/ZU=AU).
# Expected: SAT for the AltD profile under these constraints, then UNSAT if trying 
#           to find an alternative profile for the 3 initially free bits.
# This version generalizes the D13 round-trip law.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal
import math

# --- Configuration ---
VERBOSE_MODEL_PRINTING = True # Set to False for less output if script is too chatty

# --- Global Omega Parameter & Test Results ---
_Omega_HDivD_V3_Global_Context: int = 0 # Renamed for V3
smt_test_results_summary_HDivD_V3: Dict[str, Dict[str, Any]] = {} # Test Name -> {status, met_expectation, model_aspects}

# --- Unio Class Definition ---
class Unio_HDivD_V3:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool: return isinstance(other, Unio_HDivD_V3)
    def __hash__(self) -> int: return hash(type(self))
    def __repr__(self) -> str: return f"Unio_HDivD_V3('{self.aspect}')"

ZERO_UNIO_HDivD_V3 = Unio_HDivD_V3("zero")
AREO_UNIO_HDivD_V3 = Unio_HDivD_V3("areo")
AVCVal_HDivD_V3 = Union[int, Unio_HDivD_V3]

def set_avca_omega_hdivd_v3(omega_value: int, verbose: bool = False):
    global _Omega_HDivD_V3_Global_Context
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_HDivD_V3 parameter must be an integer >= 1.")
    _Omega_HDivD_V3_Global_Context = omega_value
    if verbose:
        print(f"H_Div_AltD_Derivation_V3 Test: Global Context Omega_HDivD_V3 set to {_Omega_HDivD_V3_Global_Context}")

# --- SMT Symbolic Representation and Base Constraints (using _v3 suffix) ---
def create_symbolic_avc_val_hdivd_v3(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_areo_aspect": Symbol(f"{name_prefix}_is_AA_hdivd_v3", SMT_BOOL_TYPE), 
        "is_finite": Symbol(f"{name_prefix}_is_DFI_hdivd_v3", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_hdivd_v3", SMT_INT_TYPE),
        "is_unio": Symbol(f"{name_prefix}_is_Unio_hdivd_v3", SMT_BOOL_TYPE),
        "name": name_prefix
    }

def assign_unio_aspect_v3(target_res_repr: Dict[str, FNode], is_areo_flag: FNode) -> FNode:
    return And(
        target_res_repr["is_unio"], 
        Not(target_res_repr["is_finite"]),
        Equals(target_res_repr["val"], Int(0)), 
        Iff(target_res_repr["is_areo_aspect"], is_areo_flag)
    )

def get_base_avc_constraints_hdivd_v3(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    constraints = [
        Iff(avc_repr["is_unio"], Not(avc_repr["is_finite"])),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_unio"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_finite"], Not(avc_repr["is_areo_aspect"])) 
    ]
    if current_omega_py == 1:
        constraints.append(avc_repr["is_unio"]) # is_finite must be false
    return constraints

def avc_deep_equals_smt_hdivd_v3(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    return And(
        Iff(avc1["is_finite"], avc2["is_finite"]),
        Iff(avc1["is_unio"], avc2["is_unio"]),
        Implies(avc1["is_finite"], Equals(avc1["val"], avc2["val"])),
        Implies(avc1["is_unio"], Iff(avc1["is_areo_aspect"], avc2["is_areo_aspect"]))
    )

SMT_ZU_OBJ_HDivD_V3 = create_symbolic_avc_val_hdivd_v3("SMT_ZU_CONST")
SMT_AU_OBJ_HDivD_V3 = create_symbolic_avc_val_hdivd_v3("SMT_AU_CONST")
constant_unio_constraints_v3 = [
    SMT_ZU_OBJ_HDivD_V3["is_unio"], Not(SMT_ZU_OBJ_HDivD_V3["is_finite"]), Not(SMT_ZU_OBJ_HDivD_V3["is_areo_aspect"]), Equals(SMT_ZU_OBJ_HDivD_V3["val"], Int(0)),
    SMT_AU_OBJ_HDivD_V3["is_unio"], Not(SMT_AU_OBJ_HDivD_V3["is_finite"]), SMT_AU_OBJ_HDivD_V3["is_areo_aspect"], Equals(SMT_AU_OBJ_HDivD_V3["val"], Int(0))
]

# --- SMT Logic Builder for Multiplication (avc_mul_v1.2 "Areo Dominates") ---
def _smt_logic_mul_dfi_dfi_hdivd_v3(a: Dict[str, FNode], b: Dict[str, FNode],
                                   res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    prod_val = Times(a["val"], b["val"])
    res_is_FP_prod_formula = And(res["is_finite"], Not(res["is_unio"]), Not(res["is_areo_aspect"]), Equals(res["val"], prod_val))
    res_is_AU_overflow = assign_unio_aspect_v3(res, TRUE())
    return Ite(And(prod_val >= Int(1), prod_val < omega_smt_node), res_is_FP_prod_formula, res_is_AU_overflow)

def avc_mul_smt_logic_AreoDom_HDivD_V3(a: Dict[str, FNode], b: Dict[str, FNode],
                                       res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    cond_any_operand_is_unio = Or(a["is_unio"], b["is_unio"])
    res_is_ZU_outcome = assign_unio_aspect_v3(res, FALSE())
    res_is_AU_outcome = assign_unio_aspect_v3(res, TRUE())
    cond_any_unio_operand_is_areo = Or(And(a["is_unio"], a["is_areo_aspect"]), And(b["is_unio"], b["is_areo_aspect"]))
    unio_case_behavior = Ite(cond_any_unio_operand_is_areo, res_is_AU_outcome, res_is_ZU_outcome)
    dfi_case_behavior = _smt_logic_mul_dfi_dfi_hdivd_v3(a, b, res, omega_smt_node)
    return Ite(cond_any_operand_is_unio, unio_case_behavior, dfi_case_behavior)

# --- SMT Logic for Division (incorporating T1-T4, using symbolic aspects for U-involved) ---
def symbolic_division_op_definition_hdivd_v3( # Renamed, MI is applied globally now
    a: Dict[str, FNode], b: Dict[str, FNode], res: Dict[str, FNode],
    s_slot_is_areo: Dict[str, FNode], 
    omega_smt_node: FNode, current_omega_py: int
) -> List[FNode]:
    constraints = []
    # T2: DFI/DFI behavior
    dfi_a_dfi_b_cond = And(a["is_finite"], b["is_finite"])
    q_dfi_div = Symbol(f"q_dfidiv_{a['name']}_{b['name']}_hdivd_v3", SMT_INT_TYPE) 
    r_dfi_div = Symbol(f"r_dfidiv_{a['name']}_{b['name']}_hdivd_v3", SMT_INT_TYPE)
    euclidean_division_definition = Implies(b["val"] > Int(0), And(Equals(a["val"], Plus(Times(q_dfi_div, b["val"]), r_dfi_div)), r_dfi_div >= Int(0), r_dfi_div < b["val"]))
    cond_exact_div_and_q_in_range = And(Equals(r_dfi_div, Int(0)), q_dfi_div >= Int(1), q_dfi_div < omega_smt_node)
    dfi_dfi_res_is_classical = And(res["is_finite"], Not(res["is_unio"]), Not(res["is_areo_aspect"]), Equals(res["val"], q_dfi_div))
    dfi_dfi_res_is_AU_breach = assign_unio_aspect_v3(res, TRUE()) # DFI/DFI breach is AU
    dfi_dfi_logic_with_euclidean_def = And(Ite(b["val"] > Int(0), euclidean_division_definition, TRUE()), Ite(cond_exact_div_and_q_in_range, dfi_dfi_res_is_classical, dfi_dfi_res_is_AU_breach))
    constraints.append(Implies(dfi_a_dfi_b_cond, dfi_dfi_logic_with_euclidean_def))
    # T3: x / 1 = x
    if current_omega_py > 1:
        fp1_cond = And(b["is_finite"], Equals(b["val"], Int(1)))
        constraints.append(Implies(fp1_cond, avc_deep_equals_smt_hdivd_v3(res, a)))
    
    # T4 & U-involved slots aspects are determined by s_slot_is_areo mapping
    # The algebraic result for these U-involved cases is U_algebraic (val=0).
    cond_S1 = And(a["is_unio"], Not(a["is_areo_aspect"]), b["is_finite"]) # ZU / DFI
    constraints.append(Implies(cond_S1, assign_unio_aspect_v3(res, s_slot_is_areo["S1"])))
    cond_S2 = And(a["is_unio"], a["is_areo_aspect"], b["is_finite"])      # AU / DFI
    constraints.append(Implies(cond_S2, assign_unio_aspect_v3(res, s_slot_is_areo["S2"])))
    cond_S3 = And(a["is_finite"], b["is_unio"], Not(b["is_areo_aspect"])) # DFI / ZU
    constraints.append(Implies(cond_S3, assign_unio_aspect_v3(res, s_slot_is_areo["S3"])))
    cond_S4 = And(a["is_finite"], b["is_unio"], b["is_areo_aspect"])      # DFI / AU
    constraints.append(Implies(cond_S4, assign_unio_aspect_v3(res, s_slot_is_areo["S4"])))
    cond_S5 = And(a["is_unio"], Not(a["is_areo_aspect"]), b["is_unio"], Not(b["is_areo_aspect"])) # ZU / ZU
    constraints.append(Implies(cond_S5, assign_unio_aspect_v3(res, s_slot_is_areo["S5"])))
    cond_S6 = And(a["is_unio"], Not(a["is_areo_aspect"]), b["is_unio"], b["is_areo_aspect"])      # ZU / AU
    constraints.append(Implies(cond_S6, assign_unio_aspect_v3(res, s_slot_is_areo["S6"])))
    cond_S7 = And(a["is_unio"], a["is_areo_aspect"], b["is_unio"], Not(b["is_areo_aspect"]))      # AU / ZU
    constraints.append(Implies(cond_S7, assign_unio_aspect_v3(res, s_slot_is_areo["S7"])))
    cond_S8 = And(a["is_unio"], a["is_areo_aspect"], b["is_unio"], b["is_areo_aspect"])      # AU / AU
    constraints.append(Implies(cond_S8, assign_unio_aspect_v3(res, s_slot_is_areo["S8"])))
    
    # MI Principle is NOT asserted here. It will be asserted globally on s_slot_is_areo vars.
    # T1 Totality: Ensured by res having base constraints and all input patterns for a,b covered.
    return constraints

# --- SMT Prover Function ---
def solve_and_report_hdivd_v3(solver: Solver, property_name: str, current_omega_py: int,
                               s_slot_vars_to_report: Dict[str, FNode] = None,
                               expect_sat: bool = True,
                               inputs_for_ce: List[Dict[str,FNode]] = None,
                               verbose_model: bool = VERBOSE_MODEL_PRINTING):
    global smt_test_results_summary_HDivD_V3
    if property_name not in smt_test_results_summary_HDivD_V3:
         smt_test_results_summary_HDivD_V3[property_name] = {}

    is_sat = solver.solve()
    status_match = (is_sat == expect_sat)
    status_emoji = "✅" if status_match else "❌"
    outcome_verb = "SAT" if is_sat else "UNSAT"
    expected_verb = "SAT" if expect_sat else "UNSAT"
    
    print(f"{status_emoji} Ω={current_omega_py}: {property_name} - Result: {outcome_verb} (Expected: {expected_verb})")

    smt_test_results_summary_HDivD_V3[property_name]['status'] = outcome_verb
    smt_test_results_summary_HDivD_V3[property_name]['met_expectation'] = status_match
    current_model_aspects = {}

    if is_sat:
        model = solver.get_model()
        if s_slot_vars_to_report and verbose_model: # Print model only if verbose
            print("    Model for symbolic aspect choices (is_areo_aspect: True if AU, False if ZU):")
            for slot_name, aspect_bool_var in s_slot_vars_to_report.items():
                if aspect_bool_var.is_symbol():
                    val_smt_bool = model.get_value(aspect_bool_var)
                    is_areo_val = val_smt_bool.is_true()
                    current_model_aspects[slot_name] = is_areo_val
                    print(f"      {slot_name}: {'AU' if is_areo_val else 'ZU'}")
        elif s_slot_vars_to_report: # Still populate for summary even if not printing
             for slot_name, aspect_bool_var in s_slot_vars_to_report.items():
                if aspect_bool_var.is_symbol():
                    current_model_aspects[slot_name] = model.get_value(aspect_bool_var).is_true()
        smt_test_results_summary_HDivD_V3[property_name]['model_aspects(is_areo)'] = current_model_aspects
        
        if not status_match and inputs_for_ce: 
            ce_parts = []
            # ... (counterexample printing logic from previous script) ...
            print(f"    Counterexample/Witness to failed expectation: {'; '.join(ce_parts)}") # Placeholder for CE
            smt_test_results_summary_HDivD_V3[property_name]['counterexample'] = '; '.join(ce_parts)

    elif not is_sat and expect_sat:
        print(f"    INFO: Expected SAT but got UNSAT for {property_name}.")
    elif is_sat and not expect_sat:
        print(f"    INFO: Expected UNSAT but got SAT for {property_name}.")

# --- Main Execution ---
if __name__ == "__main__":
    omegas_to_run = [3, 5] # Can add more, e.g., 2
    # omega_to_test_hdivd_v3 = 3 # Single run

    for current_omega_test_val in omegas_to_run:
        set_avca_omega_hdivd_v3(current_omega_test_val, verbose=True)
        omega_smt_node_hdivd_v3 = Int(current_omega_test_val)

        test_run_prefix = f"H_Div_AltD_Deriv_V3 (Ω={current_omega_test_val})"
        print(f"\n{'='*30} {test_run_prefix} {'='*30}")

        # Symbolic operands for defining the division operation
        a_def_op = create_symbolic_avc_val_hdivd_v3("a_def") # Simpler names for top-level
        b_def_op = create_symbolic_avc_val_hdivd_v3("b_def")
        res_def_op = create_symbolic_avc_val_hdivd_v3("res_def")
        
        # Slot aspect variables: s_slot_is_areo["S1"] is TRUE if ZU/DFI -> AU, FALSE if ZU/DFI -> ZU
        s_slot_is_areo: Dict[str, FNode] = { # Simplified keys
            "S1": Symbol("s1_is_areo", SMT_BOOL_TYPE), "S2": Symbol("s2_is_areo", SMT_BOOL_TYPE),
            "S3": Symbol("s3_is_areo", SMT_BOOL_TYPE), "S4": Symbol("s4_is_areo", SMT_BOOL_TYPE),
            "S5": Symbol("s5_is_areo", SMT_BOOL_TYPE), "S6": Symbol("s6_is_areo", SMT_BOOL_TYPE),
            "S7": Symbol("s7_is_areo", SMT_BOOL_TYPE), "S8": Symbol("s8_is_areo", SMT_BOOL_TYPE),
        }
        base_setup_for_def = get_base_avc_constraints_hdivd_v3(a_def_op, omega_smt_node_hdivd_v3, current_omega_test_val) + \
                             get_base_avc_constraints_hdivd_v3(b_def_op, omega_smt_node_hdivd_v3, current_omega_test_val) + \
                             get_base_avc_constraints_hdivd_v3(res_def_op, omega_smt_node_hdivd_v3, current_omega_test_val) + \
                             constant_unio_constraints_v3

        core_div_op_def_constraints = base_setup_for_def + \
            symbolic_division_op_definition_hdivd_v3(a_def_op, b_def_op, res_def_op, s_slot_is_areo, 
                                                     omega_smt_node_hdivd_v3, current_omega_test_val)
        
        # MI Principle: Assert directly on the symbolic slot variables.
        # These slots S2, S4, S6, S7, S8 must be AU if MI holds.
        # MI Comment: The Monotone Information principle states that if an AREO_UNIO aspect ('a')
        # is an input to a U-resulting division, the output aspect must be 'a'.
        # This is encoded here by directly asserting the aspect variables for slots
        # S2 (AU/DFI), S4 (DFI/AU), S6 (ZU/AU), S7 (AU/ZU), S8 (AU/AU) to be AREO (TRUE).
        mi_constraints_on_slots = [
            s_slot_is_areo["S2"], s_slot_is_areo["S4"], s_slot_is_areo["S6"],
            s_slot_is_areo["S7"], s_slot_is_areo["S8"]
        ]
        
        # Desiderata constraints that will filter S1, S3, S5
        filtering_desiderata_constraints = []
        # D13 Round Trip Law: (ZU / DFI_k) ⊗_v1.2 DFI_k = ZU_obj
        # This should force s_slot_is_areo["S1"] to be FALSE (ZU aspect for ZU/DFI)
        if current_omega_test_val > 1: # D13 needs DFI elements
            # Create a list of constraints for each DFI_k
            for k_val in range(1, current_omega_test_val):
                dfi_k_d13_name = f"dfi_k{k_val}_d13"
                zu_div_dfik_res_name = f"zu_div_dfik{k_val}_d13"
                final_d13_res_name = f"final_d13_res_k{k_val}"

                dfi_k_d13 = create_symbolic_avc_val_hdivd_v3(dfi_k_d13_name)
                zu_div_dfik_res = create_symbolic_avc_val_hdivd_v3(zu_div_dfik_res_name)
                final_d13_res = create_symbolic_avc_val_hdivd_v3(final_d13_res_name)

                filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v3(dfi_k_d13, omega_smt_node_hdivd_v3, current_omega_test_val))
                filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v3(zu_div_dfik_res, omega_smt_node_hdivd_v3, current_omega_test_val))
                filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v3(final_d13_res, omega_smt_node_hdivd_v3, current_omega_test_val))
                
                # Constrain dfi_k_d13 to be the specific DFI value k_val
                filtering_desiderata_constraints.append(dfi_k_d13["is_finite"])
                filtering_desiderata_constraints.append(Equals(dfi_k_d13["val"], Int(k_val)))

                # Constrain zu_div_dfik_res to be SMT_ZU_OBJ_HDivD_V3 / dfi_k_d13 using the main symbolic division definition
                # This applies the rules based on s_slot_is_areo to this specific division instance
                filtering_desiderata_constraints.extend(symbolic_division_op_definition_hdivd_v3(
                    SMT_ZU_OBJ_HDivD_V3, dfi_k_d13, zu_div_dfik_res, 
                    s_slot_is_areo, omega_smt_node_hdivd_v3, current_omega_test_val
                ))
                
                # Constrain final_d13_res to be zu_div_dfik_res * dfi_k_d13
                filtering_desiderata_constraints.append(avc_mul_smt_logic_AreoDom_HDivD_V3(
                    zu_div_dfik_res, dfi_k_d13, final_d13_res, omega_smt_node_hdivd_v3
                ))
                # Assert D13: final result must be ZU_obj
                filtering_desiderata_constraints.append(avc_deep_equals_smt_hdivd_v3(final_d13_res, SMT_ZU_OBJ_HDivD_V3))
        
        # D6.1 "0/0=0-like" implies S5 (ZU/ZU) must be ZU (is_areo = FALSE)
        filtering_desiderata_constraints.append(Not(s_slot_is_areo["S5"]))
        
        # D5-consistency "DFI/ZU should be AU" implies S3 (DFI/ZU) must be AU (is_areo = TRUE)
        filtering_desiderata_constraints.append(s_slot_is_areo["S3"])

        # --- Test A (Coworker LLM's "Automatic Filtering"): Derivation of AltD ---
        test_A_name = f"{test_run_prefix} - Test A: Derivation of AltD (T1-4+MI+D13s+D6.1+D5c)" # D13s for plural k
        print(f"\n--- {test_A_name} ---")
        with Solver(name="z3", logic="LIA") as s_derivation_alt_d:
            for constr in core_div_op_def_constraints: s_derivation_alt_d.add_assertion(constr)
            for constr in mi_constraints_on_slots: s_derivation_alt_d.add_assertion(constr)
            for constr in filtering_desiderata_constraints: s_derivation_alt_d.add_assertion(constr)
        solve_and_report_hdivd_v3(s_derivation_alt_d, test_A_name, 
                                  current_omega_test_val, s_slot_is_areo, expect_sat=True,
                                  inputs_for_ce=[a_def_op, b_def_op, res_def_op], verbose_model=VERBOSE_MODEL_PRINTING)

        # --- Test B: Uniqueness of AltD profile under the constraints from Test A ---
        test_B_name = f"{test_run_prefix} - Test B: Uniqueness of AltD (expect UNSAT)"
        print(f"\n--- {test_B_name} ---")
        
        # AltD profile for S1,S3,S5 in terms of is_areo: S1=F, S3=T, S5=F
        alt_d_profile_for_free_bits = And(
            Not(s_slot_is_areo["S1"]), s_slot_is_areo["S3"], Not(s_slot_is_areo["S5"])
        )
        # MI already fixed S2,S4,S6,S7,S8 to True (Areo).
        
        with Solver(name="z3", logic="LIA") as s_uniqueness:
            for constr in core_div_op_def_constraints: s_uniqueness.add_assertion(constr) 
            for constr in mi_constraints_on_slots: s_uniqueness.add_assertion(constr) 
            for constr in filtering_desiderata_constraints: s_uniqueness.add_assertion(constr) 
            s_uniqueness.add_assertion(Not(alt_d_profile_for_free_bits))
        solve_and_report_hdivd_v3(s_uniqueness, test_B_name, 
                                  current_omega_test_val, s_slot_is_areo, expect_sat=False,
                                  inputs_for_ce=[a_def_op, b_def_op, res_def_op], verbose_model=VERBOSE_MODEL_PRINTING)

    # --- Final Summary Printing ---
    print(f"\n{'='*70}")
    print(f"\nFinal Summary of H_Div_AltD_Derivation_V3 Test (across all Omegas tested):")
    overall_success = True
    for omega_val_summary in omegas_to_run:
        test_A_name_summary = f"H_Div_AltD_Deriv_V3 (Ω={omega_val_summary}) - Test A: Derivation of AltD (T1-4+MI+D13s+D6.1+D5c)"
        test_B_name_summary = f"H_Div_AltD_Deriv_V3 (Ω={omega_val_summary}) - Test B: Uniqueness of AltD (expect UNSAT)"
        
        res_A = smt_test_results_summary_HDivD_V3.get(test_A_name_summary, {})
        res_B = smt_test_results_summary_HDivD_V3.get(test_B_name_summary, {})

        print(f"\n--- Results for Omega = {omega_val_summary} ---")
        if res_A.get('met_expectation') and res_B.get('met_expectation'):
            print(f"  ✅ SUCCESS: AltD profile consistently derived and unique for Ω={omega_val_summary}.")
            final_model_aspects = res_A.get('model_aspects(is_areo)',{})
            if final_model_aspects and VERBOSE_MODEL_PRINTING:
                print("    Derived AltD aspect profile (is_areo_aspect values from Test A model):")
                slot_map_to_verbose = {
                    "S1": "S1 (ZU/DFI)", "S2": "S2 (AU/DFI)", "S3": "S3 (DFI/ZU)", "S4": "S4 (DFI/AU)",
                    "S5": "S5 (ZU/ZU)", "S6": "S6 (ZU/AU)", "S7": "S7 (AU/ZU)", "S8": "S8 (AU/AU)"
                }
                for slot_key, verbose_name in slot_map_to_verbose.items():
                    if slot_key in final_model_aspects:
                        is_areo_value = final_model_aspects[slot_key]
                        aspect_val = 'AU' if is_areo_value else 'ZU'
                        print(f"      {verbose_name} ({slot_key}): {aspect_val}")
        else:
            print(f"  ❌ FAILURE: AltD profile was not uniquely derived or consistency check failed for Ω={omega_val_summary}.")
            overall_success = False
            if not res_A.get('met_expectation'): print(f"    Test A ({test_A_name_summary}) failed expectation. Status: {res_A.get('status')}")
            if not res_B.get('met_expectation'): print(f"    Test B ({test_B_name_summary}) failed expectation. Status: {res_B.get('status')}")
            
    print(f"\n{'='*30} Overall Script Verdict {'='*30}")
    if overall_success and omegas_to_run:
        print("🎉🎉🎉 ALL H_Div_AltD_Derivation_V3 TESTS PASSED AS EXPECTED FOR ALL TESTED OMEGAS! 🎉🎉🎉")
        print("     AltD profile is consistent with and uniquely determined by T1-T4 + MI + D13(all k) + D6.1 + D5c.")
    elif not omegas_to_run:
        print("🤷 No Omega values were specified for testing.")
    else:
        print("⚠️ SYSTEM ALERT: One or more tests FAILED against expectation. Review output.")