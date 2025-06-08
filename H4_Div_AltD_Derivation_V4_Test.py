# Script H_Div_AltD_Derivation_V4_MI_Conditional_Test.py
# Purpose: To rigorously test if AltD(Balanced) division aspect rules are uniquely 
#          determined by T1-T4 algebraic division constraints, a conditionally applied 
#          Monotone Information Principle (MI) within the division definition, 
#          and three specific desiderata (D13 round-trip FOR ALL DFI_k, 
#          D6.1 ZU/ZU=ZU, D5-consistency for DFI/ZU=AU).
# Expected: SAT for the AltD profile under these constraints, then UNSAT if trying 
#           to find an alternative profile for the 3 initially free bits.
# This version uses a conditional MI encoded within the division logic,
# bolstered by witness constraints to ensure MI pattern coverage.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal
import math

# --- Configuration ---
VERBOSE_MODEL_PRINTING = True 

# --- Global Omega Parameter & Test Results ---
_Omega_HDivD_V4_Global_Context: int = 0
smt_test_results_summary_HDivD_V4: Dict[str, Dict[str, Any]] = {}

# --- Unio Class Definition ---
class Unio_HDivD_V4:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool: return isinstance(other, Unio_HDivD_V4)
    def __hash__(self) -> int: return hash(type(self))
    def __repr__(self) -> str: return f"Unio_HDivD_V4('{self.aspect}')"

ZERO_UNIO_HDivD_V4 = Unio_HDivD_V4("zero")
AREO_UNIO_HDivD_V4 = Unio_HDivD_V4("areo")
AVCVal_HDivD_V4 = Union[int, Unio_HDivD_V4]

def set_avca_omega_hdivd_v4(omega_value: int, verbose: bool = False):
    global _Omega_HDivD_V4_Global_Context
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_HDivD_V4 parameter must be an integer >= 1.")
    _Omega_HDivD_V4_Global_Context = omega_value
    if verbose:
        print(f"H_Div_AltD_Derivation_V4 Test: Global Context Omega_HDivD_V4 set to {_Omega_HDivD_V4_Global_Context}")

# --- SMT Symbolic Representation and Base Constraints (using _v4 suffix) ---
def create_symbolic_avc_val_hdivd_v4(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_areo_aspect": Symbol(f"{name_prefix}_is_AA_hdivd_v4", SMT_BOOL_TYPE), 
        "is_finite": Symbol(f"{name_prefix}_is_DFI_hdivd_v4", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_hdivd_v4", SMT_INT_TYPE),
        "is_unio": Symbol(f"{name_prefix}_is_Unio_hdivd_v4", SMT_BOOL_TYPE),
        "name": name_prefix
    }

def assign_unio_aspect_v4(target_res_repr: Dict[str, FNode], is_areo_flag: FNode) -> FNode:
    return And(
        target_res_repr["is_unio"], 
        Not(target_res_repr["is_finite"]),
        Equals(target_res_repr["val"], Int(0)), 
        Iff(target_res_repr["is_areo_aspect"], is_areo_flag)
    )

def get_base_avc_constraints_hdivd_v4(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    constraints = [
        Iff(avc_repr["is_unio"], Not(avc_repr["is_finite"])),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_unio"], Equals(avc_repr["val"], Int(0))),
        Implies(avc_repr["is_finite"], Not(avc_repr["is_areo_aspect"])) 
    ]
    if current_omega_py == 1:
        constraints.append(avc_repr["is_unio"]) 
    return constraints

def avc_deep_equals_smt_hdivd_v4(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    return And(
        Iff(avc1["is_finite"], avc2["is_finite"]),
        Iff(avc1["is_unio"], avc2["is_unio"]),
        Implies(avc1["is_finite"], Equals(avc1["val"], avc2["val"])),
        Implies(avc1["is_unio"], Iff(avc1["is_areo_aspect"], avc2["is_areo_aspect"]))
    )

SMT_ZU_OBJ_HDivD_V4 = create_symbolic_avc_val_hdivd_v4("SMT_ZU_CONST")
SMT_AU_OBJ_HDivD_V4 = create_symbolic_avc_val_hdivd_v4("SMT_AU_CONST")
constant_unio_constraints_v4 = [
    SMT_ZU_OBJ_HDivD_V4["is_unio"], Not(SMT_ZU_OBJ_HDivD_V4["is_finite"]), Not(SMT_ZU_OBJ_HDivD_V4["is_areo_aspect"]), Equals(SMT_ZU_OBJ_HDivD_V4["val"], Int(0)),
    SMT_AU_OBJ_HDivD_V4["is_unio"], Not(SMT_AU_OBJ_HDivD_V4["is_finite"]), SMT_AU_OBJ_HDivD_V4["is_areo_aspect"], Equals(SMT_AU_OBJ_HDivD_V4["val"], Int(0))
]

# --- SMT Logic Builder for Multiplication ---
def _smt_logic_mul_dfi_dfi_hdivd_v4(a: Dict[str, FNode], b: Dict[str, FNode],
                                   res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    prod_val = Times(a["val"], b["val"])
    res_is_FP_prod_formula = And(res["is_finite"], Not(res["is_unio"]), Not(res["is_areo_aspect"]), Equals(res["val"], prod_val))
    res_is_AU_overflow = assign_unio_aspect_v4(res, TRUE())
    return Ite(And(prod_val >= Int(1), prod_val < omega_smt_node), res_is_FP_prod_formula, res_is_AU_overflow)

def avc_mul_smt_logic_AreoDom_HDivD_V4(a: Dict[str, FNode], b: Dict[str, FNode],
                                    res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    cond_any_operand_is_unio = Or(a["is_unio"], b["is_unio"])
    res_is_ZU_outcome = assign_unio_aspect_v4(res, FALSE())
    res_is_AU_outcome = assign_unio_aspect_v4(res, TRUE())
    cond_any_unio_operand_is_areo = Or(And(a["is_unio"], a["is_areo_aspect"]), And(b["is_unio"], b["is_areo_aspect"]))
    unio_case_behavior = Ite(cond_any_unio_operand_is_areo, res_is_AU_outcome, res_is_ZU_outcome)
    dfi_case_behavior = _smt_logic_mul_dfi_dfi_hdivd_v4(a, b, res, omega_smt_node)
    return Ite(cond_any_operand_is_unio, unio_case_behavior, dfi_case_behavior)

# --- SMT Logic for Division with Conditional MI ---
def symbolic_division_op_definition_hdivd_v4( 
    a: Dict[str, FNode], b: Dict[str, FNode], res: Dict[str, FNode],
    s_slot_is_areo: Dict[str, FNode], 
    omega_smt_node: FNode, current_omega_py: int
) -> List[FNode]:
    constraints = []
    # T2: DFI/DFI behavior
    dfi_a_dfi_b_cond = And(a["is_finite"], b["is_finite"])
    q_dfi_div = Symbol(f"q_dfidiv_{a['name']}_{b['name']}_hdivd_v4", SMT_INT_TYPE) 
    r_dfi_div = Symbol(f"r_dfidiv_{a['name']}_{b['name']}_hdivd_v4", SMT_INT_TYPE)
    euclidean_division_definition = Implies(
        And(b["is_finite"],b["val"] > Int(0)), 
        And(
            Equals(a["val"], Plus(Times(q_dfi_div, b["val"]), r_dfi_div)), 
            r_dfi_div >= Int(0), 
            r_dfi_div < b["val"]
        )
    )
    cond_exact_div_and_q_in_range = And(
        b["val"] > Int(0), 
        Equals(r_dfi_div, Int(0)), 
        q_dfi_div >= Int(1), 
        q_dfi_div < omega_smt_node
    )
    dfi_dfi_res_is_classical = And(res["is_finite"], Not(res["is_unio"]), Not(res["is_areo_aspect"]), Equals(res["val"], q_dfi_div))
    dfi_dfi_res_is_AU_breach = assign_unio_aspect_v4(res, TRUE()) 
    
    dfi_dfi_logic_with_euclidean_def = And(
        Ite( And(a["is_finite"], b["is_finite"], b["val"] > Int(0)), 
             euclidean_division_definition, 
             TRUE() 
        ), 
        Ite(cond_exact_div_and_q_in_range, 
            dfi_dfi_res_is_classical, 
            dfi_dfi_res_is_AU_breach
        )
    )
    constraints.append(Implies(dfi_a_dfi_b_cond, dfi_dfi_logic_with_euclidean_def))
    
    # T3: x / 1 = x
    if current_omega_py > 1:
        fp1_cond = And(b["is_finite"], Equals(b["val"], Int(1)))
        constraints.append(Implies(fp1_cond, avc_deep_equals_smt_hdivd_v4(res, a)))
    
    # T4 & U-involved slots aspects determined by s_slot_is_areo
    cond_S1 = And(a["is_unio"], Not(a["is_areo_aspect"]), b["is_finite"]) # ZU / DFI
    constraints.append(Implies(cond_S1, assign_unio_aspect_v4(res, s_slot_is_areo["S1"])))
    cond_S2 = And(a["is_unio"], a["is_areo_aspect"], b["is_finite"])      # AU / DFI
    constraints.append(Implies(cond_S2, assign_unio_aspect_v4(res, s_slot_is_areo["S2"])))
    cond_S3 = And(a["is_finite"], b["is_unio"], Not(b["is_areo_aspect"])) # DFI / ZU
    constraints.append(Implies(cond_S3, assign_unio_aspect_v4(res, s_slot_is_areo["S3"])))
    cond_S4 = And(a["is_finite"], b["is_unio"], b["is_areo_aspect"])      # DFI / AU
    constraints.append(Implies(cond_S4, assign_unio_aspect_v4(res, s_slot_is_areo["S4"])))
    cond_S5 = And(a["is_unio"], Not(a["is_areo_aspect"]), b["is_unio"], Not(b["is_areo_aspect"])) # ZU / ZU
    constraints.append(Implies(cond_S5, assign_unio_aspect_v4(res, s_slot_is_areo["S5"])))
    cond_S6 = And(a["is_unio"], Not(a["is_areo_aspect"]), b["is_unio"], b["is_areo_aspect"])      # ZU / AU
    constraints.append(Implies(cond_S6, assign_unio_aspect_v4(res, s_slot_is_areo["S6"])))
    cond_S7 = And(a["is_unio"], a["is_areo_aspect"], b["is_unio"], Not(b["is_areo_aspect"]))      # AU / ZU
    constraints.append(Implies(cond_S7, assign_unio_aspect_v4(res, s_slot_is_areo["S7"])))
    cond_S8 = And(a["is_unio"], a["is_areo_aspect"], b["is_unio"], b["is_areo_aspect"])      # AU / AU
    constraints.append(Implies(cond_S8, assign_unio_aspect_v4(res, s_slot_is_areo["S8"])))
    
    # Conditional MI Principle:
    # If an input pattern (cond_SX) corresponding to an MI-sensitive slot occurs,
    # then the symbolic aspect choice for that slot (s_slot_is_areo["SX"]) must be TRUE (Areo).
    # These will be enforced by witness constraints ensuring cond_SX can be true.
    constraints.append(Implies(cond_S2, s_slot_is_areo["S2"]))
    constraints.append(Implies(cond_S4, s_slot_is_areo["S4"]))
    constraints.append(Implies(cond_S6, s_slot_is_areo["S6"]))
    constraints.append(Implies(cond_S7, s_slot_is_areo["S7"]))
    constraints.append(Implies(cond_S8, s_slot_is_areo["S8"]))
    
    return constraints

# --- SMT Prover Function (Completed) ---
def solve_and_report_hdivd_v4(solver: Solver, property_name: str, current_omega_py: int,
                                s_slot_vars_to_report: Dict[str, FNode] = None,
                                expect_sat: bool = True,
                                inputs_for_ce: List[Dict[str,FNode]] = None,
                                verbose_model_flag: bool = VERBOSE_MODEL_PRINTING):
    global smt_test_results_summary_HDivD_V4
    if property_name not in smt_test_results_summary_HDivD_V4:
        smt_test_results_summary_HDivD_V4[property_name] = {}

    is_sat = solver.solve()
    status_match = (is_sat == expect_sat)
    status_emoji = "✅" if status_match else "❌"
    outcome_verb = "SAT" if is_sat else "UNSAT"
    expected_verb = "SAT" if expect_sat else "UNSAT"
    
    print(f"{status_emoji} Ω={current_omega_py}: {property_name} - Result: {outcome_verb} (Expected: {expected_verb})")

    smt_test_results_summary_HDivD_V4[property_name]['status'] = outcome_verb
    smt_test_results_summary_HDivD_V4[property_name]['met_expectation'] = status_match
    current_model_aspects = {}

    if is_sat:
        model = solver.get_model()
        if s_slot_vars_to_report: 
            for slot_name, aspect_bool_var in s_slot_vars_to_report.items():
                if aspect_bool_var.is_symbol(): # Ensure it's a symbol we can get a value for
                    try:
                        smt_bool_val = model.get_value(aspect_bool_var)
                        current_model_aspects[slot_name] = smt_bool_val.is_true()
                    except Exception as e: # Should not happen if var is in problem
                        print(f"      Warning: Could not get model value for {slot_name}: {e}")
                        current_model_aspects[slot_name] = None # Or some other indicator
            smt_test_results_summary_HDivD_V4[property_name]['model_aspects(is_areo)'] = current_model_aspects
            
            if verbose_model_flag:
                print("      Model for symbolic aspect choices (is_areo_aspect: True if AU, False if ZU):")
                for slot_name_key in sorted(current_model_aspects.keys()):
                    is_areo_val = current_model_aspects[slot_name_key]
                    if is_areo_val is not None:
                         print(f"        {slot_name_key}: {'AU' if is_areo_val else 'ZU'}")
                    else:
                         print(f"        {slot_name_key}: UNKNOWN")
        
        if not status_match and inputs_for_ce: 
            ce_parts = []
            for repr_dict in inputs_for_ce:
                name = repr_dict['name']
                try:
                    is_a_val = model.get_value(repr_dict['is_areo_aspect'])
                    is_f_val = model.get_value(repr_dict['is_finite'])
                    val_smt_val = model.get_value(repr_dict['val'])
                    
                    is_a = is_a_val.is_true() if is_a_val is not None else None
                    is_f = is_f_val.is_true() if is_f_val is not None else None
                    
                    state_str = "?"
                    if is_f is True : state_str = f"Fp({val_smt_val})"
                    elif is_f is False: state_str = "AU" if is_a is True else ("ZU" if is_a is False else "Unio-AspectUnknown")
                    ce_parts.append(f"{name}={state_str}")
                except Exception: ce_parts.append(f"{name}=ERROR_IN_CE_PRINT")
            print(f"      Counterexample/Witness to failed expectation: {'; '.join(ce_parts)}")
            smt_test_results_summary_HDivD_V4[property_name]['counterexample'] = '; '.join(ce_parts)

    elif not is_sat and expect_sat:
        print(f"      INFO: Expected SAT but got UNSAT for {property_name}.")
    elif is_sat and not expect_sat:
        print(f"      INFO: Expected UNSAT but got SAT for {property_name}. Uniqueness claim may be false.")

# --- Main Execution ---
if __name__ == "__main__":
    omegas_to_run_v4 = [3] # Start with Omega=3 for V4, add 5 later if needed
    
    for current_omega_test_val in omegas_to_run_v4:
        set_avca_omega_hdivd_v4(current_omega_test_val, verbose=True)
        omega_smt_node_hdivd_v4 = Int(current_omega_test_val)

        test_run_prefix = f"H_Div_AltD_Deriv_V4_CondMI (Ω={current_omega_test_val})"
        print(f"\n{'='*30} {test_run_prefix} {'='*30}")

        a_def_op = create_symbolic_avc_val_hdivd_v4("a_def")
        b_def_op = create_symbolic_avc_val_hdivd_v4("b_def")
        res_def_op = create_symbolic_avc_val_hdivd_v4("res_def")
        
        s_slot_is_areo: Dict[str, FNode] = {
            "S1": Symbol("s1_is_areo_v4", SMT_BOOL_TYPE), "S2": Symbol("s2_is_areo_v4", SMT_BOOL_TYPE),
            "S3": Symbol("s3_is_areo_v4", SMT_BOOL_TYPE), "S4": Symbol("s4_is_areo_v4", SMT_BOOL_TYPE),
            "S5": Symbol("s5_is_areo_v4", SMT_BOOL_TYPE), "S6": Symbol("s6_is_areo_v4", SMT_BOOL_TYPE),
            "S7": Symbol("s7_is_areo_v4", SMT_BOOL_TYPE), "S8": Symbol("s8_is_areo_v4", SMT_BOOL_TYPE),
        }
        base_setup_for_def = get_base_avc_constraints_hdivd_v4(a_def_op, omega_smt_node_hdivd_v4, current_omega_test_val) + \
                             get_base_avc_constraints_hdivd_v4(b_def_op, omega_smt_node_hdivd_v4, current_omega_test_val) + \
                             get_base_avc_constraints_hdivd_v4(res_def_op, omega_smt_node_hdivd_v4, current_omega_test_val) + \
                             constant_unio_constraints_v4

        core_div_op_def_constraints = base_setup_for_def + \
            symbolic_division_op_definition_hdivd_v4(a_def_op, b_def_op, res_def_op, s_slot_is_areo, 
                                                     omega_smt_node_hdivd_v4, current_omega_test_val)
        
        filtering_desiderata_constraints = []
        # D13 Round Trip Law
        if current_omega_test_val > 1: 
            print(f"      INFO: Building D13 constraints for Ω={current_omega_test_val} (V4)...")
            for k_val_loop in range(1, current_omega_test_val):
                dfi_k_d13 = create_symbolic_avc_val_hdivd_v4(f"dfi_k{k_val_loop}_d13_v4")
                zu_div_dfik_res = create_symbolic_avc_val_hdivd_v4(f"zu_div_dfik{k_val_loop}_d13_v4")
                final_d13_res = create_symbolic_avc_val_hdivd_v4(f"final_d13_k{k_val_loop}_v4")

                filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v4(dfi_k_d13, omega_smt_node_hdivd_v4, current_omega_test_val))
                filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v4(zu_div_dfik_res, omega_smt_node_hdivd_v4, current_omega_test_val))
                filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v4(final_d13_res, omega_smt_node_hdivd_v4, current_omega_test_val))
                
                filtering_desiderata_constraints.append(dfi_k_d13["is_finite"])
                filtering_desiderata_constraints.append(Equals(dfi_k_d13["val"], Int(k_val_loop)))

                filtering_desiderata_constraints.extend(symbolic_division_op_definition_hdivd_v4(
                    SMT_ZU_OBJ_HDivD_V4, dfi_k_d13, zu_div_dfik_res, 
                    s_slot_is_areo, omega_smt_node_hdivd_v4, current_omega_test_val
                ))
                filtering_desiderata_constraints.append(avc_mul_smt_logic_AreoDom_HDivD_V4(
                    zu_div_dfik_res, dfi_k_d13, final_d13_res, omega_smt_node_hdivd_v4
                ))
                filtering_desiderata_constraints.append(avc_deep_equals_smt_hdivd_v4(final_d13_res, SMT_ZU_OBJ_HDivD_V4))
        
        filtering_desiderata_constraints.append(Not(s_slot_is_areo["S5"])) # D6.1
        filtering_desiderata_constraints.append(s_slot_is_areo["S3"])     # D5c

        # MI Witness Constraints (to make Conditional MI effective for these slots)
        print(f"      INFO: Building MI Witness constraints for Ω={current_omega_test_val} (V4)...")
        mi_witness_slots = { # slot_name: (operand_a_type, operand_b_type, fixed_b_val_if_dfi)
            "S2": (SMT_AU_OBJ_HDivD_V4, "DFI", 1), # AU / DFI(1)
            "S4": ("DFI", SMT_AU_OBJ_HDivD_V4, 1), # DFI(1) / AU
            "S6": (SMT_ZU_OBJ_HDivD_V4, SMT_AU_OBJ_HDivD_V4, None), # ZU / AU
            "S7": (SMT_AU_OBJ_HDivD_V4, SMT_ZU_OBJ_HDivD_V4, None), # AU / ZU
            "S8": (SMT_AU_OBJ_HDivD_V4, SMT_AU_OBJ_HDivD_V4, None)  # AU / AU
        }

        for slot_key, (a_type, b_type, b_val_fixed) in mi_witness_slots.items():
            if current_omega_test_val == 1 and ("DFI" in [a_type, b_type]): # DFI not possible if Omega=1
                print(f"        Skipping MI witness for {slot_key} as Ω=1 and DFI involved.")
                continue

            wit_a = create_symbolic_avc_val_hdivd_v4(f"wit_a_{slot_key}")
            wit_b = create_symbolic_avc_val_hdivd_v4(f"wit_b_{slot_key}")
            wit_res = create_symbolic_avc_val_hdivd_v4(f"wit_res_{slot_key}")

            filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v4(wit_a, omega_smt_node_hdivd_v4, current_omega_test_val))
            filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v4(wit_b, omega_smt_node_hdivd_v4, current_omega_test_val))
            filtering_desiderata_constraints.extend(get_base_avc_constraints_hdivd_v4(wit_res, omega_smt_node_hdivd_v4, current_omega_test_val))

            # Constrain witness operands
            if isinstance(a_type, dict): # It's SMT_AU_OBJ_HDivD_V4 or SMT_ZU_OBJ_HDivD_V4
                filtering_desiderata_constraints.append(avc_deep_equals_smt_hdivd_v4(wit_a, a_type))
            elif a_type == "DFI":
                filtering_desiderata_constraints.append(wit_a["is_finite"])
                filtering_desiderata_constraints.append(Equals(wit_a["val"], Int(1))) # Use DFI(1) as a canonical DFI for witness
            
            if isinstance(b_type, dict):
                filtering_desiderata_constraints.append(avc_deep_equals_smt_hdivd_v4(wit_b, b_type))
            elif b_type == "DFI":
                filtering_desiderata_constraints.append(wit_b["is_finite"])
                filtering_desiderata_constraints.append(Equals(wit_b["val"], Int(b_val_fixed if b_val_fixed else 1)))

            # Link to division definition (this will engage the conditional MI for this pattern)
            filtering_desiderata_constraints.extend(symbolic_division_op_definition_hdivd_v4(
                wit_a, wit_b, wit_res,
                s_slot_is_areo, omega_smt_node_hdivd_v4, current_omega_test_val
            ))
            # The result of the division wit_res is not directly constrained further for MI purposes here;
            # the goal is to make the cond_SX true so s_slot_is_areo[slot_key] is forced by conditional MI.

        # --- Test A: Derivation of AltD with Conditional MI ---
        test_A_name = f"{test_run_prefix} - Test A: Derivation (Conditional MI + Witnesses + D13s+D6.1+D5c)" # Updated name
        print(f"\n--- {test_A_name} ---")
        with Solver(name="z3", logic="LIA") as s_derivation_alt_d:
            for constr in core_div_op_def_constraints: s_derivation_alt_d.add_assertion(constr)
            # MI is now enforced via witnesses activating conditional MI within core_div_op_def_constraints
            for constr in filtering_desiderata_constraints: s_derivation_alt_d.add_assertion(constr)
            
            solve_and_report_hdivd_v4(s_derivation_alt_d, test_A_name, 
                                      current_omega_test_val, s_slot_is_areo, expect_sat=True,
                                      inputs_for_ce=[a_def_op, b_def_op, res_def_op], verbose_model_flag=VERBOSE_MODEL_PRINTING)

        # --- Test B: Uniqueness of AltD profile with Conditional MI ---
        test_B_name = f"{test_run_prefix} - Test B: Uniqueness (Conditional MI + Witnesses, expect UNSAT)" # Updated name
        print(f"\n--- {test_B_name} ---")
        
        alt_d_profile_for_free_bits = And( 
            Not(s_slot_is_areo["S1"]), s_slot_is_areo["S3"], Not(s_slot_is_areo["S5"])
        )
        
        with Solver(name="z3", logic="LIA") as s_uniqueness:
            for constr in core_div_op_def_constraints: s_uniqueness.add_assertion(constr) 
            for constr in filtering_desiderata_constraints: s_uniqueness.add_assertion(constr) 
            s_uniqueness.add_assertion(Not(alt_d_profile_for_free_bits))

            solve_and_report_hdivd_v4(s_uniqueness, test_B_name, 
                                      current_omega_test_val, s_slot_is_areo, expect_sat=False,
                                      inputs_for_ce=[a_def_op, b_def_op, res_def_op], verbose_model_flag=VERBOSE_MODEL_PRINTING)

    # --- Final Summary Printing (adapted for V4) ---
    print(f"\n{'='*70}")
    print(f"\nFinal Summary of H_Div_AltD_Derivation_V4 (Conditional MI + Witnesses) Test (across all Omegas tested):") # Updated name
    overall_success_v4 = True
    for omega_val_summary in omegas_to_run_v4:
        prefix = f"H_Div_AltD_Deriv_V4_CondMI (Ω={omega_val_summary})"
        test_A_name_summary = f"{prefix} - Test A: Derivation (Conditional MI + Witnesses + D13s+D6.1+D5c)" # Updated name
        test_B_name_summary = f"{prefix} - Test B: Uniqueness (Conditional MI + Witnesses, expect UNSAT)" # Updated name
        
        res_A = smt_test_results_summary_HDivD_V4.get(test_A_name_summary, {})
        res_B = smt_test_results_summary_HDivD_V4.get(test_B_name_summary, {})

        print(f"\n--- Results for Omega = {omega_val_summary} ---")
        current_omega_success = res_A.get('met_expectation', False) and res_B.get('met_expectation', False)
        if current_omega_success:
            print(f"  ✅ SUCCESS: AltD profile consistently derived and unique for Ω={omega_val_summary} using CONDITIONAL MI + Witnesses.")
            final_model_aspects = res_A.get('model_aspects(is_areo)',{})
            if final_model_aspects and VERBOSE_MODEL_PRINTING:
                print("      Derived AltD aspect profile (is_areo_aspect values from Test A model):")
                slot_map_to_verbose = {
                    "S1": "S1 (ZU/DFI)", "S2": "S2 (AU/DFI)", "S3": "S3 (DFI/ZU)", "S4": "S4 (DFI/AU)",
                    "S5": "S5 (ZU/ZU)", "S6": "S6 (ZU/AU)", "S7": "S7 (AU/ZU)", "S8": "S8 (AU/AU)"
                }
                for slot_key, verbose_name in sorted(slot_map_to_verbose.items()):
                    if slot_key in final_model_aspects:
                        is_areo_value = final_model_aspects[slot_key]
                        aspect_val = 'AU' if is_areo_value else 'ZU'
                        print(f"        {verbose_name} ({slot_key}): {aspect_val}")
            elif VERBOSE_MODEL_PRINTING:
                print("      Model aspects from Test A not available for printing (though test met expectation).")
        else:
            print(f"  ❌ FAILURE: AltD profile was not uniquely derived or consistency check failed for Ω={omega_val_summary} with CONDITIONAL MI + Witnesses.")
            overall_success_v4 = False
            if not res_A.get('met_expectation'): print(f"    Test A ({test_A_name_summary}) failed expectation. Status: {res_A.get('status')}")
            if not res_B.get('met_expectation'): print(f"    Test B ({test_B_name_summary}) failed expectation. Status: {res_B.get('status')}")
            
    print(f"\n{'='*30} Overall Script Verdict (V4 - Conditional MI + Witnesses) {'='*30}") # Updated name
    if not omegas_to_run_v4:
        print("🤷 No Omega values were specified for testing.")
    elif overall_success_v4:
        print("🎉🎉🎉 ALL H_Div_AltD_Derivation_V4 (Conditional MI + Witnesses) TESTS PASSED AS EXPECTED! 🎉🎉🎉")
        print("      AltD profile is consistent with and uniquely determined by T1-T4 + Conditional MI (with Witnesses) + D13(all k) + D6.1 + D5c.")
    else:
        print("⚠️ SYSTEM ALERT: One or more V4 tests FAILED against expectation. Review output.")