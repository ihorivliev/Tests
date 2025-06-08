# Script H_Div_AltD_Derivation_Test.py
# Purpose: To test if AltD(Balanced) division aspect rules are uniquely determined by
#          T1-T4 algebraic division constraints, Monotone Information Principle (MI),
#          and three specific desiderata (D13 round-trip, D6.1 ZU/ZU=ZU, D5-consistency for DFI/ZU=AU).
# Expected: SAT for the AltD profile, then UNSAT if trying to find an alternative profile
#           under these specific constraints.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies,
                             ExactlyOne, Ite, Solver, TRUE, FALSE, Iff, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal
import math

# --- Global Omega Parameter & Test Results ---
_Omega_HDivD_Global_Context: int = 0
smt_test_results_summary_HDivD: Dict[str, Dict[str, Any]] = {} # Test Name -> {status, met_expectation, model_aspects}

# --- Unio Class Definition ---
class Unio_HDivD:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool: return isinstance(other, Unio_HDivD)
    def __hash__(self) -> int: return hash(type(self))
    def __repr__(self) -> str: return f"Unio_HDivD('{self.aspect}')"

ZERO_UNIO_HDivD = Unio_HDivD("zero")
AREO_UNIO_HDivD = Unio_HDivD("areo")
AVCVal_HDivD = Union[int, Unio_HDivD]

def set_avca_omega_hdivd(omega_value: int, verbose: bool = False):
    global _Omega_HDivD_Global_Context
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_HDivD parameter must be an integer >= 1.")
    _Omega_HDivD_Global_Context = omega_value
    if verbose:
        print(f"H_Div_AltD_Derivation Test: Global Context Omega_HDivD set to {_Omega_HDivD_Global_Context}")

# --- SMT Symbolic Representation and Base Constraints ---
def create_symbolic_avc_val_hdivd(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_ZA_hdivd", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_AA_hdivd", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_DFI_hdivd", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_hdivd", SMT_INT_TYPE),
        "name": name_prefix
    }

def assign_unio_aspect(target_res_repr: Dict[str, FNode], is_areo_flag: FNode) -> FNode:
    return And(
        Not(target_res_repr["is_finite"]),
        Equals(target_res_repr["val"], Int(0)),
        Iff(target_res_repr["is_areo_aspect"], is_areo_flag),
        Iff(target_res_repr["is_zero_aspect"], Not(is_areo_flag))
    )

def get_base_avc_constraints_hdivd(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(Or(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"]), Equals(avc_repr["val"], Int(0)))
    ]
    if current_omega_py == 1:
        constraints.append(Not(avc_repr["is_finite"]))
    return constraints

def avc_deep_equals_smt_hdivd(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode: # For specific object check
    return And(
        Iff(avc1["is_zero_aspect"], avc2["is_zero_aspect"]),
        Iff(avc1["is_areo_aspect"], avc2["is_areo_aspect"]),
        Iff(avc1["is_finite"], avc2["is_finite"]),
        Implies(avc1["is_finite"], Equals(avc1["val"], avc2["val"]))
    )

SMT_ZU_OBJ_HDivD = create_symbolic_avc_val_hdivd("SMT_ZU_CONST")
SMT_AU_OBJ_HDivD = create_symbolic_avc_val_hdivd("SMT_AU_CONST")
constant_unio_constraints = [
    SMT_ZU_OBJ_HDivD["is_zero_aspect"], Not(SMT_ZU_OBJ_HDivD["is_areo_aspect"]), Not(SMT_ZU_OBJ_HDivD["is_finite"]), Equals(SMT_ZU_OBJ_HDivD["val"], Int(0)),
    Not(SMT_AU_OBJ_HDivD["is_zero_aspect"]), SMT_AU_OBJ_HDivD["is_areo_aspect"], Not(SMT_AU_OBJ_HDivD["is_finite"]), Equals(SMT_AU_OBJ_HDivD["val"], Int(0))
]


def _smt_logic_mul_dfi_dfi_hdivd(a: Dict[str, FNode], b: Dict[str, FNode],
                                res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    prod_val = Times(a["val"], b["val"])
    res_is_FP_prod_formula = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), Equals(res["val"], prod_val))
    res_is_AU_overflow = assign_unio_aspect(res, TRUE()) # DFI mult overflow yields AU_obj
    return Ite(And(prod_val >= Int(1), prod_val < omega_smt_node), res_is_FP_prod_formula, res_is_AU_overflow)

def avc_mul_smt_logic_AreoDom_HDivD(a: Dict[str, FNode], b: Dict[str, FNode],
                                    res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])
    cond_any_operand_is_unio = Or(a_is_unio, b_is_unio)
    res_is_ZU_outcome = assign_unio_aspect(res, FALSE())
    res_is_AU_outcome = assign_unio_aspect(res, TRUE())
    cond_any_unio_operand_is_areo = Or(a["is_areo_aspect"], b["is_areo_aspect"])
    unio_case_behavior = Ite(cond_any_unio_operand_is_areo, res_is_AU_outcome, res_is_ZU_outcome)
    dfi_case_behavior = _smt_logic_mul_dfi_dfi_hdivd(a, b, res, omega_smt_node)
    return Ite(cond_any_operand_is_unio, unio_case_behavior, dfi_case_behavior)

def symbolic_division_constraints_hdivd_core(
    a: Dict[str, FNode], b: Dict[str, FNode], res: Dict[str, FNode],
    s_aspect_outcomes_is_areo: Dict[str, FNode],
    omega_smt_node: FNode, current_omega_py: int
) -> List[FNode]:
    constraints = []
    # T2: DFI/DFI behavior
    dfi_a_dfi_b_cond = And(a["is_finite"], b["is_finite"])
    q_dfi_div = Symbol(f"q_dfidiv_{a['name']}_{b['name']}_hdivd_core", SMT_INT_TYPE)
    r_dfi_div = Symbol(f"r_dfidiv_{a['name']}_{b['name']}_hdivd_core", SMT_INT_TYPE)
    euclidean_division_definition = Implies(b["val"] > Int(0), And(Equals(a["val"], Plus(Times(q_dfi_div, b["val"]), r_dfi_div)), r_dfi_div >= Int(0), r_dfi_div < b["val"]))
    cond_exact_div_and_q_in_range = And(Equals(r_dfi_div, Int(0)), q_dfi_div >= Int(1), q_dfi_div < omega_smt_node)
    dfi_dfi_res_is_classical = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]), Equals(res["val"], q_dfi_div))
    dfi_dfi_res_is_AU_breach = assign_unio_aspect(res, TRUE())
    dfi_dfi_logic_with_euclidean_def = And(Ite(b["val"] > Int(0),euclidean_division_definition, TRUE()), Ite(cond_exact_div_and_q_in_range, dfi_dfi_res_is_classical, dfi_dfi_res_is_AU_breach))
    constraints.append(Implies(dfi_a_dfi_b_cond, dfi_dfi_logic_with_euclidean_def))
    # T3: x / 1 = x
    if current_omega_py > 1:
        fp1_cond = And(b["is_finite"], Equals(b["val"], Int(1)))
        constraints.append(Implies(fp1_cond, avc_deep_equals_smt_hdivd(res, a)))
    # T4 & U-involved slots aspects
    constraints.append(Implies(And(a["is_zero_aspect"], b["is_finite"]), assign_unio_aspect(res, s_aspect_outcomes_is_areo["S1_ZU_div_DFI"])))
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_finite"]), assign_unio_aspect(res, s_aspect_outcomes_is_areo["S2_AU_div_DFI"])))
    constraints.append(Implies(And(a["is_finite"], b["is_zero_aspect"]), assign_unio_aspect(res, s_aspect_outcomes_is_areo["S3_DFI_div_ZU"])))
    constraints.append(Implies(And(a["is_finite"], b["is_areo_aspect"]), assign_unio_aspect(res, s_aspect_outcomes_is_areo["S4_DFI_div_AU"])))
    constraints.append(Implies(And(a["is_zero_aspect"], b["is_zero_aspect"]), assign_unio_aspect(res, s_aspect_outcomes_is_areo["S5_ZU_div_ZU"])))
    constraints.append(Implies(And(a["is_zero_aspect"], b["is_areo_aspect"]), assign_unio_aspect(res, s_aspect_outcomes_is_areo["S6_ZU_div_AU"])))
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_zero_aspect"]), assign_unio_aspect(res, s_aspect_outcomes_is_areo["S7_AU_div_ZU"])))
    constraints.append(Implies(And(a["is_areo_aspect"], b["is_areo_aspect"]), assign_unio_aspect(res, s_aspect_outcomes_is_areo["S8_AU_div_AU"])))
    # MI Principle
    constraints.append(Implies(a["is_areo_aspect"], s_aspect_outcomes_is_areo["S2_AU_div_DFI"]))
    constraints.append(Implies(b["is_areo_aspect"], s_aspect_outcomes_is_areo["S4_DFI_div_AU"]))
    constraints.append(Implies(b["is_areo_aspect"], s_aspect_outcomes_is_areo["S6_ZU_div_AU"]))
    constraints.append(Implies(a["is_areo_aspect"], s_aspect_outcomes_is_areo["S7_AU_div_ZU"]))
    constraints.append(Implies(Or(a["is_areo_aspect"], b["is_areo_aspect"]), s_aspect_outcomes_is_areo["S8_AU_div_AU"]))
    return constraints

# --- SMT Prover Function ---
def solve_and_report_hdivd(solver: Solver, property_name: str, current_omega_py: int,
                            s_aspect_vars_to_report: Dict[str, FNode] = None, # Renamed for clarity
                            expect_sat: bool = True):
    global smt_test_results_summary_HDivD # Ensure global is accessible

    # Initialize the entry for this property_name if it doesn't exist
    if property_name not in smt_test_results_summary_HDivD:
        smt_test_results_summary_HDivD[property_name] = {} # Initialize as a dict

    is_sat = solver.solve()
    status_match = (is_sat == expect_sat)
    status_emoji = "✅" if status_match else "❌"
    outcome_verb = "SAT" if is_sat else "UNSAT"
    expected_verb = "SAT" if expect_sat else "UNSAT"

    print(f"{status_emoji} Ω={current_omega_py}: {property_name} - Result: {outcome_verb} (Expected: {expected_verb})")

    # Store basic status
    smt_test_results_summary_HDivD[property_name]['status'] = outcome_verb
    smt_test_results_summary_HDivD[property_name]['met_expectation'] = status_match
    smt_test_results_summary_HDivD[property_name]['model_aspects(is_areo)'] = {} # Initialize model aspects

    if is_sat and s_aspect_vars_to_report:
        model = solver.get_model()
        current_model_aspects = {}
        print("     Model for relevant symbolic aspect choices (True if AREO, False if ZERO):")
        for var_name, var_node in s_aspect_vars_to_report.items():
            # Only try to get value if var_node is a valid SMT symbol in the model
            if var_node.is_symbol(): # Or check if var_node in model, though get_value handles it
                val_smt_bool = model.get_value(var_node)
                is_areo_val = val_smt_bool.is_true() # Get Python bool
                current_model_aspects[var_name] = is_areo_val
                # Print all for Test 1b, otherwise only the S1,S3,S5 for focused Test 1 output
                if property_name.endswith("Test 1b: Filtered for AltD") or \
                   property_name.endswith("Test 1: T1-T4+MI+AltD_choices") or \
                   ("S1_" in var_name or "S3_" in var_name or "S5_" in var_name):
                    print(f"       {var_name}: {'AU' if is_areo_val else 'ZU'}")
            else:
                print(f"       Skipping {var_name} as it's not a direct symbol in s_aspect_vars_to_report for model extraction.")
        smt_test_results_summary_HDivD[property_name]['model_aspects(is_areo)'] = current_model_aspects

    elif not is_sat and expect_sat:
        print(f"     ERROR: Expected SAT but got UNSAT. Constraints may be too strong or contradictory for {property_name}.")
        # core = solver.get_unsat_core() # Optional: can be slow
        # print(f"     Unsat Core (sample): {list(core)[:5]}")
    elif is_sat and not expect_sat:
        print(f"     ERROR: Expected UNSAT but got SAT. Uniqueness test failed or property failed unexpectedly for {property_name}.")

# --- Main Execution ---
if __name__ == "__main__":
    omega_to_test_hdivd = 3
    set_avca_omega_hdivd(omega_to_test_hdivd, verbose=True)
    omega_smt_node_hdivd = Int(omega_to_test_hdivd)

    test_run_prefix = f"H_Div_AltD_Deriv (Ω={omega_to_test_hdivd})"
    print(f"\n{'='*30} {test_run_prefix} {'='*30}")

    # Symbolic operands for division a / b -> res (ensure these are fresh for each test context if needed)
    a_op_main = create_symbolic_avc_val_hdivd("a_op_main_t1")
    b_op_main = create_symbolic_avc_val_hdivd("b_op_main_t1")
    res_op_main = create_symbolic_avc_val_hdivd("res_op_main_t1")

    # Symbolic boolean variables for Test 1
    s_aspect_is_areo_vars_test1: Dict[str, FNode] = {
        "S1_ZU_div_DFI": Symbol("s1_t1_is_areo", SMT_BOOL_TYPE),
        "S2_AU_div_DFI": Symbol("s2_t1_is_areo", SMT_BOOL_TYPE),
        "S3_DFI_div_ZU": Symbol("s3_t1_is_areo", SMT_BOOL_TYPE),
        "S4_DFI_div_AU": Symbol("s4_t1_is_areo", SMT_BOOL_TYPE),
        "S5_ZU_div_ZU": Symbol("s5_t1_is_areo", SMT_BOOL_TYPE),
        "S6_ZU_div_AU": Symbol("s6_t1_is_areo", SMT_BOOL_TYPE),
        "S7_AU_div_ZU": Symbol("s7_t1_is_areo", SMT_BOOL_TYPE),
        "S8_AU_div_AU": Symbol("s8_t1_is_areo", SMT_BOOL_TYPE),
    }
    base_setup_main = get_base_avc_constraints_hdivd(a_op_main, omega_smt_node_hdivd, omega_to_test_hdivd) + \
                      get_base_avc_constraints_hdivd(b_op_main, omega_smt_node_hdivd, omega_to_test_hdivd) + \
                      get_base_avc_constraints_hdivd(res_op_main, omega_smt_node_hdivd, omega_to_test_hdivd) + \
                      constant_unio_constraints

    core_div_constraints_main = base_setup_main + \
        symbolic_division_constraints_hdivd_core(a_op_main, b_op_main, res_op_main, s_aspect_is_areo_vars_test1,
                                                 omega_smt_node_hdivd, omega_to_test_hdivd)

    # --- Test 1: Check consistency of T1-T4 + MI + AltD explicit choices for S1, S3, S5 ---
    print("\n--- Test 1: Consistency of T1-T4 + MI + AltD explicit choices for S1, S3, S5 ---")
    alt_d_explicit_choices = [
        Not(s_aspect_is_areo_vars_test1["S1_ZU_div_DFI"]),
        s_aspect_is_areo_vars_test1["S3_DFI_div_ZU"],
        Not(s_aspect_is_areo_vars_test1["S5_ZU_div_ZU"])
    ]

    with Solver(name="z3", logic="LIA") as s_alt_d_consistency:
        for constr in core_div_constraints_main: s_alt_d_consistency.add_assertion(constr)
        for constr in alt_d_explicit_choices: s_alt_d_consistency.add_assertion(constr)

        # --- BEGIN SIMPLIFIED DEBUG BLOCK ---
        print(f"\nDEBUGGING s_alt_d_consistency for Test 1:")
        print(f"  Type of solver object: {type(s_alt_d_consistency)}")
        print(f"  Type name of solver: {type(s_alt_d_consistency).__name__}")
        # print(f"  Attributes: {dir(s_alt_d_consistency)}") # Can be very verbose, uncomment if needed
        if hasattr(s_alt_d_consistency, 'z3'):
            # Accessing .z3 directly might be problematic if it's a complex object.
            # Let's just confirm its presence and type for now.
            print(f"  s_alt_d_consistency.z3 exists. Type of .z3: {type(getattr(s_alt_d_consistency, 'z3')).__name__}")
        else:
            print(f"  CRITICAL: s_alt_d_consistency.z3 attribute is MISSING before solve!")
        # --- END SIMPLIFIED DEBUG BLOCK ---

        solve_and_report_hdivd(s_alt_d_consistency, f"{test_run_prefix} - Test 1: T1-T4+MI+AltD_choices",
                               omega_to_test_hdivd, s_aspect_is_areo_vars_test1, expect_sat=True)


    # --- Test 1b: Check consistency of T1-T4 + MI + D13 (implies S1=ZU) + D6.1(S5=ZU) + D5c(S3=AU) ---
    print("\n--- Test 1b: Consistency & Model for T1-T4 + MI + D13(S1=ZU) + D6.1(S5=ZU) + D5c(S3=AU) ---")

    s_aspect_is_areo_vars_test1b: Dict[str, FNode] = {
        "S1_ZU_div_DFI": Symbol("s1_t1b_is_areo", SMT_BOOL_TYPE),
        "S2_AU_div_DFI": Symbol("s2_t1b_is_areo", SMT_BOOL_TYPE),
        "S3_DFI_div_ZU": Symbol("s3_t1b_is_areo", SMT_BOOL_TYPE),
        "S4_DFI_div_AU": Symbol("s4_t1b_is_areo", SMT_BOOL_TYPE),
        "S5_ZU_div_ZU": Symbol("s5_t1b_is_areo", SMT_BOOL_TYPE),
        "S6_ZU_div_AU": Symbol("s6_t1b_is_areo", SMT_BOOL_TYPE),
        "S7_AU_div_ZU": Symbol("s7_t1b_is_areo", SMT_BOOL_TYPE),
        "S8_AU_div_AU": Symbol("s8_t1b_is_areo", SMT_BOOL_TYPE),
    }

    a_op_1b = create_symbolic_avc_val_hdivd("a_op_1b"); b_op_1b = create_symbolic_avc_val_hdivd("b_op_1b"); res_op_1b = create_symbolic_avc_val_hdivd("res_op_1b")
    base_setup_1b = get_base_avc_constraints_hdivd(a_op_1b, omega_smt_node_hdivd, omega_to_test_hdivd) + \
                    get_base_avc_constraints_hdivd(b_op_1b, omega_smt_node_hdivd, omega_to_test_hdivd) + \
                    get_base_avc_constraints_hdivd(res_op_1b, omega_smt_node_hdivd, omega_to_test_hdivd) + \
                    constant_unio_constraints

    current_core_div_constraints_test1b = base_setup_1b + \
        symbolic_division_constraints_hdivd_core(a_op_1b, b_op_1b, res_op_1b, s_aspect_is_areo_vars_test1b,
                                                 omega_smt_node_hdivd, omega_to_test_hdivd)

    filtering_constraints_1b = []
    if omega_to_test_hdivd > 1:
        dfi_k_d13_1b = create_symbolic_avc_val_hdivd("dfi_k_d13_1b")
        zu_div_dfik_res_1b = create_symbolic_avc_val_hdivd("zu_div_dfik_1b")
        final_d13_res_1b = create_symbolic_avc_val_hdivd("final_d13_res_1b")

        filtering_constraints_1b += get_base_avc_constraints_hdivd(dfi_k_d13_1b, omega_smt_node_hdivd, omega_to_test_hdivd)
        filtering_constraints_1b.append(dfi_k_d13_1b["is_finite"])
        if omega_to_test_hdivd > 1:
            filtering_constraints_1b.append(Equals(dfi_k_d13_1b["val"], Int(1)))

        filtering_constraints_1b += get_base_avc_constraints_hdivd(zu_div_dfik_res_1b, omega_smt_node_hdivd, omega_to_test_hdivd)
        filtering_constraints_1b.extend(symbolic_division_constraints_hdivd_core(
            SMT_ZU_OBJ_HDivD, dfi_k_d13_1b, zu_div_dfik_res_1b,
            s_aspect_is_areo_vars_test1b, omega_smt_node_hdivd, omega_to_test_hdivd
        ))

        filtering_constraints_1b += get_base_avc_constraints_hdivd(final_d13_res_1b, omega_smt_node_hdivd, omega_to_test_hdivd)
        filtering_constraints_1b.append(avc_mul_smt_logic_AreoDom_HDivD(zu_div_dfik_res_1b, dfi_k_d13_1b, final_d13_res_1b, omega_smt_node_hdivd))
        filtering_constraints_1b.append(avc_deep_equals_smt_hdivd(final_d13_res_1b, SMT_ZU_OBJ_HDivD))

    filtering_constraints_1b.append(Not(s_aspect_is_areo_vars_test1b["S5_ZU_div_ZU"]))
    filtering_constraints_1b.append(s_aspect_is_areo_vars_test1b["S3_DFI_div_ZU"])

    with Solver(name="z3", logic="LIA") as s_filtered_alt_d:
        for constr in current_core_div_constraints_test1b: s_filtered_alt_d.add_assertion(constr)
        for constr in filtering_constraints_1b: s_filtered_alt_d.add_assertion(constr)

        # You might want to add a similar debug block here for s_filtered_alt_d if Test 1b also fails
        # print(f"\nDEBUGGING s_filtered_alt_d for Test 1b:")
        # print(f"  Type name: {type(s_filtered_alt_d).__name__}, Has .z3: {hasattr(s_filtered_alt_d, 'z3')}")


        solve_and_report_hdivd(s_filtered_alt_d, f"{test_run_prefix} - Test 1b: Filtered for AltD (T1-4+MI+D13+D6.1+D5c)",
                               omega_to_test_hdivd, s_aspect_is_areo_vars_test1b, expect_sat=True)

    # --- Test 2: Uniqueness of AltD profile under the constraints from Test 1b ---
    print("\n--- Test 2: Uniqueness of AltD profile under T1-T4 + MI + D13(S1) + D6.1(S5) + D5c(S3) ---")

    not_alt_d_profile_for_free_bits = Or(
        s_aspect_is_areo_vars_test1b["S1_ZU_div_DFI"],
        Not(s_aspect_is_areo_vars_test1b["S3_DFI_div_ZU"]),
        s_aspect_is_areo_vars_test1b["S5_ZU_div_ZU"]
    )

    with Solver(name="z3", logic="LIA") as s_uniqueness:
        for constr in current_core_div_constraints_test1b: s_uniqueness.add_assertion(constr)
        for constr in filtering_constraints_1b: s_uniqueness.add_assertion(constr)
        s_uniqueness.add_assertion(not_alt_d_profile_for_free_bits)


        # You might want to add a similar debug block here for s_uniqueness if Test 2 also fails
        # print(f"\nDEBUGGING s_uniqueness for Test 2:")
        # print(f"  Type name: {type(s_uniqueness).__name__}, Has .z3: {hasattr(s_uniqueness, 'z3')}")

        solve_and_report_hdivd(s_uniqueness, f"{test_run_prefix} - Test 2: Uniqueness (expect UNSAT if AltD is unique)",
                               omega_to_test_hdivd, s_aspect_is_areo_vars_test1b, expect_sat=False)

    # --- Final Summary Printing ---
    print(f"\n{'='*70}")
    print("\nFinal Summary of H_Div_AltD_Derivation Test:")
    test1b_name = f"{test_run_prefix} - Test 1b: Filtered for AltD (T1-4+MI+D13+D6.1+D5c)"
    test2_name = f"{test_run_prefix} - Test 2: Uniqueness (expect UNSAT if AltD is unique)"
    # Ensure test1_name matches the actual name used in solve_and_report_hdivd for Test 1
    test1_name = f"{test_run_prefix} - Test 1: T1-T4+MI+AltD_choices"


    test1_results = smt_test_results_summary_HDivD.get(test1_name, {})
    test1b_results = smt_test_results_summary_HDivD.get(test1b_name, {})
    test2_results = smt_test_results_summary_HDivD.get(test2_name, {})

    # Check Test 1 success for the overall message
    if test1_results.get('met_expectation') and \
       test1b_results.get('met_expectation') and \
       test2_results.get('met_expectation'):
        print("✅ SUCCESS: AltD profile is consistent with and uniquely determined by T1-T4+MI+D13(implies S1=ZU)+D6.1(S5=ZU)+D5c(S3=AU).")
        final_model_aspects = test1b_results.get('model_aspects(is_areo)',{})
        if final_model_aspects:
            print("  Derived AltD aspect profile (is_areo_aspect values from Test 1b model for relevant symbolic aspect variables):")
            slot_map_to_verbose = {
                "S1_ZU_div_DFI": "S1 (ZU/DFI)", "S2_AU_div_DFI": "S2 (AU/DFI)",
                "S3_DFI_div_ZU": "S3 (DFI/ZU)", "S4_DFI_div_AU": "S4 (DFI/AU)",
                "S5_ZU_div_ZU": "S5 (ZU/ZU)", "S6_ZU_div_AU": "S6 (ZU/AU)",
                "S7_AU_div_ZU": "S7 (AU/ZU)", "S8_AU_div_AU": "S8 (AU/AU)"
            }
            # This part of summary printing needs to correctly map keys from s_aspect_is_areo_vars_test1b
            # The current model aspects stored are keyed by the actual symbol names ("s1_t1b_is_areo", etc.)
            # It might be better to iterate s_aspect_is_areo_vars_test1b and use model.get_value(var_node) here
            # OR ensure final_model_aspects uses the "S1_ZU_div_DFI" style keys.
            # The current code in solve_and_report_hdivd stores them by the keys of s_aspect_vars_to_report.

            # To correctly print from Test 1b model:
            # We need the s_aspect_is_areo_vars_test1b dictionary's structure.
            # The model stored in smt_test_results_summary_HDivD already used these keys.
            for key_name, verbose_name in slot_map_to_verbose.items():
                if key_name in final_model_aspects: # final_model_aspects is from Test 1b
                    is_areo_value = final_model_aspects[key_name]
                    aspect_val = 'AU' if is_areo_value else 'ZU'
                    # The symbolic variable name from test1b was like "s1_t1b_is_areo"
                    # The key in s_aspect_is_areo_vars_test1b is "S1_ZU_div_DFI"
                    # The value in current_model_aspects IS keyed by "S1_ZU_div_DFI", etc.
                    # So this loop should work as intended if final_model_aspects is correct.
                    print(f"    {verbose_name}: {aspect_val}")
                else:
                    print(f"    {verbose_name}: Not found in Test 1b model (check keys in s_aspect_is_areo_vars_test1b).")

        else:
            print("     Model aspects from Test 1b not available for printing (Test 1b might have been UNSAT or model not requested).")
    else:
        print("❌ FAILURE: AltD profile was not uniquely derived or a consistency check failed. Review SMT output and debug info.")
        if not test1_results.get('met_expectation'):
            print(f"    Details for Test 1 ({test1_name}): Status={test1_results.get('status')}, Met Expectation: {test1_results.get('met_expectation')}")
        if not test1b_results.get('met_expectation'):
            print(f"    Details for Test 1b ({test1b_name}): Status={test1b_results.get('status')}, Met Expectation: {test1b_results.get('met_expectation')}")
        if not test2_results.get('met_expectation'):
            print(f"    Details for Test 2 ({test2_name}): Status={test2_results.get('status')}, Met Expectation: {test2_results.get('met_expectation')}")