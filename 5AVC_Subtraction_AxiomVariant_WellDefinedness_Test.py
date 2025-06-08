# Script Name: AVC_Subtraction_AxiomVariant_WellDefinedness_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Requirement 4, Step 2 (Extended): Stress testing alternative subtraction axioms
OMEGA_VARIANTS_TO_TEST = [1, 2, 3, 5, 7] # A representative range

# --- Phase 1: Foundational Definitions (Canonical AVC) ---
def create_intensity_representation(name_prefix: str) -> Dict[str, Any]:
    is_zero = Symbol(f"{name_prefix}_is_zero", solver_BOOL_TYPE)
    is_areo = Symbol(f"{name_prefix}_is_areo", solver_BOOL_TYPE)
    is_finite = Symbol(f"{name_prefix}_is_finite", solver_BOOL_TYPE)
    val = Symbol(f"{name_prefix}_val", solver_INT_TYPE)
    constraint_exactly_one_state = ExactlyOne(is_zero, is_areo, is_finite)
    constraint_pos_nat_if_finite = Implies(is_finite, val > Int(0))
    all_constraints = And(constraint_exactly_one_state, constraint_pos_nat_if_finite)
    return {
        "is_zero": is_zero, "is_areo": is_areo, "is_finite": is_finite,
        "val": val, "constraints": all_constraints, "name": name_prefix
    }

def avc_equiv_canonical(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any]) -> FNode:
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"])
    finite_finite_equal_val = And(i1_repr["is_finite"],
                                  i2_repr["is_finite"],
                                  Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Phase 2: Canonical Raw Operations Definitions ---

# Helper to define result states for subtraction builders
def get_sub_result_setters(Res_repr: Dict[str, Any], current_omega_smt: FNode):
    res_is_ZS_true = Res_repr["is_zero"]
    res_is_AS_false_for_ZS = Not(Res_repr["is_areo"])
    res_is_Fp_false_for_ZS = Not(Res_repr["is_finite"])
    set_res_ZS = And(res_is_ZS_true, res_is_AS_false_for_ZS, res_is_Fp_false_for_ZS)

    res_is_ZS_false_for_AS = Not(Res_repr["is_zero"])
    res_is_AS_true = Res_repr["is_areo"]
    res_is_Fp_false_for_AS = Not(Res_repr["is_finite"])
    res_val_is_Omega = Equals(Res_repr["val"], current_omega_smt)
    set_res_AS = And(res_is_ZS_false_for_AS, res_is_AS_true, res_is_Fp_false_for_AS, res_val_is_Omega)

    res_is_ZS_false_for_Fp = Not(Res_repr["is_zero"])
    res_is_AS_false_for_Fp = Not(Res_repr["is_areo"])
    res_is_Fp_true = Res_repr["is_finite"]
    def set_res_Fp(val_expr: FNode) -> FNode:
        return And(res_is_ZS_false_for_Fp, res_is_AS_false_for_Fp, res_is_Fp_true, Equals(Res_repr["val"], val_expr))
    return set_res_ZS, set_res_AS, set_res_Fp

# Subtraction Logic Builder - VARIANT 1 (Fp_C(x) - AS_C -> ZS_C)
def smart_raw_sub_variant1_logic_builder(A_repr: Dict[str, Any], B_repr: Dict[str, Any],
                                         Res_repr: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    set_res_ZS, set_res_AS, set_res_Fp = get_sub_result_setters(Res_repr, current_omega_smt)
    
    return Ite(A_repr["is_zero"],  # Minuend A is ZS_C
               Ite(B_repr["is_zero"], set_res_ZS,          # Axiom 1.1: ZS - ZS -> ZS
               Ite(B_repr["is_finite"], set_res_AS,      # Axiom 1.2: ZS - Fp -> AS
               set_res_ZS                               # Axiom 1.3: ZS - AS -> ZS (ZS~AS, ZS-ZS=ZS)
               )),
           Ite(A_repr["is_areo"],  # Minuend A is AS_C
               Ite(B_repr["is_zero"], set_res_ZS,          # Axiom 2.1 (Revised): AS - ZS -> ZS
               Ite(B_repr["is_finite"], set_res_AS,      # Axiom 2.2: AS - Fp -> AS
               set_res_ZS                               # Axiom 2.3: AS - AS -> ZS
               )),
           # Else Minuend A must be Fp_C(x)
               Ite(B_repr["is_zero"], set_res_Fp(A_repr["val"]),  # Axiom 3.1: Fp(x) - ZS -> Fp(x)
               Ite(B_repr["is_finite"],                         # Axiom 3.2: Fp(x) - Fp(y)
                   Ite(Equals(A_repr["val"], B_repr["val"]), set_res_ZS,
                   Ite(A_repr["val"] > B_repr["val"], set_res_Fp(A_repr["val"] - B_repr["val"]),
                                                      set_res_AS
                   )),
               # Else B must be AS_C
               set_res_ZS                                       # VARIANT 1 for Axiom 3.3: Fp(x) - AS -> ZS_C
               ))
           ))

# Subtraction Logic Builder - VARIANT 2 (Fp_C(x) - AS_C -> AS_C)
def smart_raw_sub_variant2_logic_builder(A_repr: Dict[str, Any], B_repr: Dict[str, Any],
                                         Res_repr: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    set_res_ZS, set_res_AS, set_res_Fp = get_sub_result_setters(Res_repr, current_omega_smt)

    return Ite(A_repr["is_zero"],
               Ite(B_repr["is_zero"], set_res_ZS,
               Ite(B_repr["is_finite"], set_res_AS,
               set_res_ZS 
               )),
           Ite(A_repr["is_areo"],
               Ite(B_repr["is_zero"], set_res_ZS, 
               Ite(B_repr["is_finite"], set_res_AS,
               set_res_ZS
               )),
               Ite(B_repr["is_zero"], set_res_Fp(A_repr["val"]),
               Ite(B_repr["is_finite"],
                   Ite(Equals(A_repr["val"], B_repr["val"]), set_res_ZS,
                   Ite(A_repr["val"] > B_repr["val"], set_res_Fp(A_repr["val"] - B_repr["val"]),
                                                      set_res_AS
                   )),
               set_res_AS                                       # VARIANT 2 for Axiom 3.3: Fp(x) - AS -> AS_C
               ))
           ))

def define_op_canonical_result(op_logic_builder: Callable, i1_repr: Dict[str, Any], i2_repr: Dict[str, Any],
                               result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_smt)))
    return res_repr

# --- Phase 3: Generic Property Prover ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode],
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True,
                                 op_result_dicts_for_debug: List[Dict[str,Any]] = []):
    print(f"--- Testing Property: {property_name} ---")
    solver.push()
    for assertion in setup_assertions: solver.add_assertion(assertion)
    solver.add_assertion(Not(property_to_prove_true))
    proved_universally = False
    if not solver.solve():
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved_universally = True
    else:
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_fail:
            # (Debug printing logic omitted for brevity, assumed to be same as previous script)
            for var_item in model_vars_to_print:
                if isinstance(var_item, dict) and "name" in var_item :
                    val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                    is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                    is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode):
                     print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
    solver.pop()
    print("-" * 70)
    return proved_universally

# --- Phase 4: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Subtraction Axiom Variant Well-Definedness Test ======\n")

    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        if omega_py_val < 2: # Well-definedness tests for these variants are most meaningful when Fp can exist
            print(f"\n\n===== SKIPPING OMEGA = {omega_py_val} (Variants target Fp interactions) =====\n")
            continue

        current_omega_smt = Int(omega_py_val)
        
        # --- Test Variant 1: Fp(x) - AS_C -> ZS_C ---
        s_v1 = Solver(name="z3")
        print(f"\n\n===== SUBTRACTION VARIANT 1 (Fp-AS -> ZS) WITH OMEGA = {omega_py_val} =====\n")
        A1_v1 = create_intensity_representation(f"A1_V1_O{omega_py_val}")
        A2_v1 = create_intensity_representation(f"A2_V1_O{omega_py_val}")
        B1_v1 = create_intensity_representation(f"B1_V1_O{omega_py_val}")
        B2_v1 = create_intensity_representation(f"B2_V1_O{omega_py_val}")
        
        variant1_inputs = [A1_v1, A2_v1, B1_v1, B2_v1]
        variant1_base_constraints = []
        for inp_repr in variant1_inputs:
            variant1_base_constraints.append(inp_repr["constraints"])
            variant1_base_constraints.append(Implies(inp_repr["is_areo"], Equals(inp_repr["val"], current_omega_smt)))
            variant1_base_constraints.append(Implies(inp_repr["is_finite"], inp_repr["val"] < current_omega_smt))
        s_v1.add_assertions(variant1_base_constraints)

        prem_v1 = And(avc_equiv_canonical(A1_v1, A2_v1), avc_equiv_canonical(B1_v1, B2_v1))
        res1_v1 = define_op_canonical_result(smart_raw_sub_variant1_logic_builder, A1_v1, B1_v1, f"r1_v1_O{omega_py_val}", current_omega_smt)
        res2_v1 = define_op_canonical_result(smart_raw_sub_variant1_logic_builder, A2_v1, B2_v1, f"r2_v1_O{omega_py_val}", current_omega_smt)
        conc_v1 = avc_equiv_canonical(res1_v1, res2_v1)
        setup_v1 = [prem_v1, res1_v1["constraints"], res1_v1["definition"], res2_v1["constraints"], res2_v1["definition"]]
        prove_or_find_counterexample(s_v1, f"GSUB-0 Well-Defined Sub-Variant1 (Fp-AS->ZS) (Omega={omega_py_val})",
                                     setup_v1, conc_v1, [A1_v1,A2_v1,B1_v1,B2_v1,res1_v1,res2_v1])
        del s_v1

        # --- Test Variant 2: Fp(x) - AS_C -> AS_C ---
        s_v2 = Solver(name="z3")
        print(f"\n\n===== SUBTRACTION VARIANT 2 (Fp-AS -> AS) WITH OMEGA = {omega_py_val} =====\n")
        A1_v2 = create_intensity_representation(f"A1_V2_O{omega_py_val}")
        A2_v2 = create_intensity_representation(f"A2_V2_O{omega_py_val}")
        B1_v2 = create_intensity_representation(f"B1_V2_O{omega_py_val}")
        B2_v2 = create_intensity_representation(f"B2_V2_O{omega_py_val}")

        variant2_inputs = [A1_v2, A2_v2, B1_v2, B2_v2]
        variant2_base_constraints = []
        for inp_repr in variant2_inputs:
            variant2_base_constraints.append(inp_repr["constraints"])
            variant2_base_constraints.append(Implies(inp_repr["is_areo"], Equals(inp_repr["val"], current_omega_smt)))
            variant2_base_constraints.append(Implies(inp_repr["is_finite"], inp_repr["val"] < current_omega_smt))
        s_v2.add_assertions(variant2_base_constraints)

        prem_v2 = And(avc_equiv_canonical(A1_v2, A2_v2), avc_equiv_canonical(B1_v2, B2_v2))
        res1_v2 = define_op_canonical_result(smart_raw_sub_variant2_logic_builder, A1_v2, B1_v2, f"r1_v2_O{omega_py_val}", current_omega_smt)
        res2_v2 = define_op_canonical_result(smart_raw_sub_variant2_logic_builder, A2_v2, B2_v2, f"r2_v2_O{omega_py_val}", current_omega_smt)
        conc_v2 = avc_equiv_canonical(res1_v2, res2_v2)
        setup_v2 = [prem_v2, res1_v2["constraints"], res1_v2["definition"], res2_v2["constraints"], res2_v2["definition"]]
        prove_or_find_counterexample(s_v2, f"GSUB-0 Well-Defined Sub-Variant2 (Fp-AS->AS) (Omega={omega_py_val})",
                                     setup_v2, conc_v2, [A1_v2,A2_v2,B1_v2,B2_v2,res1_v2,res2_v2])
        del s_v2
        print("-" * 80)

    print("\n====== AVC Subtraction Axiom Variant Well-Definedness Test Complete ======")