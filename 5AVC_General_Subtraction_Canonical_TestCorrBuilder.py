# Script Name: AVC_General_Subtraction_Canonical_TestCorr.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [1, 2, 3, 4, 5, 7, 12, 13]

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
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_sum = i1["val"] + i2["val"]
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])))))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]),
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]),
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_sum >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum))
                            )))
    return And(formulas)

# CORRECTED smart_raw_sub_canonical_logic_builder using nested ITEs
def smart_raw_sub_canonical_logic_builder(A_repr: Dict[str, Any], B_repr: Dict[str, Any],
                                          Res_repr: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    # Define result state setters
    # Result is ZS: is_zero=T, is_areo=F, is_finite=F
    res_is_ZS_true = Res_repr["is_zero"]
    res_is_AS_false_for_ZS = Not(Res_repr["is_areo"])
    res_is_Fp_false_for_ZS = Not(Res_repr["is_finite"])
    set_res_ZS = And(res_is_ZS_true, res_is_AS_false_for_ZS, res_is_Fp_false_for_ZS)

    # Result is AS: is_zero=F, is_areo=T, is_finite=F, val=Omega
    res_is_ZS_false_for_AS = Not(Res_repr["is_zero"])
    res_is_AS_true = Res_repr["is_areo"]
    res_is_Fp_false_for_AS = Not(Res_repr["is_finite"])
    res_val_is_Omega = Equals(Res_repr["val"], current_omega_smt)
    set_res_AS = And(res_is_ZS_false_for_AS, res_is_AS_true, res_is_Fp_false_for_AS, res_val_is_Omega)

    # Result is Fp(val_expr): is_zero=F, is_areo=F, is_finite=T, val=val_expr
    res_is_ZS_false_for_Fp = Not(Res_repr["is_zero"])
    res_is_AS_false_for_Fp = Not(Res_repr["is_areo"])
    res_is_Fp_true = Res_repr["is_finite"]
    def set_res_Fp(val_expr: FNode) -> FNode:
        return And(res_is_ZS_false_for_Fp, res_is_AS_false_for_Fp, res_is_Fp_true, Equals(Res_repr["val"], val_expr))

    # Axioms implemented with nested ITEs
    return Ite(A_repr["is_zero"],  # Minuend A is ZS_C
               Ite(B_repr["is_zero"], set_res_ZS,          # Axiom 1.1: ZS - ZS -> ZS
               Ite(B_repr["is_finite"], set_res_AS,      # Axiom 1.2: ZS - Fp -> AS
               # Else B must be AS_C (due to B's ExactlyOne constraint)
               set_res_ZS                               # Axiom 1.3: ZS - AS -> ZS
               )),
           Ite(A_repr["is_areo"],  # Minuend A is AS_C
               Ite(B_repr["is_zero"], set_res_ZS,          # Axiom 2.1 (Revised): AS - ZS -> ZS
               Ite(B_repr["is_finite"], set_res_AS,      # Axiom 2.2: AS - Fp -> AS
               # Else B must be AS_C
               set_res_ZS                               # Axiom 2.3: AS - AS -> ZS
               )),
           # Else Minuend A must be Fp_C(x)
               Ite(B_repr["is_zero"], set_res_Fp(A_repr["val"]),  # Axiom 3.1: Fp(x) - ZS -> Fp(x)
               Ite(B_repr["is_finite"],                         # Axiom 3.2: Fp(x) - Fp(y)
                   Ite(Equals(A_repr["val"], B_repr["val"]), set_res_ZS,          # 3.2.b: x = y -> ZS
                   Ite(A_repr["val"] > B_repr["val"], set_res_Fp(A_repr["val"] - B_repr["val"]), # 3.2.a: x > y -> Fp(x-y)
                                                      set_res_AS                  # 3.2.c: x < y -> AS
                   )),
               # Else B must be AS_C
               set_res_Fp(A_repr["val"])                        # Axiom 3.3: Fp(x) - AS -> Fp(x)
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
            printed_debug_info_ids = set()
            for var_item in model_vars_to_print:
                if isinstance(var_item, dict) and "name" in var_item :
                    val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                    is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                    is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode):
                    name_to_print = var_item.symbol_name() if var_item.is_symbol() else f"Expression({str(var_item)})"
                    value_str = "?"
                    try: value_str = str(solver.get_value(var_item))
                    except Exception: value_str = "(Error getting value)"
                    print(f"  {name_to_print}: {value_str}")

            if op_result_dicts_for_debug:
                print("  DEBUG Canonical Operation Results in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "name" in op_res_dict:
                        if id(op_res_dict) not in printed_debug_info_ids:
                            printed_debug_info_ids.add(id(op_res_dict))
                            val_str_node = f"V={solver.get_value(op_res_dict['val'])}" if op_res_dict['val'] in solver.get_model() else "V=?"
                            is_z_str_node = f"Z={solver.get_value(op_res_dict['is_zero'])}" if op_res_dict['is_zero'] in solver.get_model() else "Z=?"
                            is_a_str_node = f"A={solver.get_value(op_res_dict['is_areo'])}" if op_res_dict['is_areo'] in solver.get_model() else "A=?"
                            is_f_str_node = f"F={solver.get_value(op_res_dict['is_finite'])}" if op_res_dict['is_finite'] in solver.get_model() else "F=?"
                            print(f"    {op_res_dict['name']} (Canon_Res): {is_z_str_node}, {is_a_str_node}, {is_f_str_node}, {val_str_node}")
    solver.pop()
    print("-" * 70)
    return proved_universally

# --- Phase 4: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC General Subtraction Canonical Test (Corrected Logic) ======\n")

    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        s = Solver(name="z3")
        current_omega_smt = Int(omega_py_val)
        print(f"\n\n===== TESTING GENERAL SUBTRACTION WITH OMEGA = {omega_py_val} =====\n")

        A = create_intensity_representation(f"A_O{omega_py_val}")
        B = create_intensity_representation(f"B_O{omega_py_val}")
        C = create_intensity_representation(f"C_O{omega_py_val}")
        A1 = create_intensity_representation(f"A1_O{omega_py_val}")
        A2 = create_intensity_representation(f"A2_O{omega_py_val}")
        B1 = create_intensity_representation(f"B1_O{omega_py_val}")
        B2 = create_intensity_representation(f"B2_O{omega_py_val}")

        all_test_inputs = [A, B, C, A1, A2, B1, B2]
        current_inputs_base_constraints = []
        for inp_repr in all_test_inputs:
            current_inputs_base_constraints.append(inp_repr["constraints"])
            current_inputs_base_constraints.append(Implies(inp_repr["is_areo"], Equals(inp_repr["val"], current_omega_smt)))
            if omega_py_val > 1:
                current_inputs_base_constraints.append(Implies(inp_repr["is_finite"], inp_repr["val"] < current_omega_smt))
            else:
                 current_inputs_base_constraints.append(Not(inp_repr["is_finite"]))
        
        s.add_assertions(current_inputs_base_constraints)

        # --- GSUB-0: Well-Definedness of smart_raw_sub_canonical ---
        prem_gsub0 = And(avc_equiv_canonical(A1, A2), avc_equiv_canonical(B1, B2))
        res1_gsub0 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A1, B1, f"r1_gsub0_O{omega_py_val}", current_omega_smt)
        res2_gsub0 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A2, B2, f"r2_gsub0_O{omega_py_val}", current_omega_smt)
        conc_gsub0 = avc_equiv_canonical(res1_gsub0, res2_gsub0)
        gsub0_setup = [prem_gsub0,
                       res1_gsub0["constraints"], res1_gsub0["definition"],
                       res2_gsub0["constraints"], res2_gsub0["definition"]]
        prove_or_find_counterexample(s, f"GSUB-0 Well-Defined smart_raw_sub (Omega={omega_py_val})",
                                     gsub0_setup, conc_gsub0, [A1,A2,B1,B2,res1_gsub0,res2_gsub0], op_result_dicts_for_debug=[res1_gsub0,res2_gsub0])

        # --- GSUB-1: Zeroing Property: A - A ~ ZS_C ---
        ZS_C_target_repr = create_intensity_representation(f"ZS_C_target_O{omega_py_val}")
        # Add ZS_C_target_repr's constraints to the solver for this test's scope
        zs_target_setup_assertions = [ZS_C_target_repr["constraints"], ZS_C_target_repr["is_zero"]]
        if omega_py_val == 1: zs_target_setup_assertions.append(Not(ZS_C_target_repr["is_finite"]))
        # No need to constrain ZS_C_target_repr.val if it's ZS

        res_gsub1 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, A, f"r_gsub1_O{omega_py_val}", current_omega_smt)
        prop_gsub1 = avc_equiv_canonical(res_gsub1, ZS_C_target_repr)
        prove_or_find_counterexample(s, f"GSUB-1 A - A ~ ZS_C (Omega={omega_py_val})",
                                     zs_target_setup_assertions + [res_gsub1["constraints"], res_gsub1["definition"]],
                                     prop_gsub1, [A, res_gsub1, ZS_C_target_repr], op_result_dicts_for_debug=[res_gsub1])
        
        # --- GSUB-2: Right Identity of ZS_C: A - ZS_C ~ A ---
        ZS_B_repr = create_intensity_representation(f"ZS_B_O{omega_py_val}")
        zs_b_setup_assertions = [ZS_B_repr["constraints"], ZS_B_repr["is_zero"]]
        if omega_py_val == 1: zs_b_setup_assertions.append(Not(ZS_B_repr["is_finite"]))

        res_gsub2 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, ZS_B_repr, f"r_gsub2_O{omega_py_val}", current_omega_smt)
        prop_gsub2 = avc_equiv_canonical(res_gsub2, A)
        prove_or_find_counterexample(s, f"GSUB-2 A - ZS_C ~ A (Omega={omega_py_val})",
                                     zs_b_setup_assertions + [res_gsub2["constraints"], res_gsub2["definition"]],
                                     prop_gsub2, [A, ZS_B_repr, res_gsub2], op_result_dicts_for_debug=[res_gsub2])

        # --- GSUB-3: Interaction Fp_C(x) - AS_C ~ Fp_C(x) (Axiom 3.3 Verification) ---
        if omega_py_val > 1: 
            s.push()
            s.add_assertion(A["is_finite"]) 
            # A["val"] < current_omega_smt is already in current_inputs_base_constraints

            AS_B_repr = create_intensity_representation(f"AS_B_O{omega_py_val}")
            as_b_setup_assertions = [AS_B_repr["constraints"], AS_B_repr["is_areo"], Equals(AS_B_repr["val"], current_omega_smt)]
            if omega_py_val == 1: as_b_setup_assertions.append(Not(AS_B_repr["is_finite"])) # Should not happen if omega_py_val > 1
            s.add_assertions(as_b_setup_assertions)
            
            res_gsub3 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, AS_B_repr, f"r_gsub3_O{omega_py_val}", current_omega_smt)
            prop_gsub3 = avc_equiv_canonical(res_gsub3, A) 
            prove_or_find_counterexample(s, f"GSUB-3 Fp(x) - AS_C ~ Fp(x) (Omega={omega_py_val})",
                                         [res_gsub3["constraints"], res_gsub3["definition"]], # A and AS_B_repr constraints are on 's'
                                         prop_gsub3, [A, AS_B_repr, res_gsub3], op_result_dicts_for_debug=[res_gsub3])
            s.pop()

        # --- GSUB-4: Below-Zero-to-Areo (ZS_C - Fp_C ~ AS_C) (Axiom 1.2 Verification) ---
        if omega_py_val > 1:
            s.push()
            s.add_assertion(A["is_zero"]) 
            s.add_assertion(B["is_finite"]) 
            # B["val"] < current_omega_smt is already in current_inputs_base_constraints

            AS_target_repr = create_intensity_representation(f"AS_target_O{omega_py_val}")
            as_target_setup_assertions = [AS_target_repr["constraints"], AS_target_repr["is_areo"], Equals(AS_target_repr["val"], current_omega_smt)]
            if omega_py_val == 1: as_target_setup_assertions.append(Not(AS_target_repr["is_finite"]))
            s.add_assertions(as_target_setup_assertions)

            res_gsub4 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"r_gsub4_O{omega_py_val}", current_omega_smt)
            prop_gsub4 = avc_equiv_canonical(res_gsub4, AS_target_repr) 
            prove_or_find_counterexample(s, f"GSUB-4 ZS_C - Fp_C ~ AS_C (Omega={omega_py_val})",
                                         [res_gsub4["constraints"], res_gsub4["definition"]],
                                         prop_gsub4, [A, B, res_gsub4, AS_target_repr], op_result_dicts_for_debug=[res_gsub4])
            s.pop()

        # --- GSUB-5: Areo-Minus-Finite (AS_C - Fp_C ~ AS_C) (Axiom 2.2 Verification) ---
        if omega_py_val > 1:
            s.push()
            s.add_assertion(A["is_areo"]) 
            # Equals(A["val"], current_omega_smt) is already in current_inputs_base_constraints
            s.add_assertion(B["is_finite"]) 
            # B["val"] < current_omega_smt is already in current_inputs_base_constraints
            
            res_gsub5 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"r_gsub5_O{omega_py_val}", current_omega_smt)
            prop_gsub5 = avc_equiv_canonical(res_gsub5, A) 
            prove_or_find_counterexample(s, f"GSUB-5 AS_C - Fp_C ~ AS_C (Omega={omega_py_val})",
                                         [res_gsub5["constraints"], res_gsub5["definition"]],
                                         prop_gsub5, [A, B, res_gsub5], op_result_dicts_for_debug=[res_gsub5])
            s.pop()

        # --- GSUB-6: Additive Cancellation 1: (A + B)_smart - B_new ~ A ---
        sum_ab_gsub6 = define_op_canonical_result(smart_raw_add_logic_builder, A, B, f"sumAB_gsub6_O{omega_py_val}", current_omega_smt)
        res_sub_gsub6 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, sum_ab_gsub6, B, f"resSub_gsub6_O{omega_py_val}", current_omega_smt)
        prop_gsub6 = avc_equiv_canonical(res_sub_gsub6, A)
        gsub6_setup = [sum_ab_gsub6["constraints"], sum_ab_gsub6["definition"],
                       res_sub_gsub6["constraints"], res_sub_gsub6["definition"]]
        prove_or_find_counterexample(s, f"GSUB-6 (A+B)-B ~ A (Omega={omega_py_val})",
                                     gsub6_setup, prop_gsub6, [A, B, sum_ab_gsub6, res_sub_gsub6], op_result_dicts_for_debug=[sum_ab_gsub6, res_sub_gsub6])

        # --- GSUB-7: Additive Cancellation 2: (A - B)_new + B_smart ~ A ---
        sub_ab_gsub7 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"subAB_gsub7_O{omega_py_val}", current_omega_smt)
        res_add_gsub7 = define_op_canonical_result(smart_raw_add_logic_builder, sub_ab_gsub7, B, f"resAdd_gsub7_O{omega_py_val}", current_omega_smt)
        prop_gsub7 = avc_equiv_canonical(res_add_gsub7, A)
        gsub7_setup = [sub_ab_gsub7["constraints"], sub_ab_gsub7["definition"],
                       res_add_gsub7["constraints"], res_add_gsub7["definition"]]
        prove_or_find_counterexample(s, f"GSUB-7 (A-B)+B ~ A (Omega={omega_py_val})",
                                     gsub7_setup, prop_gsub7, [A, B, sub_ab_gsub7, res_add_gsub7], op_result_dicts_for_debug=[sub_ab_gsub7, res_add_gsub7])

        del s
        print("-" * 80)

    print("\n====== AVC General Subtraction Canonical Test (Corrected Logic) Complete ======")