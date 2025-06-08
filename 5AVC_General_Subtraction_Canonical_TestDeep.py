# Script Name: AVC_General_Subtraction_Canonical_TestDeep.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Requirement 4, Step 2 (Extended): Axiomatization and Verification of General Subtraction
OMEGA_VARIANTS_TO_TEST = [1, 2, 3, 4, 5, 7, 12, 13] # Consistent with OmegaSweep

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

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"]
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]),
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]),
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]),
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_prod >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
    return And(formulas)

# Corrected smart_raw_sub_canonical_logic_builder using nested ITEs
def smart_raw_sub_canonical_logic_builder(A_repr: Dict[str, Any], B_repr: Dict[str, Any],
                                          Res_repr: Dict[str, Any], current_omega_smt: FNode) -> FNode:
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
               set_res_Fp(A_repr["val"])
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
    print("====== AVC General Subtraction Canonical Test (Deep) ======\n")

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

        # --- GSUB-0 to GSUB-5 (Core Axiom Verifications - from previous script, confirmed PROVED) ---
        # For brevity, assuming these pass based on previous corrected run. If any failed, it means the new logic builder has issues.
        # It's good practice to re-run them here.

        # GSUB-0: Well-Definedness
        prem_gsub0 = And(avc_equiv_canonical(A1, A2), avc_equiv_canonical(B1, B2))
        res1_gsub0 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A1, B1, f"r1_gsub0_O{omega_py_val}", current_omega_smt)
        res2_gsub0 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A2, B2, f"r2_gsub0_O{omega_py_val}", current_omega_smt)
        conc_gsub0 = avc_equiv_canonical(res1_gsub0, res2_gsub0)
        gsub0_setup = [prem_gsub0, res1_gsub0["constraints"], res1_gsub0["definition"], res2_gsub0["constraints"], res2_gsub0["definition"]]
        prove_or_find_counterexample(s, f"GSUB-0 Well-Defined smart_raw_sub (Omega={omega_py_val})", gsub0_setup, conc_gsub0, [A1,A2,B1,B2,res1_gsub0,res2_gsub0], op_result_dicts_for_debug=[res1_gsub0,res2_gsub0])

        # GSUB-1: A - A ~ ZS_C
        ZS_C_target_repr_gs1 = create_intensity_representation(f"ZS_C_gs1_O{omega_py_val}")
        zs_target_setup_gs1 = [ZS_C_target_repr_gs1["constraints"], ZS_C_target_repr_gs1["is_zero"]]
        if omega_py_val == 1: zs_target_setup_gs1.append(Not(ZS_C_target_repr_gs1["is_finite"]))
        res_gsub1 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, A, f"r_gsub1_O{omega_py_val}", current_omega_smt)
        prop_gsub1 = avc_equiv_canonical(res_gsub1, ZS_C_target_repr_gs1)
        prove_or_find_counterexample(s, f"GSUB-1 A - A ~ ZS_C (Omega={omega_py_val})", zs_target_setup_gs1 + [res_gsub1["constraints"], res_gsub1["definition"]], prop_gsub1, [A, res_gsub1, ZS_C_target_repr_gs1], op_result_dicts_for_debug=[res_gsub1])
        
        # GSUB-2: A - ZS_C ~ A
        ZS_B_repr_gs2 = create_intensity_representation(f"ZS_B_gs2_O{omega_py_val}")
        zs_b_setup_gs2 = [ZS_B_repr_gs2["constraints"], ZS_B_repr_gs2["is_zero"]]
        if omega_py_val == 1: zs_b_setup_gs2.append(Not(ZS_B_repr_gs2["is_finite"]))
        res_gsub2 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, ZS_B_repr_gs2, f"r_gsub2_O{omega_py_val}", current_omega_smt)
        prop_gsub2 = avc_equiv_canonical(res_gsub2, A)
        prove_or_find_counterexample(s, f"GSUB-2 A - ZS_C ~ A (Omega={omega_py_val})", zs_b_setup_gs2 + [res_gsub2["constraints"], res_gsub2["definition"]], prop_gsub2, [A, ZS_B_repr_gs2, res_gsub2], op_result_dicts_for_debug=[res_gsub2])

        if omega_py_val > 1:
            # GSUB-3: Fp(x) - AS_C ~ Fp(x)
            s.push()
            s.add_assertion(A["is_finite"])
            AS_B_repr_gs3 = create_intensity_representation(f"AS_B_gs3_O{omega_py_val}")
            as_b_setup_gs3 = [AS_B_repr_gs3["constraints"], AS_B_repr_gs3["is_areo"], Equals(AS_B_repr_gs3["val"], current_omega_smt)]
            s.add_assertions(as_b_setup_gs3)
            res_gsub3 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, AS_B_repr_gs3, f"r_gsub3_O{omega_py_val}", current_omega_smt)
            prop_gsub3 = avc_equiv_canonical(res_gsub3, A)
            prove_or_find_counterexample(s, f"GSUB-3 Fp(x) - AS_C ~ Fp(x) (Omega={omega_py_val})", [res_gsub3["constraints"], res_gsub3["definition"]], prop_gsub3, [A, AS_B_repr_gs3, res_gsub3], op_result_dicts_for_debug=[res_gsub3])
            s.pop()

            # GSUB-4: ZS_C - Fp_C ~ AS_C
            s.push()
            s.add_assertion(A["is_zero"])
            s.add_assertion(B["is_finite"])
            AS_target_repr_gs4 = create_intensity_representation(f"AS_target_gs4_O{omega_py_val}")
            as_target_setup_gs4 = [AS_target_repr_gs4["constraints"], AS_target_repr_gs4["is_areo"], Equals(AS_target_repr_gs4["val"], current_omega_smt)]
            s.add_assertions(as_target_setup_gs4)
            res_gsub4 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"r_gsub4_O{omega_py_val}", current_omega_smt)
            prop_gsub4 = avc_equiv_canonical(res_gsub4, AS_target_repr_gs4)
            prove_or_find_counterexample(s, f"GSUB-4 ZS_C - Fp_C ~ AS_C (Omega={omega_py_val})", [res_gsub4["constraints"], res_gsub4["definition"]], prop_gsub4, [A, B, res_gsub4, AS_target_repr_gs4], op_result_dicts_for_debug=[res_gsub4])
            s.pop()

            # GSUB-5: AS_C - Fp_C ~ AS_C
            s.push()
            s.add_assertion(A["is_areo"])
            s.add_assertion(B["is_finite"])
            res_gsub5 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"r_gsub5_O{omega_py_val}", current_omega_smt)
            prop_gsub5 = avc_equiv_canonical(res_gsub5, A)
            prove_or_find_counterexample(s, f"GSUB-5 AS_C - Fp_C ~ AS_C (Omega={omega_py_val})", [res_gsub5["constraints"], res_gsub5["definition"]], prop_gsub5, [A, B, res_gsub5], op_result_dicts_for_debug=[res_gsub5])
            s.pop()

        # --- GSUB-6: Additive Cancellation 1: (A + B)_smart - B_new ~ A ---
        sum_ab_gsub6 = define_op_canonical_result(smart_raw_add_logic_builder, A, B, f"sumAB_gsub6_O{omega_py_val}", current_omega_smt)
        res_sub_gsub6 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, sum_ab_gsub6, B, f"resSub_gsub6_O{omega_py_val}", current_omega_smt)
        prop_gsub6 = avc_equiv_canonical(res_sub_gsub6, A)
        gsub6_setup = [sum_ab_gsub6["constraints"], sum_ab_gsub6["definition"], res_sub_gsub6["constraints"], res_sub_gsub6["definition"]]
        prove_or_find_counterexample(s, f"GSUB-6 (A+B)-B ~ A (Omega={omega_py_val})", gsub6_setup, prop_gsub6, [A, B, sum_ab_gsub6, res_sub_gsub6], op_result_dicts_for_debug=[sum_ab_gsub6, res_sub_gsub6])

        # --- GSUB-7: Additive Cancellation 2: (A - B)_new + B_smart ~ A ---
        sub_ab_gsub7 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"subAB_gsub7_O{omega_py_val}", current_omega_smt)
        res_add_gsub7 = define_op_canonical_result(smart_raw_add_logic_builder, sub_ab_gsub7, B, f"resAdd_gsub7_O{omega_py_val}", current_omega_smt)
        prop_gsub7 = avc_equiv_canonical(res_add_gsub7, A)
        gsub7_setup = [sub_ab_gsub7["constraints"], sub_ab_gsub7["definition"], res_add_gsub7["constraints"], res_add_gsub7["definition"]]
        prove_or_find_counterexample(s, f"GSUB-7 (A-B)+B ~ A (Omega={omega_py_val})", gsub7_setup, prop_gsub7, [A, B, sub_ab_gsub7, res_add_gsub7], op_result_dicts_for_debug=[sub_ab_gsub7, res_add_gsub7])

        # --- GSUB-8: Distributivity of Mul over New Sub ---
        print(f"\n--- Test Group GSUB-8: Distributivity Mul over Sub (Omega={omega_py_val}) ---")
        # GSUB-8.1: Left Distributivity: A * (B - C) ~ (A * B) - (A * C)
        s.push()
        sub_bc_gsub81 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, B, C, f"subBC_gsub81_O{omega_py_val}", current_omega_smt)
        lhs_gsub81 = define_op_canonical_result(raw_mul_logic_builder, A, sub_bc_gsub81, f"lhs_gsub81_O{omega_py_val}", current_omega_smt)
        prod_ab_gsub81 = define_op_canonical_result(raw_mul_logic_builder, A, B, f"prodAB_gsub81_O{omega_py_val}", current_omega_smt)
        prod_ac_gsub81 = define_op_canonical_result(raw_mul_logic_builder, A, C, f"prodAC_gsub81_O{omega_py_val}", current_omega_smt)
        rhs_gsub81 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, prod_ab_gsub81, prod_ac_gsub81, f"rhs_gsub81_O{omega_py_val}", current_omega_smt)
        prop_gsub81 = avc_equiv_canonical(lhs_gsub81, rhs_gsub81)
        gsub81_setup = [ sub_bc_gsub81["constraints"], sub_bc_gsub81["definition"], lhs_gsub81["constraints"], lhs_gsub81["definition"], prod_ab_gsub81["constraints"], prod_ab_gsub81["definition"], prod_ac_gsub81["constraints"], prod_ac_gsub81["definition"], rhs_gsub81["constraints"], rhs_gsub81["definition"] ]
        prove_or_find_counterexample(s, f"GSUB-8.1 Left Distrib A*(B-C) ~ (A*B)-(A*C) (Omega={omega_py_val})", gsub81_setup, prop_gsub81, [A, B, C, lhs_gsub81, rhs_gsub81], op_result_dicts_for_debug=[sub_bc_gsub81, lhs_gsub81, prod_ab_gsub81, prod_ac_gsub81, rhs_gsub81])
        s.pop()

        # GSUB-8.2: Right Distributivity: (A - B) * C ~ (A * C) - (B * C)
        s.push()
        sub_ab_gsub82 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"subAB_gsub82_O{omega_py_val}", current_omega_smt)
        lhs_gsub82 = define_op_canonical_result(raw_mul_logic_builder, sub_ab_gsub82, C, f"lhs_gsub82_O{omega_py_val}", current_omega_smt)
        prod_ac_gsub82 = define_op_canonical_result(raw_mul_logic_builder, A, C, f"prodAC_gsub82_O{omega_py_val}", current_omega_smt)
        prod_bc_gsub82 = define_op_canonical_result(raw_mul_logic_builder, B, C, f"prodBC_gsub82_O{omega_py_val}", current_omega_smt)
        rhs_gsub82 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, prod_ac_gsub82, prod_bc_gsub82, f"rhs_gsub82_O{omega_py_val}", current_omega_smt)
        prop_gsub82 = avc_equiv_canonical(lhs_gsub82, rhs_gsub82)
        gsub82_setup = [ sub_ab_gsub82["constraints"], sub_ab_gsub82["definition"], lhs_gsub82["constraints"], lhs_gsub82["definition"], prod_ac_gsub82["constraints"], prod_ac_gsub82["definition"], prod_bc_gsub82["constraints"], prod_bc_gsub82["definition"], rhs_gsub82["constraints"], rhs_gsub82["definition"] ]
        prove_or_find_counterexample(s, f"GSUB-8.2 Right Distrib (A-B)*C ~ (A*C)-(B*C) (Omega={omega_py_val})", gsub82_setup, prop_gsub82, [A, B, C, lhs_gsub82, rhs_gsub82], op_result_dicts_for_debug=[sub_ab_gsub82, lhs_gsub82, prod_ac_gsub82, prod_bc_gsub82, rhs_gsub82])
        s.pop()

        # --- GSUB-9: Properties of Negation (-A is ZS_C - A) ---
        print(f"\n--- Test Group GSUB-9: Properties of Negation (Omega={omega_py_val}) ---")
        ZS_const = create_intensity_representation(f"ZS_const_O{omega_py_val}")
        zs_const_setup = [ZS_const["constraints"], ZS_const["is_zero"]]
        if omega_py_val == 1: zs_const_setup.append(Not(ZS_const["is_finite"]))
        
        # GSUB-9.1: ZS_C - (ZS_C - A) ~ A  (i.e. -(-A) ~ A)
        s.push()
        s.add_assertions(zs_const_setup) # ZS_const is now a fixed ZS for this scope
        neg_A = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, ZS_const, A, f"negA_gsub91_O{omega_py_val}", current_omega_smt)
        neg_neg_A = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, ZS_const, neg_A, f"negNegA_gsub91_O{omega_py_val}", current_omega_smt)
        prop_gsub91 = avc_equiv_canonical(neg_neg_A, A)
        gsub91_setup = [neg_A["constraints"], neg_A["definition"], neg_neg_A["constraints"], neg_neg_A["definition"]]
        prove_or_find_counterexample(s, f"GSUB-9.1 ZS-(ZS-A) ~ A (Omega={omega_py_val})",
                                     gsub91_setup, prop_gsub91, [A, ZS_const, neg_A, neg_neg_A], op_result_dicts_for_debug=[neg_A, neg_neg_A])
        s.pop()

        # GSUB-9.2: A - B ~ A + (ZS_C - B) (i.e. A - B ~ A + (-B))
        s.push()
        s.add_assertions(zs_const_setup)
        # LHS: A - B
        lhs_gsub92 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"lhs_gsub92_O{omega_py_val}", current_omega_smt)
        # RHS: A + (-B) where -B = ZS_const - B
        neg_B_gsub92 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, ZS_const, B, f"negB_gsub92_O{omega_py_val}", current_omega_smt)
        rhs_gsub92 = define_op_canonical_result(smart_raw_add_logic_builder, A, neg_B_gsub92, f"rhs_gsub92_O{omega_py_val}", current_omega_smt)
        prop_gsub92 = avc_equiv_canonical(lhs_gsub92, rhs_gsub92)
        gsub92_setup = [lhs_gsub92["constraints"], lhs_gsub92["definition"], neg_B_gsub92["constraints"], neg_B_gsub92["definition"], rhs_gsub92["constraints"], rhs_gsub92["definition"]]
        prove_or_find_counterexample(s, f"GSUB-9.2 A-B ~ A+(ZS-B) (Omega={omega_py_val})",
                                     gsub92_setup, prop_gsub92, [A, B, ZS_const, lhs_gsub92, neg_B_gsub92, rhs_gsub92], op_result_dicts_for_debug=[lhs_gsub92,neg_B_gsub92,rhs_gsub92])
        s.pop()
        
        # --- GSUB-10: Subtraction Associativity-like / Transformation Properties ---
        print(f"\n--- Test Group GSUB-10: Subtraction Transformation Properties (Omega={omega_py_val}) ---")
        # GSUB-10.1: (A - B) - C ~ A - (B + C)
        s.push()
        sub_ab_gsub101 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"subAB_g101_O{omega_py_val}", current_omega_smt)
        lhs_gsub101 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, sub_ab_gsub101, C, f"lhs_g101_O{omega_py_val}", current_omega_smt)
        add_bc_gsub101 = define_op_canonical_result(smart_raw_add_logic_builder, B, C, f"addBC_g101_O{omega_py_val}", current_omega_smt)
        rhs_gsub101 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, add_bc_gsub101, f"rhs_g101_O{omega_py_val}", current_omega_smt)
        prop_gsub101 = avc_equiv_canonical(lhs_gsub101, rhs_gsub101)
        gsub101_setup = [sub_ab_gsub101["constraints"], sub_ab_gsub101["definition"], lhs_gsub101["constraints"], lhs_gsub101["definition"], add_bc_gsub101["constraints"], add_bc_gsub101["definition"], rhs_gsub101["constraints"], rhs_gsub101["definition"]]
        prove_or_find_counterexample(s, f"GSUB-10.1 (A-B)-C ~ A-(B+C) (Omega={omega_py_val})",
                                     gsub101_setup, prop_gsub101, [A,B,C, lhs_gsub101, rhs_gsub101], op_result_dicts_for_debug=[sub_ab_gsub101,lhs_gsub101,add_bc_gsub101,rhs_gsub101])
        s.pop()

        # GSUB-10.2: A - (B - C) ~ (A - B) + C
        s.push()
        sub_bc_gsub102 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, B, C, f"subBC_g102_O{omega_py_val}", current_omega_smt)
        lhs_gsub102 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, sub_bc_gsub102, f"lhs_g102_O{omega_py_val}", current_omega_smt)
        sub_ab_gsub102 = define_op_canonical_result(smart_raw_sub_canonical_logic_builder, A, B, f"subAB_g102_O{omega_py_val}", current_omega_smt)
        rhs_gsub102 = define_op_canonical_result(smart_raw_add_logic_builder, sub_ab_gsub102, C, f"rhs_g102_O{omega_py_val}", current_omega_smt)
        prop_gsub102 = avc_equiv_canonical(lhs_gsub102, rhs_gsub102)
        gsub102_setup = [sub_bc_gsub102["constraints"], sub_bc_gsub102["definition"], lhs_gsub102["constraints"], lhs_gsub102["definition"], sub_ab_gsub102["constraints"], sub_ab_gsub102["definition"], rhs_gsub102["constraints"], rhs_gsub102["definition"]]
        prove_or_find_counterexample(s, f"GSUB-10.2 A-(B-C) ~ (A-B)+C (Omega={omega_py_val})",
                                     gsub102_setup, prop_gsub102, [A,B,C, lhs_gsub102, rhs_gsub102], op_result_dicts_for_debug=[sub_bc_gsub102,lhs_gsub102,sub_ab_gsub102,rhs_gsub102])
        s.pop()

        del s
        print("-" * 80)

    print("\n====== AVC General Subtraction Canonical Test (Deep) Complete ======")