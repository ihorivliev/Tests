# Script Name: AVC_Canonical_ChainedOp_Integrity_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Optional

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [2, 3, 5, 7] # Test Omega=2 (standard-like) and Omega>=3 (non-standard)

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

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"]
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]),
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]),
                            Ite(i2["val"] > Int(0),
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))
                               )))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]),
                            Ite(i1["val"] > Int(0),
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))
                               )))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_prod >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                Ite(val_prod <= Int(0), 
                                    And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
                                    And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod))
                                   )
                               )))
    return And(formulas)

def raw_div_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE)
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE)
    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])
    formulas.append(Implies(divisor_is_unio,
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt))
    ))
    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]),
        Or(
            And(i1["is_zero"],
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            And(i1["is_areo"],
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
            And(i1["is_finite"],
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym),
                    rem_sym >= Int(0),
                    rem_sym < i2["val"]),
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)),
                    Ite(q_sym >= current_omega_smt,
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))
                    ),
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt))
                )
            )
        )
    ))
    return And(formulas)

def define_operation_canonical_result(op_logic_builder_func: Callable,
                                      i1_canon_repr: Dict[str, Any], i2_canon_repr: Optional[Dict[str, Any]], 
                                      result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    if i2_canon_repr is None and op_logic_builder_func.__name__ not in ["some_unary_op_logic_builder_if_we_had_one"]: # Placeholder for actual unary ops
        raise ValueError(f"i2_canon_repr cannot be None for binary operation {op_logic_builder_func.__name__}")
        
    res_repr["definition"] = op_logic_builder_func(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_eff_c_smt)))
    return res_repr

# --- Phase 3: Generic Property Prover ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode],
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True,
                                 op_result_dicts_for_debug: List[Dict[str,Any]] = []): # Added op_result_dicts_for_debug
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
            # Print simple FNodes first
            for var_item in model_vars_to_print:
                if isinstance(var_item, FNode) and var_item.is_symbol():
                    try:
                        print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
                    except Exception:
                        print(f"  {var_item.symbol_name()}: (Error getting value or not in model)")
            
            # Then print dict representations, ensuring they are not duplicated by op_result_dicts
            printed_dict_names = set()
            for var_item in model_vars_to_print:
                if isinstance(var_item, dict) and "name" in var_item:
                    if var_item['name'] not in printed_dict_names:
                        val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                        is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                        is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                        is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                        print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                        printed_dict_names.add(var_item['name'])

            if op_result_dicts_for_debug:
                print("  DEBUG Intermediate Canonical Operation Results in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "name" in op_res_dict:
                        # Avoid reprinting if it was already in model_vars_to_print
                        if op_res_dict['name'] not in printed_dict_names:
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
    print("====== AVC Canonical Chained Operation Integrity Test ======\n")

    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        s = Solver(name="z3")
        current_omega_smt = Int(omega_py_val)
        print(f"\n\n===== CANONICAL CHAINED OP TESTS WITH OMEGA = {omega_py_val} =====\n")

        A = create_intensity_representation(f"A_O{omega_py_val}")
        B = create_intensity_representation(f"B_O{omega_py_val}")
        C = create_intensity_representation(f"C_O{omega_py_val}")
        D = create_intensity_representation(f"D_O{omega_py_val}")
        E = create_intensity_representation(f"E_O{omega_py_val}")
        W = create_intensity_representation(f"W_O{omega_py_val}") # For COI-6

        all_inputs = [A, B, C, D, E, W]
        base_constraints = []
        for inp_repr in all_inputs:
            base_constraints.append(inp_repr["constraints"])
            base_constraints.append(Implies(inp_repr["is_areo"], Equals(inp_repr["val"], current_omega_smt)))
            if omega_py_val > 1:
                base_constraints.append(Implies(inp_repr["is_finite"], inp_repr["val"] < current_omega_smt))
            else: # Omega == 1, no Finites possible
                base_constraints.append(Not(inp_repr["is_finite"]))
        
        s.add_assertions(base_constraints) # Assert these globally for this omega loop

        # --- COI-1: FOIL-like Expansion: (A+B)*(C+D) ~ (A*C)+(A*D)+(B*C)+(B*D) ---
        # To make this testable, we need to group RHS due to non-assoc of add
        # Test: (A+B)*(C+D) ~ ((A*C)+(A*D)) + ((B*C)+(B*D))
        s.push()
        sum_ab = define_operation_canonical_result(smart_raw_add_logic_builder, A, B, f"sAB_coi1", current_omega_smt)
        sum_cd = define_operation_canonical_result(smart_raw_add_logic_builder, C, D, f"sCD_coi1", current_omega_smt)
        lhs_coi1 = define_operation_canonical_result(raw_mul_logic_builder, sum_ab, sum_cd, f"lhs_coi1", current_omega_smt)

        prod_ac = define_operation_canonical_result(raw_mul_logic_builder, A, C, f"pAC_coi1", current_omega_smt)
        prod_ad = define_operation_canonical_result(raw_mul_logic_builder, A, D, f"pAD_coi1", current_omega_smt)
        prod_bc = define_operation_canonical_result(raw_mul_logic_builder, B, C, f"pBC_coi1", current_omega_smt)
        prod_bd = define_operation_canonical_result(raw_mul_logic_builder, B, D, f"pBD_coi1", current_omega_smt)
        sum_acad = define_operation_canonical_result(smart_raw_add_logic_builder, prod_ac, prod_ad, f"sACAD_coi1", current_omega_smt)
        sum_bcbd = define_operation_canonical_result(smart_raw_add_logic_builder, prod_bc, prod_bd, f"sBCBD_coi1", current_omega_smt)
        rhs_coi1 = define_operation_canonical_result(smart_raw_add_logic_builder, sum_acad, sum_bcbd, f"rhs_coi1", current_omega_smt)

        prop_coi1 = avc_equiv_canonical(lhs_coi1, rhs_coi1)
        setup_coi1 = ([sum_ab["definition"], sum_ab["constraints"], sum_cd["definition"], sum_cd["constraints"], lhs_coi1["definition"], lhs_coi1["constraints"]] +
                      [prod_ac["definition"], prod_ac["constraints"], prod_ad["definition"], prod_ad["constraints"], prod_bc["definition"], prod_bc["constraints"], prod_bd["definition"], prod_bd["constraints"]] +
                      [sum_acad["definition"], sum_acad["constraints"], sum_bcbd["definition"], sum_bcbd["constraints"], rhs_coi1["definition"], rhs_coi1["constraints"]])
        prove_or_find_counterexample(s, f"COI-1 FOIL-like (Omega={omega_py_val})", setup_coi1, prop_coi1,
                                     [A,B,C,D,lhs_coi1,rhs_coi1], op_result_dicts_for_debug=[sum_ab, sum_cd, prod_ac, prod_ad, prod_bc, prod_bd, sum_acad, sum_bcbd])
        s.pop()

        # --- COI-2: Integrity of Zero/Identity in a Chain: (((A*B)/B)-A)*C ~ ZS_C ---
        # B must not be Unio for division.
        if omega_py_val > 1: # Need DFI for B
            s.push()
            s.add_assertion(B["is_finite"]) # B is Fp
            s.add_assertion(B["val"] < current_omega_smt) # B is Fp < Omega
            
            prod_ab_coi2 = define_operation_canonical_result(raw_mul_logic_builder, A, B, f"pAB_coi2", current_omega_smt)
            div_pab_b_coi2 = define_operation_canonical_result(raw_div_logic_builder, prod_ab_coi2, B, f"dAB_B_coi2", current_omega_smt)
            sub_term_a_coi2 = define_operation_canonical_result(smart_raw_sub_canonical_logic_builder, div_pab_b_coi2, A, f"sT_A_coi2", current_omega_smt)
            lhs_coi2 = define_operation_canonical_result(raw_mul_logic_builder, sub_term_a_coi2, C, f"lhs_coi2", current_omega_smt)

            ZS_target = create_intensity_representation(f"ZSTarget_coi2")
            s.add_assertion(ZS_target["constraints"])
            s.add_assertion(ZS_target["is_zero"])
            if omega_py_val ==1: s.add_assertion(Not(ZS_target["is_finite"]))


            prop_coi2 = avc_equiv_canonical(lhs_coi2, ZS_target)
            setup_coi2 = ([prod_ab_coi2["definition"], prod_ab_coi2["constraints"], div_pab_b_coi2["definition"], div_pab_b_coi2["constraints"],
                           sub_term_a_coi2["definition"], sub_term_a_coi2["constraints"], lhs_coi2["definition"], lhs_coi2["constraints"]])
            prove_or_find_counterexample(s, f"COI-2 Zero Chain (((A*B)/B)-A)*C ~ ZS (Omega={omega_py_val})", setup_coi2, prop_coi2,
                                         [A,B,C,lhs_coi2, ZS_target], op_result_dicts_for_debug=[prod_ab_coi2, div_pab_b_coi2, sub_term_a_coi2])
            s.pop()
        else:
            print(f"--- SKIPPING COI-2 for Omega=1 (Requires DFI for B) ---")

        # --- COI-3: Order of Operations with Mixed Add/Sub: (A+B)-C ~ A+(B-C) ---
        s.push()
        sum_ab_coi3 = define_operation_canonical_result(smart_raw_add_logic_builder, A, B, f"sAB_coi3", current_omega_smt)
        lhs_coi3 = define_operation_canonical_result(smart_raw_sub_canonical_logic_builder, sum_ab_coi3, C, f"lhs_coi3", current_omega_smt)
        sub_bc_coi3 = define_operation_canonical_result(smart_raw_sub_canonical_logic_builder, B, C, f"sBC_coi3", current_omega_smt)
        rhs_coi3 = define_operation_canonical_result(smart_raw_add_logic_builder, A, sub_bc_coi3, f"rhs_coi3", current_omega_smt)
        prop_coi3 = avc_equiv_canonical(lhs_coi3, rhs_coi3)
        setup_coi3 = ([sum_ab_coi3["definition"], sum_ab_coi3["constraints"], lhs_coi3["definition"], lhs_coi3["constraints"],
                       sub_bc_coi3["definition"], sub_bc_coi3["constraints"], rhs_coi3["definition"], rhs_coi3["constraints"]])
        prove_or_find_counterexample(s, f"COI-3 Mixed Add/Sub (A+B)-C ~ A+(B-C) (Omega={omega_py_val})", setup_coi3, prop_coi3,
                                     [A,B,C,lhs_coi3,rhs_coi3], op_result_dicts_for_debug=[sum_ab_coi3, sub_bc_coi3])
        s.pop()
        
        # --- COI-5: Iterated Subtraction from Areo: (((AS_C - Fp1) - Fp2) - Fp3) ~ AS_C ---
        # Requires Fp1, Fp2, Fp3 to be distinct small DFIs
        if omega_py_val >= 4: # Need at least 3 distinct DFIs + AS
            s.push()
            AS_const = create_intensity_representation("AS_const_coi5")
            s.add_assertion(AS_const["constraints"])
            s.add_assertion(AS_const["is_areo"])
            s.add_assertion(Equals(AS_const["val"], current_omega_smt))

            Fp1 = create_intensity_representation("Fp1_coi5")
            Fp2 = create_intensity_representation("Fp2_coi5")
            Fp3 = create_intensity_representation("Fp3_coi5")
            fp_setup = [ Fp1["constraints"], Fp1["is_finite"], Equals(Fp1["val"], Int(1)), Fp1["val"] < current_omega_smt,
                         Fp2["constraints"], Fp2["is_finite"], Equals(Fp2["val"], Int(2)), Fp2["val"] < current_omega_smt,
                         Fp3["constraints"], Fp3["is_finite"], Equals(Fp3["val"], Int(3)), Fp3["val"] < current_omega_smt,
                         Not(Equals(Fp1["val"],Fp2["val"])), Not(Equals(Fp1["val"],Fp3["val"])), Not(Equals(Fp2["val"],Fp3["val"]))
                       ]
            s.add_assertions(fp_setup)

            term1_coi5 = define_operation_canonical_result(smart_raw_sub_canonical_logic_builder, AS_const, Fp1, "t1_coi5", current_omega_smt)
            term2_coi5 = define_operation_canonical_result(smart_raw_sub_canonical_logic_builder, term1_coi5, Fp2, "t2_coi5", current_omega_smt)
            lhs_coi5 = define_operation_canonical_result(smart_raw_sub_canonical_logic_builder, term2_coi5, Fp3, "lhs_coi5", current_omega_smt)
            
            prop_coi5 = avc_equiv_canonical(lhs_coi5, AS_const)
            setup_coi5 = ([term1_coi5["definition"], term1_coi5["constraints"], term2_coi5["definition"], term2_coi5["constraints"],
                           lhs_coi5["definition"], lhs_coi5["constraints"]])
            prove_or_find_counterexample(s, f"COI-5 Iterated Sub from AS ~ AS (Omega={omega_py_val})", setup_coi5, prop_coi5,
                                         [AS_const,Fp1,Fp2,Fp3,lhs_coi5], op_result_dicts_for_debug=[term1_coi5, term2_coi5])
            s.pop()
        else:
            print(f"--- SKIPPING COI-5 for Omega={omega_py_val} (Requires richer DFI) ---")

        # --- COI-6: Path Dependence from Additive Non-Associativity ---
        # If (X+Y)+Z (LHS_add) is not ~ X+(Y+Z) (RHS_add), does multiplying by W change this?
        # This test uses symbolic X,Y,Z,W that are Finites to stress non-associativity
        if omega_py_val >= 3: # Non-associativity of add starts at Omega=3
            s.push()
            # Ensure X,Y,Z,W are DFIs for this test
            s.add_assertion(A["is_finite"]) # A is X
            s.add_assertion(B["is_finite"]) # B is Y
            s.add_assertion(C["is_finite"]) # C is Z
            s.add_assertion(D["is_finite"]) # D is W (multiplier/divisor)
            s.add_assertion(A["val"] < current_omega_smt)
            s.add_assertion(B["val"] < current_omega_smt)
            s.add_assertion(C["val"] < current_omega_smt)
            s.add_assertion(D["val"] < current_omega_smt)


            sum_ab_coi6 = define_operation_canonical_result(smart_raw_add_logic_builder, A, B, "sAB_coi6", current_omega_smt)
            lhs_add_coi6 = define_operation_canonical_result(smart_raw_add_logic_builder, sum_ab_coi6, C, "lhsAdd_coi6", current_omega_smt)
            sum_bc_coi6 = define_operation_canonical_result(smart_raw_add_logic_builder, B, C, "sBC_coi6", current_omega_smt)
            rhs_add_coi6 = define_operation_canonical_result(smart_raw_add_logic_builder, A, sum_bc_coi6, "rhsAdd_coi6", current_omega_smt)
            
            # Premise: (A+B)+C is NOT equivalent to A+(B+C) for some Finites A,B,C
            # This is known for Omega >= 3. We don't need to assert Not(avc_equiv(lhs_add,rhs_add))
            # Instead, we test if their products/divisions with W become equivalent or stay non-equivalent

            # COI-6.1: Test ( (A+B)+C ) * W ~ ( A+(B+C) ) * W
            lhs_mul_coi6 = define_operation_canonical_result(raw_mul_logic_builder, lhs_add_coi6, D, "lhsMul_coi6", current_omega_smt)
            rhs_mul_coi6 = define_operation_canonical_result(raw_mul_logic_builder, rhs_add_coi6, D, "rhsMul_coi6", current_omega_smt)
            prop_coi61 = avc_equiv_canonical(lhs_mul_coi6, rhs_mul_coi6)
            setup_coi61 = ([sum_ab_coi6["definition"], sum_ab_coi6["constraints"], lhs_add_coi6["definition"], lhs_add_coi6["constraints"],
                            sum_bc_coi6["definition"], sum_bc_coi6["constraints"], rhs_add_coi6["definition"], rhs_add_coi6["constraints"],
                            lhs_mul_coi6["definition"], lhs_mul_coi6["constraints"], rhs_mul_coi6["definition"], rhs_mul_coi6["constraints"]])
            prove_or_find_counterexample(s, f"COI-6.1 Path Dep Mul: (LHS_add)*W ~ (RHS_add)*W (Omega={omega_py_val})", setup_coi61, prop_coi61,
                                         [A,B,C,D,lhs_add_coi6,rhs_add_coi6,lhs_mul_coi6,rhs_mul_coi6], 
                                         op_result_dicts_for_debug=[sum_ab_coi6,lhs_add_coi6,sum_bc_coi6,rhs_add_coi6])

            # COI-6.2: Test ( (A+B)+C ) / W ~ ( A+(B+C) ) / W (W is DFI)
            # We need W (which is D here) to be DFI for division to be meaningful.
            s.push() # Inner push for W=DFI constraint
            s.add_assertion(D["is_finite"]) # W is DFI
            s.add_assertion(D["val"] < current_omega_smt)

            lhs_div_coi6 = define_operation_canonical_result(raw_div_logic_builder, lhs_add_coi6, D, "lhsDiv_coi6", current_omega_smt)
            rhs_div_coi6 = define_operation_canonical_result(raw_div_logic_builder, rhs_add_coi6, D, "rhsDiv_coi6", current_omega_smt)
            prop_coi62 = avc_equiv_canonical(lhs_div_coi6, rhs_div_coi6)
            # Setup assertions from coi61 already cover add parts. Add div parts.
            setup_coi62 = setup_coi61 + [lhs_div_coi6["definition"], lhs_div_coi6["constraints"], rhs_div_coi6["definition"], rhs_div_coi6["constraints"]]
            prove_or_find_counterexample(s, f"COI-6.2 Path Dep Div: (LHS_add)/W ~ (RHS_add)/W (W is DFI) (Omega={omega_py_val})", setup_coi62, prop_coi62,
                                         [A,B,C,D,lhs_add_coi6,rhs_add_coi6,lhs_div_coi6,rhs_div_coi6],
                                         op_result_dicts_for_debug=[sum_ab_coi6,lhs_add_coi6,sum_bc_coi6,rhs_add_coi6])
            s.pop() # Pop W=DFI constraint
            s.pop() # Pop main COI-6 context
        else:
            print(f"--- SKIPPING COI-6 for Omega={omega_py_val} (Additive non-assoc needs Omega>=3) ---")


        del s
        print("-" * 80)

    print("\n====== AVC Canonical Chained Operation Integrity Test Complete ======")