# Script Name: AVC_General_Subtraction_Adaptive_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Requirement 4, Step 2: General Subtraction in Adaptive Model
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5] 
DEFAULT_P_A_OFFSET = 0

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

# Define specific canonical result functions that use the generic create_intensity_representation and add constraints
def define_smart_raw_add_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any],
                                          result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_eff_c_smt)))
    return res_repr

def define_smart_raw_sub_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any],
                                          result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_sub_canonical_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_eff_c_smt)))
    return res_repr

# --- Phase 3: Local Frame, Adaptive Omega, and Mappings (Simple Adaptive Model) ---
def is_local_ZS_val(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS_val(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI_val(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    # Ensures P_A < val_L < P_B, implies S_L >= 2
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

def avc_equiv_local_val(X1_L_val_sym: FNode, X2_L_val_sym: FNode,
                        P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Or(
        And(is_local_ZS_val(X1_L_val_sym, P_A_val_sym), is_local_ZS_val(X2_L_val_sym, P_A_val_sym)),
        And(is_local_AS_val(X1_L_val_sym, P_B_val_sym), is_local_AS_val(X2_L_val_sym, P_B_val_sym)),
        And(is_local_ZS_val(X1_L_val_sym, P_A_val_sym), is_local_AS_val(X2_L_val_sym, P_B_val_sym)),
        And(is_local_AS_val(X1_L_val_sym, P_B_val_sym), is_local_ZS_val(X2_L_val_sym, P_A_val_sym)),
        And(is_local_DFI_val(X1_L_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI_val(X2_L_val_sym, P_A_val_sym, P_B_val_sym),
            Equals(X1_L_val_sym, X2_L_val_sym)))

def determine_effective_canonical_omega(S_val_sym: FNode) -> FNode:
    return Ite(Equals(S_val_sym, Int(1)), Int(1),
           Ite(Equals(S_val_sym, Int(2)), Int(2),
                                           Int(3)))

def map_local_to_adaptive_archetype_input_repr(
    Local_val_sym: FNode,
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode,
    Omega_eff_C_sym: FNode,
    arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    arch_repr = create_intensity_representation(arch_name_prefix)
    is_L_ZS_cond = is_local_ZS_val(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS_val(Local_val_sym, PB_sym)
    is_L_DFI_cond = is_local_DFI_val(Local_val_sym, PA_sym, PB_sym)
    kind_assertions = [
        arch_repr["constraints"],
        Implies(is_L_ZS_cond, And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))),
        Implies(is_L_AS_cond, And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))),
        Implies(is_L_DFI_cond, And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"]))
    ]
    val_assertions = [Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym))]
    val_if_omega_eff_is_2 = Int(1)
    val_if_omega_eff_is_3 = Ite(Equals(Local_val_sym, PA_sym + Int(1)), Int(1), Int(2))
    val_assertions.append(
        Implies(arch_repr["is_finite"],
            Ite(Equals(Omega_eff_C_sym, Int(1)), FALSE(),
            Ite(Equals(Omega_eff_C_sym, Int(2)), Equals(arch_repr["val"], val_if_omega_eff_is_2),
                 Equals(arch_repr["val"], val_if_omega_eff_is_3)))))
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))
    return arch_repr, kind_assertions + val_assertions

def map_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], PA_sym: FNode, PB_sym: FNode, S_sym: FNode, Omega_eff_C_sym: FNode
) -> FNode:
    val_from_fp_if_omega_eff_is_1 = PB_sym
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))
    val_from_fp_if_omega_eff_is_3 = \
        Ite(Equals(S_sym, Int(1)), PB_sym,
        Ite(Equals(S_sym, Int(2)),
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym),
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym - Int(1))))
    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                    Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         val_from_fp_if_omega_eff_is_3))
    return Ite(Arch_Res_Repr["is_zero"], PA_sym, Ite(Arch_Res_Repr["is_areo"], PB_sym, fp_result_val))

def define_local_op_adaptive_archetype_result(
    op_canonical_result_definer_func: Callable, # e.g., define_smart_raw_sub_canonical_result
    X_L_val_sym: FNode, Y_L_val_sym: FNode,
    P_A_val_sym: FNode, P_B_val_sym: FNode, result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    S_val_sym = P_B_val_sym - P_A_val_sym
    Omega_eff_C_sym = determine_effective_canonical_omega(S_val_sym)
    X_canon_repr, x_canon_assertions = map_local_to_adaptive_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_xc")
    defining_assertions_for_local_op.extend(x_canon_assertions)
    Y_canon_repr, y_canon_assertions = map_local_to_adaptive_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_yc")
    defining_assertions_for_local_op.extend(y_canon_assertions)
    
    Res_canon_repr = op_canonical_result_definer_func( 
        X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", Omega_eff_C_sym
    )
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"]) 
    
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym)
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))
    debug_info = {"X_L_val_dbg": X_L_val_sym, "X_canon_repr_dbg": X_canon_repr,
                  "Y_L_val_dbg": Y_L_val_sym, "Y_canon_repr_dbg": Y_canon_repr,
                  "Res_canon_repr_dbg": Res_canon_repr, "Omega_eff_C_sym_dbg": Omega_eff_C_sym,
                  "S_val_sym_dbg": S_val_sym, "parent_dict_name_for_debug": result_name_prefix_local }
    return {"val_L_sym": Res_L_val_sym, "defining_assertions": defining_assertions_for_local_op, "debug_info": debug_info}

# --- Phase 4: Generic Property Prover ---
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
                elif isinstance(var_item, FNode): # Print simple FNodes like PA_val_sym etc.
                    if var_item.is_symbol():
                        print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
            
            if op_result_dicts_for_debug:
                print("  DEBUG Canonical Mappings/Results in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "debug_info" in op_res_dict:
                        debug_info = op_res_dict["debug_info"]
                        if isinstance(debug_info, dict) and id(debug_info) not in printed_debug_info_ids:
                            printed_debug_info_ids.add(id(debug_info))
                            op_name_for_print = debug_info.get("parent_dict_name_for_debug", "UnknownOp")
                            print(f"    Context for Local Result '{op_name_for_print}':")

                            s_val_dbg = debug_info.get('S_val_sym_dbg')
                            o_eff_dbg = debug_info.get('Omega_eff_C_sym_dbg')
                            s_val_str = f"{solver.get_value(s_val_dbg)}" if s_val_dbg and s_val_dbg in solver.get_model() else "?"
                            o_eff_str = f"{solver.get_value(o_eff_dbg)}" if o_eff_dbg and o_eff_dbg in solver.get_model() else "?"
                            print(f"      Local Span S_val={s_val_str}, Effective Canon. Omega_eff_C={o_eff_str}")

                            for repr_key_tuple in [("X_L_val_dbg", "X_canon_repr_dbg"), ("Y_L_val_dbg", "Y_canon_repr_dbg"), (None, "Res_canon_repr_dbg")]:
                                local_val_key, canon_repr_key = repr_key_tuple
                                if local_val_key:
                                    local_val_sym_dbg = debug_info.get(local_val_key)
                                    if local_val_sym_dbg and local_val_sym_dbg in solver.get_model(): print(f"        Local Input {local_val_key.split('_')[0]}: {local_val_sym_dbg.symbol_name()} = {solver.get_value(local_val_sym_dbg)}")
                                repr_dict_dbg = debug_info.get(canon_repr_key)
                                if repr_dict_dbg and isinstance(repr_dict_dbg, dict) and "name" in repr_dict_dbg:
                                    val_str_node = f"V={solver.get_value(repr_dict_dbg['val'])}" if repr_dict_dbg['val'] in solver.get_model() else "V=?"
                                    is_z_str_node = f"Z={solver.get_value(repr_dict_dbg['is_zero'])}" if repr_dict_dbg['is_zero'] in solver.get_model() else "Z=?"
                                    is_a_str_node = f"A={solver.get_value(repr_dict_dbg['is_areo'])}" if repr_dict_dbg['is_areo'] in solver.get_model() else "A=?"
                                    is_f_str_node = f"F={solver.get_value(repr_dict_dbg['is_finite'])}" if repr_dict_dbg['is_finite'] in solver.get_model() else "F=?"
                                    print(f"          {repr_dict_dbg['name']} (Canon): {is_z_str_node}, {is_a_str_node}, {is_f_str_node}, {val_str_node}")
    solver.pop()
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC General Subtraction Adaptive Test ======\n")

    P_A_val_sym = Symbol("PA_val_gsubadap", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_gsubadap", solver_INT_TYPE)
    
    # For general tests GSUB-Adap-0,1,2,6,7
    A_L_val = Symbol("A_L_gsubadap", solver_INT_TYPE)
    B_L_val = Symbol("B_L_gsubadap", solver_INT_TYPE)
    # For specific kind tests GSUB-Adap-3,4,5
    Fp_L_val = Symbol("Fp_L_gsubadap", solver_INT_TYPE) 

    # For GSUB-Adap-0 (Well-definedness)
    A1_L_val = Symbol("A1_L_gsubadap", solver_INT_TYPE)
    A2_L_val = Symbol("A2_L_gsubadap", solver_INT_TYPE)
    B1_L_val = Symbol("B1_L_gsubadap", solver_INT_TYPE)
    B2_L_val = Symbol("B2_L_gsubadap", solver_INT_TYPE)


    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== ADAPTIVE SUBTRACTION TESTS WITH Local Span S = {current_local_span_S_py} =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        # Constraints for general symbolic local values A_L, B_L to be valid in the frame
        general_inputs_setup = [
            And(A_L_val >= P_A_val_sym, A_L_val <= P_B_val_sym),
            And(B_L_val >= P_A_val_sym, B_L_val <= P_B_val_sym),
        ]
        # For well-definedness, A1,A2,B1,B2 also need to be valid
        wd_inputs_setup = general_inputs_setup + [
            And(A1_L_val >= P_A_val_sym, A1_L_val <= P_B_val_sym),
            And(A2_L_val >= P_A_val_sym, A2_L_val <= P_B_val_sym),
            And(B1_L_val >= P_A_val_sym, B1_L_val <= P_B_val_sym),
            And(B2_L_val >= P_A_val_sym, B2_L_val <= P_B_val_sym),
        ]
        
        # --- GSUB-Adap-0: Well-Definedness ---
        s.push()
        s.add_assertions(wd_inputs_setup)
        prem_gsub_adap0 = And(avc_equiv_local_val(A1_L_val, A2_L_val, P_A_val_sym, P_B_val_sym),
                              avc_equiv_local_val(B1_L_val, B2_L_val, P_A_val_sym, P_B_val_sym))
        res1_gsub_adap0 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, A1_L_val, B1_L_val, P_A_val_sym, P_B_val_sym, f"r1_gsa0_S{current_local_span_S_py}")
        res2_gsub_adap0 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, A2_L_val, B2_L_val, P_A_val_sym, P_B_val_sym, f"r2_gsa0_S{current_local_span_S_py}")
        conc_gsub_adap0 = avc_equiv_local_val(res1_gsub_adap0["val_L_sym"], res2_gsub_adap0["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gsub_adap0 = [prem_gsub_adap0] + res1_gsub_adap0["defining_assertions"] + res2_gsub_adap0["defining_assertions"]
        prove_or_find_counterexample(s, f"GSUB-Adap-0 Well-Defined (S={current_local_span_S_py})", setup_gsub_adap0, conc_gsub_adap0, 
                                     [P_A_val_sym, P_B_val_sym, A1_L_val, A2_L_val, B1_L_val, B2_L_val, res1_gsub_adap0["val_L_sym"], res2_gsub_adap0["val_L_sym"]],
                                     op_result_dicts_for_debug=[res1_gsub_adap0, res2_gsub_adap0])
        s.pop()

        # --- GSUB-Adap-1: A_L - A_L ~ ZS_L ---
        s.push()
        s.add_assertion(And(A_L_val >= P_A_val_sym, A_L_val <= P_B_val_sym)) # A_L is general
        res_gsub_adap1 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, A_L_val, A_L_val, P_A_val_sym, P_B_val_sym, f"r_gsa1_S{current_local_span_S_py}")
        prop_gsub_adap1 = is_local_ZS_val(res_gsub_adap1["val_L_sym"], P_A_val_sym) # Equiv to ZS_L
        setup_gsub_adap1 = res_gsub_adap1["defining_assertions"]
        prove_or_find_counterexample(s, f"GSUB-Adap-1 A_L-A_L ~ ZS_L (S={current_local_span_S_py})", setup_gsub_adap1, prop_gsub_adap1,
                                     [P_A_val_sym, P_B_val_sym, A_L_val, res_gsub_adap1["val_L_sym"]], op_result_dicts_for_debug=[res_gsub_adap1])
        s.pop()

        # --- GSUB-Adap-2: A_L - ZS_L ~ A_L ---
        s.push()
        s.add_assertion(And(A_L_val >= P_A_val_sym, A_L_val <= P_B_val_sym)) # A_L is general
        res_gsub_adap2 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, A_L_val, P_A_val_sym, P_A_val_sym, P_B_val_sym, f"r_gsa2_S{current_local_span_S_py}")
        prop_gsub_adap2 = avc_equiv_local_val(res_gsub_adap2["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
        setup_gsub_adap2 = res_gsub_adap2["defining_assertions"]
        prove_or_find_counterexample(s, f"GSUB-Adap-2 A_L-ZS_L ~ A_L (S={current_local_span_S_py})", setup_gsub_adap2, prop_gsub_adap2,
                                     [P_A_val_sym, P_B_val_sym, A_L_val, res_gsub_adap2["val_L_sym"]], op_result_dicts_for_debug=[res_gsub_adap2])
        s.pop()
        
        # Specific kind tests (GSUB-Adap-3,4,5) only if DFI can exist (S >= 2)
        if current_local_span_S_py >= 2:
            # GSUB-Adap-3: Fp_L(x) - AS_L ~ Fp_L(x)
            s.push()
            s.add_assertion(is_local_DFI_val(Fp_L_val, P_A_val_sym, P_B_val_sym)) # Fp_L_val is DFI
            res_gsub_adap3 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, Fp_L_val, P_B_val_sym, P_A_val_sym, P_B_val_sym, f"r_gsa3_S{current_local_span_S_py}")
            prop_gsub_adap3 = avc_equiv_local_val(res_gsub_adap3["val_L_sym"], Fp_L_val, P_A_val_sym, P_B_val_sym)
            setup_gsub_adap3 = res_gsub_adap3["defining_assertions"]
            prove_or_find_counterexample(s, f"GSUB-Adap-3 Fp_L-AS_L ~ Fp_L (S={current_local_span_S_py})", setup_gsub_adap3, prop_gsub_adap3,
                                         [P_A_val_sym, P_B_val_sym, Fp_L_val, res_gsub_adap3["val_L_sym"]], op_result_dicts_for_debug=[res_gsub_adap3])
            s.pop()

            # GSUB-Adap-4: ZS_L - Fp_L ~ AS_L
            s.push()
            s.add_assertion(is_local_DFI_val(Fp_L_val, P_A_val_sym, P_B_val_sym)) # Fp_L_val is DFI
            res_gsub_adap4 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, P_A_val_sym, Fp_L_val, P_A_val_sym, P_B_val_sym, f"r_gsa4_S{current_local_span_S_py}")
            prop_gsub_adap4 = is_local_AS_val(res_gsub_adap4["val_L_sym"], P_B_val_sym) # Equiv to AS_L
            setup_gsub_adap4 = res_gsub_adap4["defining_assertions"]
            prove_or_find_counterexample(s, f"GSUB-Adap-4 ZS_L-Fp_L ~ AS_L (S={current_local_span_S_py})", setup_gsub_adap4, prop_gsub_adap4,
                                         [P_A_val_sym, P_B_val_sym, Fp_L_val, res_gsub_adap4["val_L_sym"]], op_result_dicts_for_debug=[res_gsub_adap4])
            s.pop()

            # GSUB-Adap-5: AS_L - Fp_L ~ AS_L
            s.push()
            s.add_assertion(is_local_DFI_val(Fp_L_val, P_A_val_sym, P_B_val_sym)) # Fp_L_val is DFI
            res_gsub_adap5 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, P_B_val_sym, Fp_L_val, P_A_val_sym, P_B_val_sym, f"r_gsa5_S{current_local_span_S_py}")
            prop_gsub_adap5 = is_local_AS_val(res_gsub_adap5["val_L_sym"], P_B_val_sym) # Equiv to AS_L
            setup_gsub_adap5 = res_gsub_adap5["defining_assertions"]
            prove_or_find_counterexample(s, f"GSUB-Adap-5 AS_L-Fp_L ~ AS_L (S={current_local_span_S_py})", setup_gsub_adap5, prop_gsub_adap5,
                                         [P_A_val_sym, P_B_val_sym, Fp_L_val, res_gsub_adap5["val_L_sym"]], op_result_dicts_for_debug=[res_gsub_adap5])
            s.pop()
        else: # S=1, no Fp_L, skip GSUB-Adap-3,4,5
            print(f"--- SKIPPING GSUB-Adap-3,4,5 for S=1 (No DFI to test with) ---")


        # --- GSUB-Adap-6: Additive Cancellation 1: (A_L + B_L) - B_L ~ A_L ---
        s.push()
        s.add_assertions(general_inputs_setup) # A_L, B_L are general
        sum_ab_gsa6 = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"sumAB_gsa6_S{current_local_span_S_py}")
        res_sub_gsa6 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, sum_ab_gsa6["val_L_sym"], B_L_val, P_A_val_sym, P_B_val_sym, f"resSub_gsa6_S{current_local_span_S_py}")
        prop_gsa6 = avc_equiv_local_val(res_sub_gsa6["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
        setup_gsa6 = sum_ab_gsa6["defining_assertions"] + res_sub_gsa6["defining_assertions"]
        prove_or_find_counterexample(s, f"GSUB-Adap-6 (A_L+B_L)-B_L ~ A_L (S={current_local_span_S_py})", setup_gsa6, prop_gsa6,
                                     [P_A_val_sym, P_B_val_sym, A_L_val, B_L_val, sum_ab_gsa6["val_L_sym"], res_sub_gsa6["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_gsa6, res_sub_gsa6])
        s.pop()

        # --- GSUB-Adap-7: Additive Cancellation 2: (A_L - B_L) + B_L ~ A_L ---
        s.push()
        s.add_assertions(general_inputs_setup) # A_L, B_L are general
        sub_ab_gsa7 = define_local_op_adaptive_archetype_result(define_smart_raw_sub_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"subAB_gsa7_S{current_local_span_S_py}")
        res_add_gsa7 = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, sub_ab_gsa7["val_L_sym"], B_L_val, P_A_val_sym, P_B_val_sym, f"resAdd_gsa7_S{current_local_span_S_py}")
        prop_gsa7 = avc_equiv_local_val(res_add_gsa7["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
        setup_gsa7 = sub_ab_gsa7["defining_assertions"] + res_add_gsa7["defining_assertions"]
        prove_or_find_counterexample(s, f"GSUB-Adap-7 (A_L-B_L)+B_L ~ A_L (S={current_local_span_S_py})", setup_gsa7, prop_gsa7,
                                     [P_A_val_sym, P_B_val_sym, A_L_val, B_L_val, sub_ab_gsa7["val_L_sym"], res_add_gsa7["val_L_sym"]],
                                     op_result_dicts_for_debug=[sub_ab_gsa7, res_add_gsa7])
        s.pop()
        
        del s
        print("-" * 80)

    print("\n====== AVC General Subtraction Adaptive Test Complete ======")