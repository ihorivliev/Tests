from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7] 
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
                                res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode:
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])))))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))))) 
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
                            Ite(val_sum >= current_omega_eff_c_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) 
                            )))
    return And(formulas)

def define_smart_raw_add_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                          result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"] 
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]), And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]), 
                            Ite(i2["val"] > Int(0), And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])))))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]), 
                            Ite(i1["val"] > Int(0), And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
                            Ite(val_prod >= current_omega_eff_c_smt, And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
    return And(formulas)

def define_raw_mul_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                    result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

def raw_div_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode: 
    formulas = [] 
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE) 
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE) 
    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])
    formulas.append(Implies(divisor_is_unio, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), 
        Or( 
            And(i1["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), 
            And(i1["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(i1["is_finite"], 
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), rem_sym >= Int(0), rem_sym < i2["val"]), 
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)), 
                    Ite(q_sym >= current_omega_eff_c_smt, 
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))), 
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) )))))
    return And(formulas)

def define_raw_div_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                     result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_div_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

def raw_sub_from_Unio_Areo_aspect_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                                res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode:
    # Premise: i1 is Unio (ZS or AS), i2 is DFI. Result is always AS.
    # This covers Postulate 6.3 (U - X_DFI -> U via Areo-aspect)
    # and P2.2.iv (A - X_DFI = A).
    # If ZS - X_DFI "goes below zero", it resolves to Unio (AS aspect).
    is_i1_unio_component = Or(i1["is_zero"], i1["is_areo"])
    
    # The core definition: if i1 is a Unio component and i2 is Finite, the result is Areo.
    # If i2 is not Finite (i.e., ZS or AS), this specific rule doesn't apply.
    # A full subtraction would define U-U -> U, U-ZS -> U, U-AS -> U etc.
    # For this test, focusing on P6.3/P2.2.iv, i2 must be DFI for the rule to clearly fire.
    core_def = Implies(And(is_i1_unio_component, i2["is_finite"]), 
                       And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])))

    # What if i1 is not a Unio component OR i2 is not Finite?
    # The result should be robustly defined for well-definedness tests.
    # If i1 is Finite (violating precondition for *this* sub op): result could be undefined by *this* rule.
    # To make the operation total for SMT (even if conceptually a misuse):
    # Fp - X -> AS (if this op is called with Fp, treat it as an error resolving to AS/Unio)
    # Unio - Unio -> AS
    # Unio - ZS -> AS
    # Unio - AS -> AS (all these maintain result is Unio/AS)
    
    other_cases_res_AS = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]))

    # If the explicit (Unio - DFI) case isn't met, make the result AS to ensure totality for any inputs.
    # This means misuse of this specific op (e.g. DFI - DFI) would yield AS.
    # In a full system, there might be a different subtract for DFI - DFI.
    full_def = Ite(
        And(is_i1_unio_component, i2["is_finite"]),
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # Defined case: U - DFI -> AS
        other_cases_res_AS # For all other input combinations, result is AS
    )
    return full_def


def define_raw_sub_from_Unio_Areo_aspect_canonical_result(
    i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
    result_name_prefix: str, current_omega_eff_c_smt: FNode
) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_sub_from_Unio_Areo_aspect_logic_builder(
        i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt
    )
    return res_repr


# --- Phase 3: Local Frame, Adaptive Omega, and Mappings ---
# (Copied and verified from AVC_Adaptive_Refined_Test.py)
def is_local_ZS_val(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS_val(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI_val(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
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
    op_canonical_result_definer: Callable, X_L_val_sym: FNode, Y_L_val_sym: FNode, 
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
    Res_canon_repr = op_canonical_result_definer(X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", Omega_eff_C_sym)
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
# (Copied from AVC_Adaptive_Division_Properties_Test.py - includes debug enhancements)
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
    print("====== AVC Adaptive Subtraction Interactions Test ======\n")

    P_A_val_sym = Symbol("PA_val_asub", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_asub", solver_INT_TYPE)
    
    La_val_sym = Symbol("La_val_asub", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val_asub", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val_asub", solver_INT_TYPE)

    Li1_val_sym = Symbol("Li1_val_asub", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val_asub", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val_asub", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val_asub", solver_INT_TYPE)

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S_py} (Adaptive Omega for Subtraction) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) 

        # --- L0-Sub: Foundational Soundness ---
        print(f"--- Test L0-Sub (S={current_local_span_S_py}) ---")
        s.push() # Context L0-Sub
        # L0.1 Well-definedness
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))
        premise_L0Sub = And(avc_equiv_local_val(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym),
                             avc_equiv_local_val(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        op_L0Sub_r1 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L0Sub_r1")
        op_L0Sub_r2 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L0Sub_r2")
        conc_L0Sub = avc_equiv_local_val(op_L0Sub_r1["val_L_sym"], op_L0Sub_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.1-Sub raw_sub_local_adaptive respects avc_equiv_local (S={current_local_span_S_py})",
                                     [premise_L0Sub] + op_L0Sub_r1["defining_assertions"] + op_L0Sub_r2["defining_assertions"], conc_L0Sub,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L0Sub_r1["val_L_sym"],op_L0Sub_r2["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L0Sub_r1, op_L0Sub_r2])
        s.pop() # End L0.1

        s.push() # Context L0.2
        # L0.2: Local_ZS_L - Local_DFI_L ~ Local_AS_L
        s.add_assertion(is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym)) # Lb_val_sym is DFI
        op_L02Sub = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, P_A_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L02Sub")
        conc_L02Sub = is_local_AS_val(op_L02Sub["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.2-Sub (ZS_L - DFI_L) ~ AS_L (S={current_local_span_S_py})",
                                     op_L02Sub["defining_assertions"], conc_L02Sub,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Lb_val_sym, op_L02Sub["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L02Sub])
        s.pop() # End L0.2

        s.push() # Context L0.3
        # L0.3: Local_AS_L - Local_DFI_L ~ Local_AS_L
        s.add_assertion(is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym)) # Lb_val_sym is DFI
        op_L03Sub = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, P_B_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L03Sub")
        conc_L03Sub = is_local_AS_val(op_L03Sub["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.3-Sub (AS_L - DFI_L) ~ AS_L (S={current_local_span_S_py})",
                                     op_L03Sub["defining_assertions"], conc_L03Sub,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Lb_val_sym, op_L03Sub["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L03Sub])
        s.pop() # End L0.3
        # --- End L0-Sub ---

        # General setup for other tests: La, Lb, Lc are DFI.
        # Specific tests might override this or use poles directly.
        dfi_L_abc_setup = [
            is_local_DFI_val(La_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI_val(Lc_val_sym, P_A_val_sym, P_B_val_sym)
        ]

        # --- L1-Sub: Interaction with Addition yielding Local AS ---
        print(f"\n--- Test L1-Sub: (DFI+DFI)_AS - DFI (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(dfi_L_abc_setup)
        sum_ab_L1Sub = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L1Sub_sum_ab")
        s.add_assertion(is_local_AS_val(sum_ab_L1Sub["val_L_sym"], P_B_val_sym)) # Constrain sum to be AS_L

        res_L1Sub = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, 
                                                              sum_ab_L1Sub["val_L_sym"], Lc_val_sym, 
                                                              P_A_val_sym, P_B_val_sym, "L1Sub_res")
        conc_L1Sub = is_local_AS_val(res_L1Sub["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L1-Sub (DFI+DFI)_AS - DFI_L ~ AS_L (S={current_local_span_S_py})",
                                     sum_ab_L1Sub["defining_assertions"] + res_L1Sub["defining_assertions"], conc_L1Sub,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym, sum_ab_L1Sub["val_L_sym"], res_L1Sub["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_L1Sub, res_L1Sub])
        s.pop()

        # --- L2-Sub: Interaction with Multiplication yielding Local AS ---
        print(f"\n--- Test L2-Sub: (DFI*DFI)_AS - DFI (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(dfi_L_abc_setup)
        prod_ab_L2Sub = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2Sub_prod_ab")
        s.add_assertion(is_local_AS_val(prod_ab_L2Sub["val_L_sym"], P_B_val_sym))

        res_L2Sub = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result,
                                                              prod_ab_L2Sub["val_L_sym"], Lc_val_sym,
                                                              P_A_val_sym, P_B_val_sym, "L2Sub_res")
        conc_L2Sub = is_local_AS_val(res_L2Sub["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L2-Sub (DFI*DFI)_AS - DFI_L ~ AS_L (S={current_local_span_S_py})",
                                     prod_ab_L2Sub["defining_assertions"] + res_L2Sub["defining_assertions"], conc_L2Sub,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym, prod_ab_L2Sub["val_L_sym"], res_L2Sub["val_L_sym"]],
                                     op_result_dicts_for_debug=[prod_ab_L2Sub, res_L2Sub])
        s.pop()

        # --- L3-Sub: Interaction with Division yielding Local AS ---
        print(f"\n--- Test L3-Sub: (DFI/DFI)_AS - DFI (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(dfi_L_abc_setup) # La, Lb, Lc are DFI
        div_ab_L3Sub = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3Sub_div_ab")
        s.add_assertion(is_local_AS_val(div_ab_L3Sub["val_L_sym"], P_B_val_sym)) # Constrain division to result in AS_L

        res_L3Sub = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result,
                                                              div_ab_L3Sub["val_L_sym"], Lc_val_sym, # Lc_val_sym is DFI
                                                              P_A_val_sym, P_B_val_sym, "L3Sub_res")
        conc_L3Sub = is_local_AS_val(res_L3Sub["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L3-Sub (DFI/DFI)_AS - DFI_L ~ AS_L (S={current_local_span_S_py})",
                                     div_ab_L3Sub["defining_assertions"] + res_L3Sub["defining_assertions"], conc_L3Sub,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym, div_ab_L3Sub["val_L_sym"], res_L3Sub["val_L_sym"]],
                                     op_result_dicts_for_debug=[div_ab_L3Sub, res_L3Sub])
        s.pop()

        # --- L4-Sub: Chained Subtraction from AS ---
        print(f"\n--- Test L4-Sub: (AS_L - DFI_1)_AS - DFI_2 (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym)) # Lb is DFI1
        s.add_assertion(is_local_DFI_val(Lc_val_sym, P_A_val_sym, P_B_val_sym)) # Lc is DFI2
        
        # (Local_AS_L - Lb_DFI) -> this should be Local_AS_L
        intermediate_sub_L4 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result,
                                                                        P_B_val_sym, Lb_val_sym, # AS_L - DFI1
                                                                        P_A_val_sym, P_B_val_sym, "L4Sub_inter")
        # Ensure intermediate is AS_L for clarity, though op def should ensure it if inputs are correct
        s.add_assertion(is_local_AS_val(intermediate_sub_L4["val_L_sym"], P_B_val_sym))

        final_res_L4Sub = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result,
                                                                    intermediate_sub_L4["val_L_sym"], Lc_val_sym, # (AS_L from prev step) - DFI2
                                                                    P_A_val_sym, P_B_val_sym, "L4Sub_final")
        conc_L4Sub = is_local_AS_val(final_res_L4Sub["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L4-Sub (AS_L - DFI_1)_AS - DFI_2 ~ AS_L (S={current_local_span_S_py})",
                                     intermediate_sub_L4["defining_assertions"] + final_res_L4Sub["defining_assertions"], conc_L4Sub,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Lb_val_sym,Lc_val_sym, intermediate_sub_L4["val_L_sym"], final_res_L4Sub["val_L_sym"]],
                                     op_result_dicts_for_debug=[intermediate_sub_L4, final_res_L4Sub])
        s.pop()

        # --- L5-Sub: "Illegal" First Operand for raw_sub_from_Unio_Areo_aspect ---
        # Test well-definedness: DFI_A - DFI_B using this specific subtraction
        print(f"\n--- Test L5-Sub: Well-definedness of DFI_A - DFI_B via UnioSub (S={current_local_span_S_py}) ---")
        s.push()
        # Li1, Lj1, Li2, Lj2 are all DFI for this test.
        s.add_assertion(is_local_DFI_val(Li1_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Lj1_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Li2_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        
        premise_L5Sub = And(avc_equiv_local_val(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym), # Li1=Li2 as DFIs
                             avc_equiv_local_val(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym)) # Lj1=Lj2 as DFIs

        op_L5Sub_r1 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, 
                                                                Li1_val_sym, Lj1_val_sym, # DFI - DFI
                                                                P_A_val_sym, P_B_val_sym, "L5Sub_r1")
        op_L5Sub_r2 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, 
                                                                Li2_val_sym, Lj2_val_sym, # DFI - DFI
                                                                P_A_val_sym, P_B_val_sym, "L5Sub_r2")
        conc_L5Sub = avc_equiv_local_val(op_L5Sub_r1["val_L_sym"], op_L5Sub_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        
        prove_or_find_counterexample(s, f"L5-Sub DFI_A-DFI_B (via UnioSub) respects equiv (S={current_local_span_S_py})",
                                     [premise_L5Sub] + op_L5Sub_r1["defining_assertions"] + op_L5Sub_r2["defining_assertions"], conc_L5Sub,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L5Sub_r1["val_L_sym"],op_L5Sub_r2["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L5Sub_r1, op_L5Sub_r2])
        s.pop()
        # --- End L5-Sub ---
        
        del s 
        print("-" * 80)

    print("\n====== AVC Adaptive Subtraction Interactions Test Complete ======")