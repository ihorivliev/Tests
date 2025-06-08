from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# We will focus on a local span S that demonstrates DFI compression
# when mapping to an Omega_eff_C=3 archetype. S=5 is a good candidate.
# Local DFI for S=5: {PA+1, PA+2, PA+3, PA+4}
# Omega_eff_C for S=5 is 3. Canonical DFI_C for Omega_eff_C=3 is {Fp_C(1), Fp_C(2)}.
# Mapping for S=5 to Omega_eff_C=3:
#   Local PA+1 -> Fp_C(1)
#   Local PA+2 -> Fp_C(2)
#   Local PA+3 -> Fp_C(2) (aliases with PA+2)
#   Local PA+4 -> Fp_C(2) (aliases with PA+2, PA+3)
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [5] # Focus on S=5 for this specific aliasing test. Can add more.
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

# --- Phase 3: Local Frame, Adaptive Omega, and Mappings ---
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
    defining_assertions_for_local_op.append(Implies(Res_canon_repr["is_areo"], Equals(Res_canon_repr["val"], Omega_eff_C_sym)))

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
                elif isinstance(var_item, FNode):
                    name_to_print = ""
                    if var_item.is_symbol(): name_to_print = var_item.symbol_name()
                    else: name_to_print = f"Expression({str(var_item)})"
                    value_str = "?"
                    try: value_str = str(solver.get_value(var_item))
                    except Exception: value_str = "(Error getting value)" # Should not happen if SAT
                    print(f"  {name_to_print}: {value_str}")
            
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
    print("====== AVC Adaptive Mapping Aliasing Impact Test ======\n")

    P_A_val_sym = Symbol("PA_val_alias", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_alias", solver_INT_TYPE)
    
    # Symbolic local intensity values
    La1_L_val = Symbol("La1_L_alias", solver_INT_TYPE)
    La2_L_val = Symbol("La2_L_alias", solver_INT_TYPE)
    Lb_L_val  = Symbol("Lb_L_alias", solver_INT_TYPE) # Common second operand

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        # This test is most interesting for S where mapping causes aliasing to Omega_eff_C=3 DFI.
        # S=5 is the prime candidate. S=1,2 map to Omega_eff_C=1,2 where DFI is trivial or single point.
        # S=3 maps to Omega_eff_C=3, DFI_C={1,2}. Local S=3 means DFI_L={PA+1, PA+2}.
        # PA+1 -> Fp_C(1), PA+2 -> Fp_C(2). No aliasing of distinct local DFIs for S=3.
        # So let's ensure we run for S=5.
        if current_local_span_S_py < 4: # Only run for S >= 4 to have enough local DFIs for interesting aliasing to Fp_C(2) from Omega_eff_C=3
            print(f"\n\n===== SKIPPING LOCAL SPAN S = {current_local_span_S_py} (Aliasing test more meaningful for S>=4) =====\n")
            continue

        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S_py} (Adaptive Omega, Testing Aliasing) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) 

        # --- L0-Alias: Mapping Verification ---
        # Show that for S=5: PA+2 and PA+3 both map to canonical Fp_C(2) when Omega_eff_C=3
        if current_local_span_S_py == 5: # Specific check for S=5
            print(f"--- Test L0-Alias: Mapping Verification for S=5 to Omega_eff_C=3 ---")
            s.push()
            s.add_assertion(Equals(current_local_span_S_smt, Int(5))) # Fix S=5

            local_PA_plus_2 = P_A_val_sym + Int(2)
            local_PA_plus_3 = P_A_val_sym + Int(3)

            S_for_map = P_B_val_sym - P_A_val_sym # Should be 5
            Omega_eff_C_for_map = determine_effective_canonical_omega(S_for_map) # Should be 3

            map1_repr, map1_asserts = map_local_to_adaptive_archetype_input_repr(local_PA_plus_2, P_A_val_sym, P_B_val_sym, S_for_map, Omega_eff_C_for_map, "L0_map1")
            map2_repr, map2_asserts = map_local_to_adaptive_archetype_input_repr(local_PA_plus_3, P_A_val_sym, P_B_val_sym, S_for_map, Omega_eff_C_for_map, "L0_map2")
            
            # Property: map1 is Fp_C(2) AND map2 is Fp_C(2)
            prop_L0_Alias = And(
                map1_repr["is_finite"], Equals(map1_repr["val"], Int(2)),
                map2_repr["is_finite"], Equals(map2_repr["val"], Int(2)),
                Equals(Omega_eff_C_for_map, Int(3)) # Also verify Omega_eff_C is 3
            )
            prove_or_find_counterexample(s, f"L0-Alias: Local PA+2 & PA+3 map to Fp_C(2) for S=5",
                                         map1_asserts + map2_asserts, prop_L0_Alias,
                                         model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_for_map, Omega_eff_C_for_map, local_PA_plus_2, map1_repr, local_PA_plus_3, map2_repr])
            s.pop()
        # --- End L0-Alias ---

        # --- L1-Alias: Operational Equivalence of Aliased Inputs ---
        print(f"\n--- Test L1-Alias: Ops on Aliased Inputs (S={current_local_span_S_py}) ---")
        s.push()
        # Setup: La1_L and La2_L are distinct local DFIs but map to the same canonical DFI
        # For S=5, Omega_eff_C=3. DFI_C={1,2}.
        # Local PA+2 (value=2) maps to Fp_C(2). Local PA+3 (value=3) maps to Fp_C(2).
        s.add_assertion(Equals(La1_L_val, P_A_val_sym + Int(2)))
        s.add_assertion(is_local_DFI_val(La1_L_val, P_A_val_sym, P_B_val_sym)) # Ensure PA+2 is DFI for this S
        
        s.add_assertion(Equals(La2_L_val, P_A_val_sym + Int(3)))
        s.add_assertion(is_local_DFI_val(La2_L_val, P_A_val_sym, P_B_val_sym)) # Ensure PA+3 is DFI for this S
        
        s.add_assertion(Not(Equals(La1_L_val, La2_L_val))) # Ensure they are numerically distinct local values

        # Lb_L is a different local DFI that maps to a distinct canonical DFI if possible
        s.add_assertion(Equals(Lb_L_val, P_A_val_sym + Int(1))) # Maps to Fp_C(1) for Omega_eff_C=3
        s.add_assertion(is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym))

        # Test L1.1 (Addition)
        op_L11_r1 = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, La1_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "L11_r1")
        op_L11_r2 = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, La2_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "L11_r2")
        conc_L11 = avc_equiv_local_val(op_L11_r1["val_L_sym"], op_L11_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.1-Alias Add: op(alias1,Lb) ~ op(alias2,Lb) (S={current_local_span_S_py})",
                                     op_L11_r1["defining_assertions"] + op_L11_r2["defining_assertions"], conc_L11,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La1_L_val,La2_L_val,Lb_L_val, op_L11_r1["val_L_sym"],op_L11_r2["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L11_r1, op_L11_r2])
        
        # Test L1.2 (Multiplication)
        op_L12_r1 = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La1_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "L12_r1")
        op_L12_r2 = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La2_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "L12_r2")
        conc_L12 = avc_equiv_local_val(op_L12_r1["val_L_sym"], op_L12_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.2-Alias Mul: op(alias1,Lb) ~ op(alias2,Lb) (S={current_local_span_S_py})",
                                     op_L12_r1["defining_assertions"] + op_L12_r2["defining_assertions"], conc_L12,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La1_L_val,La2_L_val,Lb_L_val, op_L12_r1["val_L_sym"],op_L12_r2["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L12_r1, op_L12_r2])

        # Test L1.3 (Division)
        op_L13_r1 = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La1_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "L13_r1")
        op_L13_r2 = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La2_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "L13_r2")
        conc_L13 = avc_equiv_local_val(op_L13_r1["val_L_sym"], op_L13_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.3-Alias Div: op(alias1,Lb) ~ op(alias2,Lb) (S={current_local_span_S_py})",
                                     op_L13_r1["defining_assertions"] + op_L13_r2["defining_assertions"], conc_L13,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La1_L_val,La2_L_val,Lb_L_val, op_L13_r1["val_L_sym"],op_L13_r2["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L13_r1, op_L13_r2])
        s.pop()
        # --- End L1-Alias ---

        del s 
        print("-" * 80)

    print("\n====== AVC Adaptive Mapping Aliasing Impact Test Complete ======")