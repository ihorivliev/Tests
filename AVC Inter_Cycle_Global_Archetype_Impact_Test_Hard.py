from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
GLOBAL_CANONICAL_OMEGA_PY_VARIANTS = [3, 7] # Test with GCA Omegas where behavior is critical

P_A1_OFFSET_PY = 0
LOCAL_SPAN_S1_PY = 5 # Span that can generate diverse k values
P_A2_OFFSET_PY = 100 
LOCAL_SPAN_S2_PY = 6
P_A3_OFFSET_PY = 200
LOCAL_SPAN_S3_PY = 7


# --- Phase 1: Foundational Definitions (Canonical AVC - for the Global Archetype) ---
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

# --- Phase 2: Canonical Raw Operations (for Global Archetype) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))
    )))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))
    )))
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
                            Ite(val_sum >= current_omega_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) 
                            )))
    return And(formulas)

def define_smart_raw_add_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any], 
                                       result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
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
                            Ite(val_prod >= current_omega_smt, And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
    return And(formulas)

def define_raw_mul_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any], 
                                 result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
    return res_repr

# --- Phase 3: Local Frame Definitions and Mappings to Global Archetype ---
def is_local_ZS_val(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS_val(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI_val(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

# --- MAPPING STRATEGIES ---
def map_local_to_global_archetype_repr_RESTRICTIVE(
    Local_val_sym: FNode, 
    PA_local_sym: FNode, PB_local_sym: FNode, S_local_sym: FNode,
    Omega_global_sym: FNode, Omega_global_py: int, # Omega_global_py for Python logic
    global_arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    global_repr = create_intensity_representation(global_arch_name_prefix)
    assertions = [global_repr["constraints"]]
    is_L_ZS = is_local_ZS_val(Local_val_sym, PA_local_sym)
    is_L_AS = is_local_AS_val(Local_val_sym, PB_local_sym)

    assertions.append(
        Ite(is_L_ZS, And(global_repr["is_zero"], Not(global_repr["is_areo"]), Not(global_repr["is_finite"])),
        Ite(is_L_AS, And(Not(global_repr["is_zero"]), global_repr["is_areo"], Not(global_repr["is_finite"])),
                     And(Not(global_repr["is_zero"]), Not(global_repr["is_areo"]), global_repr["is_finite"]))))
    
    assertions.append(Implies(global_repr["is_areo"], Equals(global_repr["val"], Omega_global_sym)))

    default_other_dfi_val_G = Ite(Omega_global_sym < Int(3), Int(1), Int(2))
    is_first_local_dfi_strict = And(S_local_sym > Int(1), Equals(Local_val_sym, PA_local_sym + Int(1)))
    is_last_local_dfi_strict  = And(S_local_sym > Int(2), Equals(Local_val_sym, PB_local_sym - Int(1))) 
    
    global_dfi_val_definition_body = \
        Ite(is_first_local_dfi_strict, 
            Ite(Omega_global_sym >= Int(2), Equals(global_repr["val"], Int(1)), FALSE()), # Map to Fp_G(1) if possible, else this path is invalid for Fp_G
        Ite(is_last_local_dfi_strict,
            Ite(Omega_global_sym > Int(2), Equals(global_repr["val"], Omega_global_sym - Int(1)), 
            Ite(Omega_global_sym >= Int(2), Equals(global_repr["val"], Int(1)), FALSE())), 
            Ite(Omega_global_sym >= Int(2), Equals(global_repr["val"], default_other_dfi_val_G), FALSE()) 
           )
        )
    assertions.append(Implies(global_repr["is_finite"], global_dfi_val_definition_body))
    assertions.append(Implies(global_repr["is_finite"], And(global_repr["val"] > Int(0), global_repr["val"] < Omega_global_sym)))
    return global_repr, assertions

def map_local_to_global_archetype_repr_BROADER(
    Local_val_sym: FNode, 
    PA_local_sym: FNode, PB_local_sym: FNode, S_local_sym: FNode, # S_local_sym not directly used in this mapping logic
    Omega_global_sym: FNode, Omega_global_py: int,
    global_arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    global_repr = create_intensity_representation(global_arch_name_prefix)
    assertions = [global_repr["constraints"]]
    is_L_ZS = is_local_ZS_val(Local_val_sym, PA_local_sym)
    is_L_AS = is_local_AS_val(Local_val_sym, PB_local_sym)
    
    # Relative local k value: k_L = Local_val_sym - PA_local_sym
    k_L_val = Local_val_sym - PA_local_sym

    # --- Define Global Kind ---
    # If local is DFI AND k_L (its relative value) is too large for global DFI, it becomes global AS
    # Otherwise, local kind maps directly to global kind
    local_dfi_becomes_global_as = And(
        is_local_DFI_val(Local_val_sym, PA_local_sym, PB_local_sym), # It's a local DFI
        k_L_val >= Omega_global_sym # But its relative value is too big for global DFI
    )
    assertions.append(
        Ite(is_L_ZS, And(global_repr["is_zero"], Not(global_repr["is_areo"]), Not(global_repr["is_finite"])),
        Ite(Or(is_L_AS, local_dfi_becomes_global_as), 
            And(Not(global_repr["is_zero"]), global_repr["is_areo"], Not(global_repr["is_finite"])),
            And(Not(global_repr["is_zero"]), Not(global_repr["is_areo"]), global_repr["is_finite"]) # Must be Local DFI mapping to Global Fp
        ))
    )
    
    # --- Define Global Value ---
    assertions.append(Implies(global_repr["is_areo"], Equals(global_repr["val"], Omega_global_sym)))
    # If it's global Fp, its value is k_L, provided k_L > 0 and k_L < Omega_global_sym
    # The k_L > 0 is implied by is_local_DFI_val. k_L < Omega_global_sym is implied by not(local_dfi_becomes_global_as).
    assertions.append(Implies(global_repr["is_finite"], Equals(global_repr["val"], k_L_val)))
    
    # Redundant final check for global Fp validity (already baked into logic above)
    assertions.append(Implies(global_repr["is_finite"], 
                              And(global_repr["val"] > Int(0), global_repr["val"] < Omega_global_sym)))
    return global_repr, assertions

# --- Phase 4: Inter-Cycle Operation Definition (Parameterized by Mapping Function) ---
def define_inter_cycle_op_result(
    op_global_canonical_result_definer: Callable, 
    mapping_function: Callable, # Either _RESTRICTIVE or _BROADER
    X_L_val_sym: FNode, PA_X_sym: FNode, PB_X_sym: FNode, S_X_sym: FNode, 
    Y_L_val_sym: FNode, PA_Y_sym: FNode, PB_Y_sym: FNode, S_Y_sym: FNode, 
    Omega_global_sym: FNode, Omega_global_py: int,
    result_name_prefix: str
) -> Dict[str, Any]: 
    all_inter_cycle_assertions = []

    X_global_repr, x_global_assertions = mapping_function(
        X_L_val_sym, PA_X_sym, PB_X_sym, S_X_sym, Omega_global_sym, Omega_global_py, f"{result_name_prefix}_xg"
    )
    all_inter_cycle_assertions.extend(x_global_assertions)

    Y_global_repr, y_global_assertions = mapping_function(
        Y_L_val_sym, PA_Y_sym, PB_Y_sym, S_Y_sym, Omega_global_sym, Omega_global_py, f"{result_name_prefix}_yg"
    )
    all_inter_cycle_assertions.extend(y_global_assertions)
   
    Res_global_repr = op_global_canonical_result_definer( 
        X_global_repr, Y_global_repr, 
        f"{result_name_prefix}_resg",
        Omega_global_sym 
    )
    all_inter_cycle_assertions.append(Res_global_repr["definition"])
    all_inter_cycle_assertions.append(Res_global_repr["constraints"]) 
    
    debug_info = {
        "X_local_val_dbg": X_L_val_sym, "PA_X_dbg": PA_X_sym, "PB_X_dbg": PB_X_sym, "S_X_dbg": S_X_sym,
        "Y_local_val_dbg": Y_L_val_sym, "PA_Y_dbg": PA_Y_sym, "PB_Y_dbg": PB_Y_sym, "S_Y_dbg": S_Y_sym,
        "X_global_repr_dbg": X_global_repr, 
        "Y_global_repr_dbg": Y_global_repr,
        "Res_global_repr_dbg": Res_global_repr, 
        "Omega_global_sym_dbg": Omega_global_sym,
        "parent_dict_name_for_debug": result_name_prefix,
        "mapping_strategy_name_dbg": mapping_function.__name__
    }
    return {
        "global_repr": Res_global_repr, 
        "defining_assertions": all_inter_cycle_assertions,
        "debug_info": debug_info
    }

# --- Phase 5: Generic Property Prover (Enhanced for Debugging Mappings) ---
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
                print("  DEBUG Global Representations & Results in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "debug_info" in op_res_dict:
                        debug_info = op_res_dict["debug_info"]
                        if isinstance(debug_info, dict) and id(debug_info) not in printed_debug_info_ids:
                            printed_debug_info_ids.add(id(debug_info)) 
                            op_name_for_print = debug_info.get("parent_dict_name_for_debug", "InterCycleOp")
                            mapping_name = debug_info.get("mapping_strategy_name_dbg", "UnknownMapping")
                            print(f"    Context for Operation Result '{op_name_for_print}' (Mapping: {mapping_name}):")
                            
                            omega_g_sym_dbg = debug_info.get('Omega_global_sym_dbg')
                            omega_g_str_dbg = f"{solver.get_value(omega_g_sym_dbg)}" if omega_g_sym_dbg and omega_g_sym_dbg in solver.get_model() else "?"
                            print(f"      Global Archetype Omega_G = {omega_g_str_dbg}")

                            for frame_prefix_dbg_key in ["X", "Y"]: 
                                pa_sym_dbg_val = debug_info.get(f"PA_{frame_prefix_dbg_key}_dbg")
                                pb_sym_dbg_val = debug_info.get(f"PB_{frame_prefix_dbg_key}_dbg")
                                s_sym_dbg_val = debug_info.get(f"S_{frame_prefix_dbg_key}_dbg")
                                lv_sym_dbg_val = debug_info.get(f"{frame_prefix_dbg_key}_local_val_dbg")
                                g_repr_dbg_val = debug_info.get(f"{frame_prefix_dbg_key}_global_repr_dbg")

                                if lv_sym_dbg_val and pa_sym_dbg_val and pb_sym_dbg_val and s_sym_dbg_val and g_repr_dbg_val :
                                    print(f"      Input {frame_prefix_dbg_key}:")
                                    lv_name_str = lv_sym_dbg_val.symbol_name() if isinstance(lv_sym_dbg_val, FNode) else 'LocalVal'
                                    pa_name_str = pa_sym_dbg_val.symbol_name() if isinstance(pa_sym_dbg_val, FNode) else 'PA'
                                    pb_name_str = pb_sym_dbg_val.symbol_name() if isinstance(pb_sym_dbg_val, FNode) else 'PB'
                                    s_name_str = s_sym_dbg_val.symbol_name() if isinstance(s_sym_dbg_val, FNode) else 'S'
                                    
                                    print(f"        Local {lv_name_str}: {solver.get_value(lv_sym_dbg_val) if lv_sym_dbg_val in solver.get_model() else '?'}")
                                    print(f"        Frame {pa_name_str}: {solver.get_value(pa_sym_dbg_val) if pa_sym_dbg_val in solver.get_model() else '?'} to {pb_name_str}: {solver.get_value(pb_sym_dbg_val) if pb_sym_dbg_val in solver.get_model() else '?'} (Span {s_name_str}: {solver.get_value(s_sym_dbg_val) if s_sym_dbg_val in solver.get_model() else '?'})")
                                    
                                    val_str_g_node = f"V={solver.get_value(g_repr_dbg_val['val'])}" if g_repr_dbg_val['val'] in solver.get_model() else "V=?"
                                    is_z_str_g_node = f"Z={solver.get_value(g_repr_dbg_val['is_zero'])}" if g_repr_dbg_val['is_zero'] in solver.get_model() else "Z=?"
                                    is_a_str_g_node = f"A={solver.get_value(g_repr_dbg_val['is_areo'])}" if g_repr_dbg_val['is_areo'] in solver.get_model() else "A=?"
                                    is_f_str_g_node = f"F={solver.get_value(g_repr_dbg_val['is_finite'])}" if g_repr_dbg_val['is_finite'] in solver.get_model() else "F=?"
                                    print(f"        Mapped Global {g_repr_dbg_val['name']}: {is_z_str_g_node}, {is_a_str_g_node}, {is_f_str_g_node}, {val_str_g_node}")

                            res_g_repr_node_dbg = debug_info.get("Res_global_repr_dbg")
                            if res_g_repr_node_dbg and isinstance(res_g_repr_node_dbg, dict) and "name" in res_g_repr_node_dbg:
                                val_str_resg_node = f"V={solver.get_value(res_g_repr_node_dbg['val'])}" if res_g_repr_node_dbg['val'] in solver.get_model() else "V=?"
                                is_z_str_resg_node = f"Z={solver.get_value(res_g_repr_node_dbg['is_zero'])}" if res_g_repr_node_dbg['is_zero'] in solver.get_model() else "Z=?"
                                is_a_str_resg_node = f"A={solver.get_value(res_g_repr_node_dbg['is_areo'])}" if res_g_repr_node_dbg['is_areo'] in solver.get_model() else "A=?"
                                is_f_str_resg_node = f"F={solver.get_value(res_g_repr_node_dbg['is_finite'])}" if res_g_repr_node_dbg['is_finite'] in solver.get_model() else "F=?"
                                print(f"      Global Result {res_g_repr_node_dbg['name']}: {is_z_str_resg_node}, {is_a_str_resg_node}, {is_f_str_resg_node}, {val_str_resg_node}")
            
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 6: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Inter-Cycle DFI Mapping Sensitivity Test ======\n")
    
    frame_A_params = {"pa_offset": P_A1_OFFSET_PY, "span": LOCAL_SPAN_S1_PY, "name_suffix": "A"} 
    frame_B_params = {"pa_offset": P_A2_OFFSET_PY, "span": LOCAL_SPAN_S2_PY, "name_suffix": "B"} 
    frame_C_params = {"pa_offset": P_A3_OFFSET_PY, "span": LOCAL_SPAN_S3_PY, "name_suffix": "C"}

    mapping_strategies = [
        ("Restrictive", map_local_to_global_archetype_repr_RESTRICTIVE),
        ("Broader    ", map_local_to_global_archetype_repr_BROADER)
    ]

    for global_omega_py in GLOBAL_CANONICAL_OMEGA_PY_VARIANTS:
        current_global_omega_smt = Int(global_omega_py)
        print(f"\n\n===== GLOBAL OMEGA = {global_omega_py} =====")

        for mapping_name_str, mapping_func_to_use in mapping_strategies:
            s = Solver(name="z3")
            print(f"\n--- Using DFI Mapping Strategy: {mapping_name_str} ---")

            # Define symbolic local values and their frame parameters
            XA_L_val = Symbol(f"XA_L_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE)
            PA_X_sym = Symbol(f"PA_X_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE); PB_X_sym = Symbol(f"PB_X_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE); S_X_sym = Symbol(f"S_X_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE)
            s.add_assertion(Equals(PA_X_sym, Int(frame_A_params["pa_offset"])))
            s.add_assertion(Equals(S_X_sym, Int(frame_A_params["span"])))
            s.add_assertion(S_X_sym > Int(0)); s.add_assertion(Equals(PB_X_sym, PA_X_sym + S_X_sym))
            s.add_assertion(And(XA_L_val >= PA_X_sym, XA_L_val <= PB_X_sym))

            YB_L_val = Symbol(f"YB_L_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE)
            PA_Y_sym = Symbol(f"PA_Y_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE); PB_Y_sym = Symbol(f"PB_Y_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE); S_Y_sym = Symbol(f"S_Y_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE)
            s.add_assertion(Equals(PA_Y_sym, Int(frame_B_params["pa_offset"])))
            s.add_assertion(Equals(S_Y_sym, Int(frame_B_params["span"])))
            s.add_assertion(S_Y_sym > Int(0)); s.add_assertion(Equals(PB_Y_sym, PA_Y_sym + S_Y_sym))
            s.add_assertion(And(YB_L_val >= PA_Y_sym, YB_L_val <= PB_Y_sym))

            ZC_L_val = Symbol(f"ZC_L_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE)
            PA_Z_sym = Symbol(f"PA_Z_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE); PB_Z_sym = Symbol(f"PB_Z_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE); S_Z_sym = Symbol(f"S_Z_go{global_omega_py}_{mapping_name_str[0]}", solver_INT_TYPE)
            s.add_assertion(Equals(PA_Z_sym, Int(frame_C_params["pa_offset"])))
            s.add_assertion(Equals(S_Z_sym, Int(frame_C_params["span"])))
            s.add_assertion(S_Z_sym > Int(0)); s.add_assertion(Equals(PB_Z_sym, PA_Z_sym + S_Z_sym))
            s.add_assertion(And(ZC_L_val >= PA_Z_sym, ZC_L_val <= PB_Z_sym))

            # Test IC-2: Distributivity: XA_G * (YB_G + ZC_G) ~ (XA_G * YB_G) + (XA_G * ZC_G)
            test_name_suffix = f"G{global_omega_py}_{mapping_name_str[0]}"
            
            sum_YB_ZC_inter_dict = define_inter_cycle_op_result(
                define_smart_raw_add_global_result, mapping_func_to_use,
                YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
                ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym,
                current_global_omega_smt, global_omega_py, f"Dist_sum_YBZC_{test_name_suffix}"
            )
            XA_global_repr, xa_global_assertions = mapping_func_to_use(
                XA_L_val, PA_X_sym, PB_X_sym, S_X_sym, current_global_omega_smt, global_omega_py, f"Dist_XA_G_{test_name_suffix}"
            )
            
            LHS_dist_global_repr = define_raw_mul_global_result(
                XA_global_repr, sum_YB_ZC_inter_dict["global_repr"],
                f"Dist_LHS_G_{test_name_suffix}", current_global_omega_smt
            )

            prod_XA_YB_inter_dict = define_inter_cycle_op_result(
                define_raw_mul_global_result, mapping_func_to_use,
                XA_L_val, PA_X_sym, PB_X_sym, S_X_sym,
                YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
                current_global_omega_smt, global_omega_py, f"Dist_prod_XAYB_{test_name_suffix}"
            )
            prod_XA_ZC_inter_dict = define_inter_cycle_op_result(
                define_raw_mul_global_result, mapping_func_to_use,
                XA_L_val, PA_X_sym, PB_X_sym, S_X_sym,
                ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym,
                current_global_omega_smt, global_omega_py, f"Dist_prod_XAZC_{test_name_suffix}"
            )
            RHS_dist_global_repr = define_smart_raw_add_global_result(
                prod_XA_YB_inter_dict["global_repr"], prod_XA_ZC_inter_dict["global_repr"],
                f"Dist_RHS_G_{test_name_suffix}", current_global_omega_smt
            )

            all_dist_assertions = sum_YB_ZC_inter_dict["defining_assertions"] + \
                                 xa_global_assertions + [XA_global_repr["constraints"]] + \
                                 [LHS_dist_global_repr["definition"], LHS_dist_global_repr["constraints"]] + \
                                 prod_XA_YB_inter_dict["defining_assertions"] + \
                                 prod_XA_ZC_inter_dict["defining_assertions"] + \
                                 [RHS_dist_global_repr["definition"], RHS_dist_global_repr["constraints"]]

            property_dist = avc_equiv_canonical(LHS_dist_global_repr, RHS_dist_global_repr)

            model_vars_dist = [
                XA_L_val, PA_X_sym, PB_X_sym, S_X_sym, 
                YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
                ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym,
                LHS_dist_global_repr, RHS_dist_global_repr
            ]
            debug_ops_dist = [sum_YB_ZC_inter_dict, 
                              prod_XA_YB_inter_dict, prod_XA_ZC_inter_dict,
                              {"debug_info": { # For LHS and RHS direct global ops
                                "X_global_repr_dbg": XA_global_repr, 
                                "Y_global_repr_dbg": sum_YB_ZC_inter_dict["global_repr"],
                                "Res_global_repr_dbg": LHS_dist_global_repr,
                                "Omega_global_sym_dbg": current_global_omega_smt,
                                "parent_dict_name_for_debug": f"Dist_LHS_Op_{test_name_suffix}",
                                "mapping_strategy_name_dbg": mapping_name_str
                                }},
                              {"debug_info": {
                                "X_global_repr_dbg": prod_XA_YB_inter_dict["global_repr"], 
                                "Y_global_repr_dbg": prod_XA_ZC_inter_dict["global_repr"],
                                "Res_global_repr_dbg": RHS_dist_global_repr,
                                "Omega_global_sym_dbg": current_global_omega_smt,
                                "parent_dict_name_for_debug": f"Dist_RHS_Op_{test_name_suffix}",
                                "mapping_strategy_name_dbg": mapping_name_str
                              }}
                             ]

            prove_or_find_counterexample(s, f"IC-Distributivity (Mapping: {mapping_name_str}, Global Omega={global_omega_py})",
                                         all_dist_assertions, property_dist,
                                         model_vars_to_print=model_vars_dist,
                                         op_result_dicts_for_debug=debug_ops_dist)
            del s
            print("-" * 40)
        print("-" * 80)

    print("\n====== AVC Inter-Cycle DFI Mapping Sensitivity Test Complete ======")