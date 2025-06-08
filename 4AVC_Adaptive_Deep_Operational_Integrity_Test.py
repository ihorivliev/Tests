from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [2, 3, 5, 7] # Test S=2 (Omega_eff_C=2) and S>=3 (Omega_eff_C=7)
DEFAULT_P_A_OFFSET = 0 
COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY = 7 # For Model 3b

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
    is_i1_unio_component = Or(i1["is_zero"], i1["is_areo"])
    result_as_AS_C = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]))
    
    full_def = Ite(
        And(is_i1_unio_component, i2["is_finite"]), # Condition: i1 is Unio, i2 is DFI
        result_as_AS_C,                             # THEN result is AS_C
        result_as_AS_C                              # ELSE (for ALL OTHER input combinations) result is also AS_C
    )
    return full_def

def define_raw_sub_from_Unio_Areo_aspect_canonical_result(
    i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
    result_name_prefix: str, current_omega_eff_c_smt: FNode
) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_sub_from_Unio_Areo_aspect_logic_builder(
        i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

# --- Phase 3: Local Frame, Complex Adaptive Omega, and Mappings ---
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

def determine_effective_canonical_omega_complex(S_val_sym: FNode, complex_omega_smt: FNode) -> FNode:
    return Ite(Equals(S_val_sym, Int(1)), Int(1),
           Ite(Equals(S_val_sym, Int(2)), Int(2),
                                           complex_omega_smt)) 

def map_local_to_complex_adaptive_archetype_input_repr(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode, complex_omega_py_val: int, 
    arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    arch_repr = create_intensity_representation(arch_name_prefix)
    is_L_ZS_cond = is_local_ZS_val(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS_val(Local_val_sym, PB_sym)
    is_L_DFI_cond = is_local_DFI_val(Local_val_sym, PA_sym, PB_sym)
    kind_assertions = [arch_repr["constraints"]]
    kind_assertions.append(Implies(is_L_ZS_cond, And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_L_AS_cond, And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_L_DFI_cond, And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"])))
    val_assertions = [Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym))]
    k_L_val = Local_val_sym - PA_sym
    val_if_omega_eff_is_2 = Int(1)
    cap_val_for_complex_dfi = Int(complex_omega_py_val - 1)
    val_if_omega_eff_is_complex_mapped = Ite(k_L_val > cap_val_for_complex_dfi, 
                                             cap_val_for_complex_dfi, 
                                             Ite(k_L_val <= Int(0), Int(1), k_L_val))
    val_assertions.append(
        Implies(arch_repr["is_finite"], 
            Ite(Equals(Omega_eff_C_sym, Int(1)), FALSE(), 
            Ite(Equals(Omega_eff_C_sym, Int(2)), Equals(arch_repr["val"], val_if_omega_eff_is_2),
                 Equals(arch_repr["val"], val_if_omega_eff_is_complex_mapped)))))
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))
    return arch_repr, kind_assertions + val_assertions

def map_complex_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode, complex_omega_py_val: int
) -> FNode:
    val_from_fp_if_omega_eff_is_1 = PB_sym 
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))
    # For Omega_eff_C = complex_omega_py_val (e.g. 7)
    # Arch_Res_Repr["val"] is v_C from [1, complex_omega_py_val-1]
    # We want to map v_C back to a local DFI PA_sym + k_L, where PA_sym + k_L < PB_sym
    # The forward mapping was k_L -> min(k_L, complex_omega_py_val-1)
    # Reverse: if v_C < complex_omega_py_val-1, then k_L = v_C. Local = PA_sym + v_C
    # If v_C = complex_omega_py_val-1, k_L could have been >= complex_omega_py_val-1. Map to PB_sym-1 (last local DFI).
    val_if_fp_from_omega_eff_is_complex = Ite(
        Equals(Arch_Res_Repr["val"], Int(complex_omega_py_val - 1)),
        PB_sym - Int(1), # Map canonical max DFI to local max DFI
        PA_sym + Arch_Res_Repr["val"] # Other canonical DFIs map based on their value
    )
    # This needs to be capped if PA_sym + Arch_Res_Repr["val"] >= PB_sym, or if PB_sym - Int(1) <= PA_sym
    # Corrected robust reverse mapping for Fp_C from complex archetype:
    val_from_fp_if_omega_eff_is_complex_robust = Ite(S_sym <= Int(1), PB_sym, # No local DFI if S=1
        Ite(PA_sym + Arch_Res_Repr["val"] < PB_sym, # Can we map PA + v_C directly?
            PA_sym + Arch_Res_Repr["val"],
            PB_sym - Int(1) # Otherwise, map to last possible local DFI (if S>1)
        )
    )
    # Ensure that if S=2 and Omega_eff_C=7, Fp_C(>1) from Omega_eff_C=7 should map to PB_sym for S=2.
    # The val_from_fp_if_omega_eff_is_complex logic needs to be carefully nested with S_sym checks like in map_adaptive_archetype_result_to_local
    map_val_complex = Ite(Equals(S_sym, Int(1)), PB_sym, # No local DFI
                      Ite(Equals(S_sym, Int(2)), # Local DFI is {PA+1}
                          Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym), # Fp_C(1) from Omega=7 maps to PA+1 for S=2. Others to PB.
                          # Else S_sym >= 3. Max local DFI is PB-1.
                          # Map canonical Arch_Res_Repr["val"] (which is in 1..complex_omega_py_val-1)
                          # to a value in [PA+1 .. PB-1]
                          Ite(PA_sym + Arch_Res_Repr["val"] < PB_sym, 
                              PA_sym + Arch_Res_Repr["val"], 
                              PB_sym - Int(1)) # Cap at PB-1 if PA+val is too large or if val is large
                         )
                     )

    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                    Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         map_val_complex))

    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
               fp_result_val 
           ))

def define_local_op_complex_adaptive_archetype_result(
    op_canonical_result_definer: Callable, X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    S_val_sym = P_B_val_sym - P_A_val_sym
    complex_omega_smt = Int(COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY)
    Omega_eff_C_sym = determine_effective_canonical_omega_complex(S_val_sym, complex_omega_smt)
    X_canon_repr, x_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, f"{result_name_prefix_local}_xc")
    defining_assertions_for_local_op.extend(x_canon_assertions)
    Y_canon_repr, y_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, f"{result_name_prefix_local}_yc")
    defining_assertions_for_local_op.extend(y_canon_assertions)
    Res_canon_repr = op_canonical_result_definer(X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", Omega_eff_C_sym)
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])
    defining_assertions_for_local_op.append(Implies(Res_canon_repr["is_areo"], Equals(Res_canon_repr["val"], Omega_eff_C_sym)))
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_complex_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY)
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
    # (Copied from previous script, includes robust FNode printing)
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
    print("====== AVC Adaptive Deep Operational Integrity Test ======\n")

    P_A_val_sym = Symbol("PA_val_adoi", solver_INT_TYPE) # adoi for Adaptive Deep Op Integrity
    P_B_val_sym = Symbol("PB_val_adoi", solver_INT_TYPE)
    
    La_L_val = Symbol("La_L_adoi", solver_INT_TYPE)
    Lb_L_val = Symbol("Lb_L_adoi", solver_INT_TYPE)
    Lc_L_val = Symbol("Lc_L_adoi", solver_INT_TYPE)
    Ld_L_val = Symbol("Ld_L_adoi", solver_INT_TYPE)
    Le_L_val = Symbol("Le_L_adoi", solver_INT_TYPE)


    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        complex_omega_smt_val = Int(COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY) # For mapping funcs
        
        print(f"\n\n===== LOCAL SPAN S = {current_local_span_S_py} (Complex Adaptive Omega for Deep Ops) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) 

        # General setup for inputs to be valid local values
        general_L_inputs_setup = [
            And(La_L_val >= P_A_val_sym, La_L_val <= P_B_val_sym),
            And(Lb_L_val >= P_A_val_sym, Lb_L_val <= P_B_val_sym),
            And(Lc_L_val >= P_A_val_sym, Lc_L_val <= P_B_val_sym),
            And(Ld_L_val >= P_A_val_sym, Ld_L_val <= P_B_val_sym),
            And(Le_L_val >= P_A_val_sym, Le_L_val <= P_B_val_sym),
        ]
        s.add_assertions(general_L_inputs_setup)

        # --- Test DOI-1: Pole Propagation through mixed ops ---
        # Res_L = (((P_A + La_DFI) * P_B) / Lb_DFI) -sub Lc_DFI 
        # Expected Res_L ~ P_B if La_DFI, Lb_DFI, Lc_DFI are 'standard' DFIs
        print(f"--- Test DOI-1: Pole Propagation (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(is_local_DFI_val(La_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Lc_L_val, P_A_val_sym, P_B_val_sym))

        # Step 1: term1_add = P_A_val_sym +_LCA La_L_val
        term1_add = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, P_A_val_sym, La_L_val, P_A_val_sym, P_B_val_sym, "doi1_t1add")
        # Step 2: term2_mul = term1_add *_LCA P_B_val_sym
        term2_mul = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, term1_add["val_L_sym"], P_B_val_sym, P_A_val_sym, P_B_val_sym, "doi1_t2mul")
        # Step 3: term3_div = term2_mul /_LCA Lb_L_val
        term3_div = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, term2_mul["val_L_sym"], Lb_L_val, P_A_val_sym, P_B_val_sym, "doi1_t3div")
        # Step 4: res_L_doi1 = term3_div -_sub_LCA Lc_L_val
        res_L_doi1 = define_local_op_complex_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, term3_div["val_L_sym"], Lc_L_val, P_A_val_sym, P_B_val_sym, "doi1_res")
        
        prop_doi1 = is_local_AS_val(res_L_doi1["val_L_sym"], P_B_val_sym)
        all_doi1_assertions = term1_add["defining_assertions"] + term2_mul["defining_assertions"] + term3_div["defining_assertions"] + res_L_doi1["defining_assertions"]
        
        prove_or_find_counterexample(s, f"DOI-1 Pole Propagation (S={current_local_span_S_py})",
                                     all_doi1_assertions, prop_doi1,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_L_val, Lb_L_val, Lc_L_val, 
                                                          term1_add["val_L_sym"], term2_mul["val_L_sym"], term3_div["val_L_sym"], res_L_doi1["val_L_sym"]],
                                     op_result_dicts_for_debug=[term1_add, term2_mul, term3_div, res_L_doi1])
        s.pop()

        # --- Test DOI-2: Associativity Interaction with Division ---
        # Test: ( (La_L +_LCA Lb_L) /_LCA Ld_L ) +_LCA Lc_L  ~_L  ( La_L +_LCA (Lb_L /_LCA Ld_L) ) +_LCA Lc_L
        # This specific formulation wasn't ideal. A better test of interaction:
        # Test: ( (La_L +_LCA Lb_L) +_LCA Lc_L ) /_LCA Ld_L ~_L ( La_L +_LCA (Lb_L +_LCA Lc_L) ) /_LCA Ld_L
        print(f"\n--- Test DOI-2: Additive Associativity under Division (S={current_local_span_S_py}) ---")
        s.push()
        # For this test, let all be DFIs to stress additive non-associativity
        s.add_assertion(is_local_DFI_val(La_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Lc_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Ld_L_val, P_A_val_sym, P_B_val_sym)) # Divisor also DFI

        # LHS path
        sum_ab_doi2 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "doi2_sum_ab")
        sum_abc_lhs_doi2 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, sum_ab_doi2["val_L_sym"], Lc_L_val, P_A_val_sym, P_B_val_sym, "doi2_sum_abc_lhs")
        lhs_doi2 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, sum_abc_lhs_doi2["val_L_sym"], Ld_L_val, P_A_val_sym, P_B_val_sym, "doi2_lhs")

        # RHS path
        sum_bc_doi2 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "doi2_sum_bc")
        sum_abc_rhs_doi2 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, La_L_val, sum_bc_doi2["val_L_sym"], P_A_val_sym, P_B_val_sym, "doi2_sum_abc_rhs")
        rhs_doi2 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, sum_abc_rhs_doi2["val_L_sym"], Ld_L_val, P_A_val_sym, P_B_val_sym, "doi2_rhs")
        
        prop_doi2 = avc_equiv_local_val(lhs_doi2["val_L_sym"], rhs_doi2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        all_doi2_assertions = sum_ab_doi2["defining_assertions"] + sum_abc_lhs_doi2["defining_assertions"] + lhs_doi2["defining_assertions"] + \
                              sum_bc_doi2["defining_assertions"] + sum_abc_rhs_doi2["defining_assertions"] + rhs_doi2["defining_assertions"]
        
        prove_or_find_counterexample(s, f"DOI-2 AddAssoc under Div (S={current_local_span_S_py})",
                                     all_doi2_assertions, prop_doi2,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_L_val,Lb_L_val,Lc_L_val,Ld_L_val, 
                                                          sum_abc_lhs_doi2["val_L_sym"], sum_abc_rhs_doi2["val_L_sym"], # sums before div
                                                          lhs_doi2["val_L_sym"], rhs_doi2["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_doi2, sum_abc_lhs_doi2, lhs_doi2, sum_bc_doi2, sum_abc_rhs_doi2, rhs_doi2])
        s.pop()

        # --- Test DOI-3: Subtraction "Zeroing" attempt in a chain ---
        # Test: ( (La_DFI *_LCA Lb_DFI) /_LCA Lb_DFI ) -_sub_LCA La_DFI ~_L P_A (Local ZS)
        # This tests if the result of a potential cancellation (La*Lb)/Lb simplifies to La,
        # and then if La -sub La results in ZS_L. We know La -sub La (misuse) results in AS_L (~ZS_L).
        # So the core is whether (La*Lb)/Lb results in La.
        print(f"\n--- Test DOI-3: Subtraction Zeroing Chain (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(is_local_DFI_val(La_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym)) # Lb is DFI for division

        term1_mul_doi3 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "doi3_t1mul")
        term2_div_doi3 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, term1_mul_doi3["val_L_sym"], Lb_L_val, P_A_val_sym, P_B_val_sym, "doi3_t2div")
        
        # We need to test if term2_div_doi3 is ~_L La_L_val first. Let's call this result "potential_La"
        # Then, res_L_doi3 = potential_La -_sub_LCA La_L_val
        # This is too complex for a single property. Let's test intermediate.
        
        # Test 1: Does (La_DFI * Lb_DFI) / Lb_DFI simplify to La_DFI? (Cancellation RD-3 for this adaptive model)
        # This is L4-Div-CA from previous script. Expected FAIL generally for S>=3.
        prop_doi3_cancel = avc_equiv_local_val(term2_div_doi3["val_L_sym"], La_L_val, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"DOI-3.1 Cancellation (La*Lb)/Lb ~ La (S={current_local_span_S_py})",
                                     term1_mul_doi3["defining_assertions"] + term2_div_doi3["defining_assertions"], prop_doi3_cancel,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_L_val,Lb_L_val, term1_mul_doi3["val_L_sym"], term2_div_doi3["val_L_sym"]],
                                     op_result_dicts_for_debug=[term1_mul_doi3, term2_div_doi3])
        
        # Test 2: Assuming the above term simplifies to some 'X_res'. Does X_res -_sub_LCA La_L_val ~ P_A_val_sym?
        # If X_res is DFI, then DFI - DFI (misuse of sub) -> AS_L ~ ZS_L.
        # If X_res is AS_L (e.g. if cancellation failed and result was AS_L), then AS_L - DFI -> AS_L ~ ZS_L.
        # So this part should always yield something ~ ZS_L if La_L_val is DFI.
        res_L_doi3_sub = define_local_op_complex_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, 
                                                                           term2_div_doi3["val_L_sym"], La_L_val, # Subtracting original La_L
                                                                           P_A_val_sym, P_B_val_sym, "doi3_res_sub")
        prop_doi3_final = avc_equiv_local_val(res_L_doi3_sub["val_L_sym"], P_A_val_sym, P_A_val_sym, P_B_val_sym) # Check against ZS_L
        
        prove_or_find_counterexample(s, f"DOI-3.2 ((La*Lb)/Lb) -sub La ~ ZS_L (S={current_local_span_S_py})",
                                     term1_mul_doi3["defining_assertions"] + term2_div_doi3["defining_assertions"] + res_L_doi3_sub["defining_assertions"], 
                                     prop_doi3_final,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_L_val,Lb_L_val, term1_mul_doi3["val_L_sym"], term2_div_doi3["val_L_sym"], res_L_doi3_sub["val_L_sym"]],
                                     op_result_dicts_for_debug=[term1_mul_doi3, term2_div_doi3, res_L_doi3_sub])
        s.pop()

        del s 
        print("-" * 80)

    print("\n====== AVC Adaptive Deep Operational Integrity Test Complete ======")