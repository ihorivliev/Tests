# Script Name: AVC_General_Addition_ComplexAdaptive_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7, 10]
DEFAULT_P_A_OFFSET = 0
COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY = 7 # Omega for the richer archetype when S >= 3

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
    # Case 1: i1 is ZS_C
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), # ZS + ZS -> ZS
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)), # ZS + AS -> AS
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) # ZS + Fp -> Fp
    )))
    # Case 2: i1 is AS_C
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)), # AS + ZS -> AS
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)), # AS + AS -> AS
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) # AS + Fp -> Fp
    )))
    # Case 3: i1 is Fp_C
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), # Fp + ZS -> Fp
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), # Fp + AS -> Fp
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), # Fp + Fp
                            Ite(val_sum >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)), # Sum >= Omega -> AS
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) # Sum < Omega -> Fp
                            )))
    return And(formulas)

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"]
    # Annihilation by Zero
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) )) # ZS * X -> ZS
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) )) # X * ZS -> ZS (if X not ZS)

    # Areo interactions (excluding ZS which is covered above)
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]), # AS * AS -> AS
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]), # AS * Fp
                            Ite(i2["val"] > Int(0), # AS * Fp(>0) -> AS
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) # Should not happen if Fp means val > 0
                               )))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]), # Fp * AS
                            Ite(i1["val"] > Int(0), # Fp(>0) * AS -> AS
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) # Should not happen
                               )))
    # Finite * Finite
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_prod >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)), # Prod >= Omega -> AS
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)) # Prod < Omega -> Fp
                               )))
    return And(formulas)

def define_smart_raw_add_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any],
                                          result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_eff_c_smt)))
    return res_repr

def define_raw_mul_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any],
                                     result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_eff_c_smt)))
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
                                        complex_omega_smt)) # Default to complex_omega_smt for S >= 3

def map_local_to_complex_adaptive_archetype_input_repr(
    Local_val_sym: FNode,
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, # S_sym is P_B-P_A
    Omega_eff_C_sym: FNode, complex_omega_py_val: int, # complex_omega_py_val is the Python int for Omega_eff_C when S_sym >=3
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
    
    # DFI Value Mapping
    # k_L_val is the 1-based step from PA_sym for a local DFI. (e.g., PA+1 -> k_L=1, PA+2 -> k_L=2)
    k_L_val = Local_val_sym - PA_sym 
    
    # Mapping for Omega_eff_C_sym == 1 (No Finites in Canon)
    map_to_false_if_omega_is_1 = FALSE() # arch_repr["is_finite"] should be false

    # Mapping for Omega_eff_C_sym == 2 (Canon DFI is Fp_C(1))
    map_to_fp1_if_omega_is_2 = Equals(arch_repr["val"], Int(1))
    
    # Mapping for Omega_eff_C_sym == complex_omega_py_val (e.g., 7)
    # Local DFI k_L_val maps to canonical min(k_L_val, complex_omega_py_val - 1)
    # Ensure canonical val is > 0. If k_L_val itself is 0 or less, is_L_DFI_cond would be false.
    cap_val_for_complex_dfi = Int(complex_omega_py_val - 1)
    val_if_omega_eff_is_complex_mapped = Ite(k_L_val > cap_val_for_complex_dfi,
                                             cap_val_for_complex_dfi,
                                             Ite(k_L_val <= Int(0), Int(1), k_L_val)) # Ensure positive, default to 1 if k_L is non-positive (though is_L_DFI implies k_L > 0)

    val_assertions.append(
        Implies(arch_repr["is_finite"],
            Ite(Equals(Omega_eff_C_sym, Int(1)), map_to_false_if_omega_is_1, 
            Ite(Equals(Omega_eff_C_sym, Int(2)), map_to_fp1_if_omega_is_2,
                                                Equals(arch_repr["val"], val_if_omega_eff_is_complex_mapped) # Default to complex mapping rules
            )))
    )
    # Ensure canonical finite value is within its bounds (redundant if mapping logic is correct, but good for safety)
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))
    
    return arch_repr, kind_assertions + val_assertions

def map_complex_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any],
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, # S_sym is P_B-P_A
    Omega_eff_C_sym: FNode, complex_omega_py_val: int # complex_omega_py_val is the Python int for Omega_eff_C when S_sym >=3
) -> FNode:
    # If canonical result is ZS_C -> map to Local PA_sym (ZS_L)
    # If canonical result is AS_C -> map to Local PB_sym (AS_L)
    
    # If canonical result is Fp_C(v_C):
    # Case 1: Omega_eff_C_sym was 1 (No Fp_C possible, Arch_Res_Repr["is_finite"] would be False. If somehow true, map to AS_L)
    val_from_fp_if_omega_eff_is_1 = PB_sym 
    
    # Case 2: Omega_eff_C_sym was 2 (Fp_C(1) is the only possibility)
    #   If local S=1 (no local DFI), map Fp_C(1) to PB_sym (AS_L).
    #   If local S>=2 (local DFI PA_sym+1 exists), map Fp_C(1) to PA_sym+1.
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))
                                     
    # Case 3: Omega_eff_C_sym was complex_omega_py_val (e.g., 7)
    #   Arch_Res_Repr["val"] is v_C, where 0 < v_C < complex_omega_py_val.
    #   Attempt to map v_C back to PA_sym + v_C.
    #   If PA_sym + v_C >= PB_sym (i.e., exceeds local DFI range for current S_sym), map to PB_sym-1 (last DFI step).
    #   This handles cases where S_sym < complex_omega_py_val, so canonical DFI range is richer.
    #   Example: S_sym=3 (DFI={PA+1,PA+2}). Omega_eff_C=7. Canon.Result Fp_C(4). Map back to PA+(PB-PA-1) = PB-1 = PA+2.
    #   Example: S_sym=5. Omega_eff_C=7. Canon.Result Fp_C(6). Map back to PA+6 if 0+6 < 5 (false), so PB-1 = PA+4.
    #   Example: S_sym=10. Omega_eff_C=7. Canon.Result Fp_C(6). Map back to PA+6 if 0+6 < 10 (true), so PA+6.
    map_val_complex = Ite(Equals(S_sym, Int(1)), PB_sym, # No local DFI
                     Ite(Equals(S_sym, Int(2)), # Local DFI is PA+1
                         Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), # Fp_C(1) -> PA+1
                                                                 PB_sym), # Should not happen if Omega_eff_C=2
                         # S_sym >= 3, Omega_eff_C is complex_omega_py_val (e.g. 7)
                         Ite( (PA_sym + Arch_Res_Repr["val"]) < PB_sym, # Does PA_sym + v_C fit in local DFI?
                              PA_sym + Arch_Res_Repr["val"],
                              PB_sym - Int(1)) # Cap at last local DFI step
                        ))

    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                      Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         map_val_complex)) # Default to complex mapping rules
                                                         
    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
                                         fp_result_val
           ))

def define_local_op_complex_adaptive_archetype_result(
    op_canonical_result_definer_func: Callable, # e.g., define_smart_raw_add_canonical_result
    X_L_val_sym: FNode, Y_L_val_sym: FNode,
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
    
    Res_canon_repr = op_canonical_result_definer_func( 
        X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", Omega_eff_C_sym
    )
    # Constraints for Res_canon_repr (e.g. AS val = Omega_eff_C) are handled within op_canonical_result_definer_func
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"]) 
    
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
            # Print PA, PB, S etc. if they are simple FNodes passed in model_vars_to_print
            simple_vars_printed_this_context = set()
            for var_item in model_vars_to_print:
                if isinstance(var_item, FNode) and var_item.is_symbol():
                    if var_item.symbol_name() not in simple_vars_printed_this_context:
                        print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
                        simple_vars_printed_this_context.add(var_item.symbol_name())
                elif isinstance(var_item, dict) and "name" in var_item : # For intensity_repr dicts
                    if var_item['name'] not in simple_vars_printed_this_context:
                        val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                        is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                        is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                        is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                        print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                        simple_vars_printed_this_context.add(var_item['name'])
            
            if op_result_dicts_for_debug:
                print("  DEBUG Canonical Mappings/Results in Counterexample:")
                printed_debug_info_ids = set()
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
                                    if local_val_sym_dbg and local_val_sym_dbg in solver.get_model(): 
                                        print(f"        Local Input {local_val_key.split('_')[0]}: {local_val_sym_dbg.symbol_name()} = {solver.get_value(local_val_sym_dbg)}")
                                
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
    print("====== AVC General Addition Complex Adaptive Test ======\n")

    P_A_val_sym = Symbol("PA_val_gaddcadap", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_gaddcadap", solver_INT_TYPE)
    
    # For general tests GADD-CAdap-0,1,2,3,4,5,6,7,8
    A_L_val = Symbol("A_L_gaddcadap", solver_INT_TYPE)
    B_L_val = Symbol("B_L_gaddcadap", solver_INT_TYPE)
    C_L_val = Symbol("C_L_gaddcadap", solver_INT_TYPE) # For 3-operand tests
    
    # For GADD-CAdap-0 (Well-definedness)
    A1_L_val = Symbol("A1_L_gaddcadap", solver_INT_TYPE)
    A2_L_val = Symbol("A2_L_gaddcadap", solver_INT_TYPE)
    B1_L_val = Symbol("B1_L_gaddcadap", solver_INT_TYPE)
    B2_L_val = Symbol("B2_L_gaddcadap", solver_INT_TYPE)

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        effective_omega_for_print = COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY if current_local_span_S_py >=3 else (2 if current_local_span_S_py == 2 else 1)
        print(f"\n\n===== COMPLEX ADAPTIVE ADDITION TESTS WITH Local Span S = {current_local_span_S_py} (maps to Omega_eff_C = {effective_omega_for_print}) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        all_adaptive_test_inputs = [A_L_val, B_L_val, C_L_val, A1_L_val, A2_L_val, B1_L_val, B2_L_val]
        for inp_val_sym in all_adaptive_test_inputs:
            s.add_assertion(And(inp_val_sym >= P_A_val_sym, inp_val_sym <= P_B_val_sym))
        
        # --- GADD-CAdap-0: Well-Definedness ---
        s.push()
        prem_gadd_cadap0 = And(avc_equiv_local_val(A1_L_val, A2_L_val, P_A_val_sym, P_B_val_sym),
                                avc_equiv_local_val(B1_L_val, B2_L_val, P_A_val_sym, P_B_val_sym))
        res1_gadd0 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A1_L_val, B1_L_val, P_A_val_sym, P_B_val_sym, f"r1ca_ga0_S{current_local_span_S_py}")
        res2_gadd0 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A2_L_val, B2_L_val, P_A_val_sym, P_B_val_sym, f"r2ca_ga0_S{current_local_span_S_py}")
        conc_gadd0 = avc_equiv_local_val(res1_gadd0["val_L_sym"], res2_gadd0["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gadd0 = [prem_gadd_cadap0] + res1_gadd0["defining_assertions"] + res2_gadd0["defining_assertions"]
        prove_or_find_counterexample(s, f"GADD-CAdap-0 Well-Defined (S={current_local_span_S_py})", setup_gadd0, conc_gadd0, 
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A1_L_val, A2_L_val, B1_L_val, B2_L_val, res1_gadd0["val_L_sym"], res2_gadd0["val_L_sym"]],
                                     op_result_dicts_for_debug=[res1_gadd0, res2_gadd0])
        s.pop()

        # --- GADD-CAdap-1: ZS_L + A_L ~ A_L ---
        s.push()
        res_gadd1 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, P_A_val_sym, A_L_val, P_A_val_sym, P_B_val_sym, f"r_ga1ca_S{current_local_span_S_py}")
        prop_gadd1 = avc_equiv_local_val(res_gadd1["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"GADD-CAdap-1 ZS_L + A_L ~ A_L (S={current_local_span_S_py})", res_gadd1["defining_assertions"], prop_gadd1,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gadd1["val_L_sym"]], op_result_dicts_for_debug=[res_gadd1])
        s.pop()

        # --- GADD-CAdap-2: A_L + ZS_L ~ A_L ---
        s.push()
        res_gadd2 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, P_A_val_sym, P_A_val_sym, P_B_val_sym, f"r_ga2ca_S{current_local_span_S_py}")
        prop_gadd2 = avc_equiv_local_val(res_gadd2["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"GADD-CAdap-2 A_L + ZS_L ~ A_L (S={current_local_span_S_py})", res_gadd2["defining_assertions"], prop_gadd2,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gadd2["val_L_sym"]], op_result_dicts_for_debug=[res_gadd2])
        s.pop()

        # --- GADD-CAdap-3: AS_L + A_L ~ ExpectedResult_L ---
        # Expected: if A_L is ZS_L or AS_L -> AS_L. If A_L is DFI_L -> A_L (mapped back from Fp_C).
        s.push()
        res_gadd3 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, P_B_val_sym, A_L_val, P_A_val_sym, P_B_val_sym, f"r_ga3ca_S{current_local_span_S_py}")
        # Expected result is tricky: if A_L maps to ZS_C or AS_C, canonical result is AS_C -> local AS_L.
        # If A_L maps to Fp_C, canonical result is Fp_C -> local A_L (potentially transformed by mapping).
        # So, this tests AS_L + A_L ~ A_L (if A_L is DFI/ZS) or ~AS_L (if A_L is AS). More simply, just check AS_L + A_L behavior.
        # Let's check AS_L + A_L ~ (ZS_L + A_L) since AS_L ~ ZS_L
        # This would be op(AS_L, A_L) ~ op(ZS_L, A_L) which is part of well-definedness.
        # The most direct test is against the known smart_raw_add rules:
        # AS_C + ZS_C -> AS_C
        # AS_C + AS_C -> AS_C
        # AS_C + Fp_C -> Fp_C
        # Local Target Construction:
        # Map A_L to A_C. If A_C is ZS_C or AS_C, target is AS_L. If A_C is Fp_C, target is A_L (after mapping back if A_C became result).
        # This is complex to formulate as a simple target, let's use the well-definedness approach using ZS_L.
        res_gadd3_compare_with_zs = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, P_A_val_sym, A_L_val, P_A_val_sym, P_B_val_sym, f"r_ga3comp_S{current_local_span_S_py}")
        prop_gadd3 = avc_equiv_local_val(res_gadd3["val_L_sym"], res_gadd3_compare_with_zs["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gadd3 = res_gadd3["defining_assertions"] + res_gadd3_compare_with_zs["defining_assertions"]
        prove_or_find_counterexample(s, f"GADD-CAdap-3 AS_L + A_L ~ (ZS_L+A_L) (S={current_local_span_S_py})", setup_gadd3, prop_gadd3,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gadd3["val_L_sym"], res_gadd3_compare_with_zs["val_L_sym"]], 
                                     op_result_dicts_for_debug=[res_gadd3, res_gadd3_compare_with_zs])
        s.pop()
        
        # --- GADD-CAdap-4: A_L + AS_L ~ ExpectedResult_L --- (Similar to GADD-CAdap-3 due to commutativity)
        s.push()
        res_gadd4 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, P_B_val_sym, P_A_val_sym, P_B_val_sym, f"r_ga4ca_S{current_local_span_S_py}")
        res_gadd4_compare_with_zs = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, P_A_val_sym, P_A_val_sym, P_B_val_sym, f"r_ga4comp_S{current_local_span_S_py}")
        prop_gadd4 = avc_equiv_local_val(res_gadd4["val_L_sym"], res_gadd4_compare_with_zs["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gadd4 = res_gadd4["defining_assertions"] + res_gadd4_compare_with_zs["defining_assertions"]
        prove_or_find_counterexample(s, f"GADD-CAdap-4 A_L + AS_L ~ (A_L+ZS_L) (S={current_local_span_S_py})", setup_gadd4, prop_gadd4,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gadd4["val_L_sym"], res_gadd4_compare_with_zs["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_gadd4, res_gadd4_compare_with_zs])
        s.pop()

        # --- GADD-CAdap-5: Commutativity: A_L + B_L ~ B_L + A_L ---
        s.push()
        res1_gadd5 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"r1_ga5ca_S{current_local_span_S_py}")
        res2_gadd5 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, B_L_val, A_L_val, P_A_val_sym, P_B_val_sym, f"r2_ga5ca_S{current_local_span_S_py}")
        prop_gadd5 = avc_equiv_local_val(res1_gadd5["val_L_sym"], res2_gadd5["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gadd5 = res1_gadd5["defining_assertions"] + res2_gadd5["defining_assertions"]
        prove_or_find_counterexample(s, f"GADD-CAdap-5 Commutativity (S={current_local_span_S_py})", setup_gadd5, prop_gadd5,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, B_L_val, res1_gadd5["val_L_sym"], res2_gadd5["val_L_sym"]],
                                     op_result_dicts_for_debug=[res1_gadd5, res2_gadd5])
        s.pop()

        # --- GADD-CAdap-6: Associativity: (A_L + B_L) + C_L ~ A_L + (B_L + C_L) ---
        # This test uses DFI inputs for A, B, C to stress the property
        s.push()
        s.add_assertion(is_local_DFI_val(A_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(B_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(C_L_val, P_A_val_sym, P_B_val_sym))

        sum_ab_gadd6 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"sumAB_ga6ca_S{current_local_span_S_py}")
        lhs_gadd6 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, sum_ab_gadd6["val_L_sym"], C_L_val, P_A_val_sym, P_B_val_sym, f"lhs_ga6ca_S{current_local_span_S_py}")
        sum_bc_gadd6 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, B_L_val, C_L_val, P_A_val_sym, P_B_val_sym, f"sumBC_ga6ca_S{current_local_span_S_py}")
        rhs_gadd6 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, sum_bc_gadd6["val_L_sym"], P_A_val_sym, P_B_val_sym, f"rhs_ga6ca_S{current_local_span_S_py}")
        prop_gadd6 = avc_equiv_local_val(lhs_gadd6["val_L_sym"], rhs_gadd6["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gadd6 = sum_ab_gadd6["defining_assertions"] + lhs_gadd6["defining_assertions"] + sum_bc_gadd6["defining_assertions"] + rhs_gadd6["defining_assertions"]
        prove_or_find_counterexample(s, f"GADD-CAdap-6 Associativity (DFIs) (S={current_local_span_S_py})", setup_gadd6, prop_gadd6,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,B_L_val,C_L_val,sum_ab_gadd6["val_L_sym"],lhs_gadd6["val_L_sym"],sum_bc_gadd6["val_L_sym"],rhs_gadd6["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_gadd6,lhs_gadd6,sum_bc_gadd6,rhs_gadd6])
        s.pop()
        
        # --- GADD-CAdap-7: Left Distributivity: C_L * (A_L + B_L) ~ (C_L*A_L) + (C_L*B_L) ---
        s.push()
        s.add_assertion(is_local_DFI_val(A_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(B_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(C_L_val, P_A_val_sym, P_B_val_sym)) # Multiplier C_L also DFI

        sum_ab_gadd7 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"sumAB_ga7ca_S{current_local_span_S_py}")
        lhs_gadd7 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, C_L_val, sum_ab_gadd7["val_L_sym"], P_A_val_sym, P_B_val_sym, f"lhs_ga7ca_S{current_local_span_S_py}")
        
        prod_ca_gadd7 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, C_L_val, A_L_val, P_A_val_sym, P_B_val_sym, f"prodCA_ga7ca_S{current_local_span_S_py}")
        prod_cb_gadd7 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, C_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"prodCB_ga7ca_S{current_local_span_S_py}")
        rhs_gadd7 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, prod_ca_gadd7["val_L_sym"], prod_cb_gadd7["val_L_sym"], P_A_val_sym, P_B_val_sym, f"rhs_ga7ca_S{current_local_span_S_py}")
        prop_gadd7 = avc_equiv_local_val(lhs_gadd7["val_L_sym"], rhs_gadd7["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gadd7 = sum_ab_gadd7["defining_assertions"] + lhs_gadd7["defining_assertions"] + prod_ca_gadd7["defining_assertions"] + prod_cb_gadd7["defining_assertions"] + rhs_gadd7["defining_assertions"]
        prove_or_find_counterexample(s, f"GADD-CAdap-7 Left Distributivity (DFIs) (S={current_local_span_S_py})", setup_gadd7, prop_gadd7,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,B_L_val,C_L_val,lhs_gadd7["val_L_sym"],rhs_gadd7["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_gadd7,lhs_gadd7,prod_ca_gadd7,prod_cb_gadd7,rhs_gadd7])
        s.pop()

        # --- GADD-CAdap-8: Right Distributivity: (A_L + B_L) * C_L ~ (A_L*C_L) + (B_L*C_L) ---
        s.push()
        s.add_assertion(is_local_DFI_val(A_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(B_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(C_L_val, P_A_val_sym, P_B_val_sym))

        sum_ab_gadd8 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"sumAB_ga8ca_S{current_local_span_S_py}")
        lhs_gadd8 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, sum_ab_gadd8["val_L_sym"], C_L_val, P_A_val_sym, P_B_val_sym, f"lhs_ga8ca_S{current_local_span_S_py}")

        prod_ac_gadd8 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A_L_val, C_L_val, P_A_val_sym, P_B_val_sym, f"prodAC_ga8ca_S{current_local_span_S_py}")
        prod_bc_gadd8 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, B_L_val, C_L_val, P_A_val_sym, P_B_val_sym, f"prodBC_ga8ca_S{current_local_span_S_py}")
        rhs_gadd8 = define_local_op_complex_adaptive_archetype_result(define_smart_raw_add_canonical_result, prod_ac_gadd8["val_L_sym"], prod_bc_gadd8["val_L_sym"], P_A_val_sym, P_B_val_sym, f"rhs_ga8ca_S{current_local_span_S_py}")
        prop_gadd8 = avc_equiv_local_val(lhs_gadd8["val_L_sym"], rhs_gadd8["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gadd8 = sum_ab_gadd8["defining_assertions"] + lhs_gadd8["defining_assertions"] + prod_ac_gadd8["defining_assertions"] + prod_bc_gadd8["defining_assertions"] + rhs_gadd8["defining_assertions"]
        prove_or_find_counterexample(s, f"GADD-CAdap-8 Right Distributivity (DFIs) (S={current_local_span_S_py})", setup_gadd8, prop_gadd8,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,B_L_val,C_L_val,lhs_gadd8["val_L_sym"],rhs_gadd8["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_gadd8,lhs_gadd8,prod_ac_gadd8,prod_bc_gadd8,rhs_gadd8])
        s.pop()

        del s
        print("-" * 80)

    print("\n====== AVC General Addition Complex Adaptive Test Complete ======")