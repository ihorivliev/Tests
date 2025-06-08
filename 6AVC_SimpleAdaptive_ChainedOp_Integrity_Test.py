# Script Name: AVC_SimpleAdaptive_ChainedOp_Integrity_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Optional

# --- Configuration ---
# Test S=2 (maps to Omega_eff_C=2)
# Test S=3 (maps to Omega_eff_C=3)
# Test S=5 (maps to Omega_eff_C=3 - DFI compression from S=5 to Omega_eff_C=3)
LOCAL_SPANS_TO_TEST = [2, 3, 5] 
DEFAULT_P_A_OFFSET = 0
# Note: COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY is NOT used in this Simple Adaptive Model script.

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

# Define specific canonical result functions
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
    
def define_raw_mul_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any],
                                     result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_eff_c_smt)))
    return res_repr

def define_raw_div_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any],
                                     result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_div_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_eff_c_smt)))
    return res_repr

# --- Phase 3: Local Frame, Simple Adaptive Omega, and Mappings ---
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

def determine_effective_canonical_omega(S_val_sym: FNode) -> FNode: # Simple Adaptive
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

    kind_assertions = [arch_repr["constraints"]]
    kind_assertions.append(Implies(is_L_ZS_cond, And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_L_AS_cond, And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_L_DFI_cond, And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"])))

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
    Arch_Res_Repr: Dict[str, Any], 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, Omega_eff_C_sym: FNode 
) -> FNode:
    val_from_fp_if_omega_eff_is_1 = PB_sym 
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))
    
    val_from_fp_if_omega_eff_is_3 = \
        Ite(Equals(S_sym, Int(1)), PB_sym, 
        Ite(Equals(S_sym, Int(2)), 
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym), 
            # S_sym >= 3 (and Omega_eff_C = 3)
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), # Fp_C(1) -> PA+1
                                                     PB_sym - Int(1))  # Fp_C(2) -> PB-1 (last DFI for S>=3)
           ))

    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                      Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         val_from_fp_if_omega_eff_is_3))
                                                         
    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
                                         fp_result_val
           ))

def define_local_op_simple_adaptive_archetype_result( # Renamed for clarity
    op_canonical_result_definer_func: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: Optional[FNode], 
    P_A_val_sym: FNode, P_B_val_sym: FNode, result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    S_val_sym = P_B_val_sym - P_A_val_sym
    Omega_eff_C_sym = determine_effective_canonical_omega(S_val_sym) # Simple adaptive omega

    X_canon_repr, x_canon_assertions = map_local_to_adaptive_archetype_input_repr( # Simple mapping
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_xc")
    defining_assertions_for_local_op.extend(x_canon_assertions)
    
    Y_canon_repr_for_op = None
    Y_canon_repr_for_debug = None 
    if Y_L_val_sym is not None:
        Y_canon_repr_mapped, y_canon_assertions = map_local_to_adaptive_archetype_input_repr( # Simple mapping
            Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_yc")
        defining_assertions_for_local_op.extend(y_canon_assertions)
        Y_canon_repr_for_op = Y_canon_repr_mapped
        Y_canon_repr_for_debug = Y_canon_repr_mapped
        Res_canon_repr = op_canonical_result_definer_func( 
            X_canon_repr, Y_canon_repr_for_op, f"{result_name_prefix_local}_resc", Omega_eff_C_sym
        )
    else: 
        Res_canon_repr = op_canonical_result_definer_func( 
            X_canon_repr, None, f"{result_name_prefix_local}_resc", Omega_eff_C_sym
        )

    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])
    
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_adaptive_archetype_result_to_local( # Simple mapping
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym)
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))
    
    debug_info = {"X_L_val_dbg": X_L_val_sym, "X_canon_repr_dbg": X_canon_repr,
                  "Y_L_val_dbg": Y_L_val_sym, "Y_canon_repr_dbg": Y_canon_repr_for_debug,
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
            simple_vars_printed_this_context = set()
            for var_item in model_vars_to_print:
                if isinstance(var_item, FNode) and var_item.is_symbol():
                    if var_item.symbol_name() not in simple_vars_printed_this_context:
                        try: print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
                        except Exception: print(f"  {var_item.symbol_name()}: (Error getting value)")
                        simple_vars_printed_this_context.add(var_item.symbol_name())
                elif isinstance(var_item, dict) and "name" in var_item : 
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
                                        try: print(f"        Local Input {local_val_key.split('_')[0]}: {local_val_sym_dbg.symbol_name()} = {solver.get_value(local_val_sym_dbg)}")
                                        except Exception: print(f"        Local Input {local_val_key.split('_')[0]}: {local_val_sym_dbg.symbol_name()} = (Error getting value)")
                                
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
    print("====== AVC Simple Adaptive Chained Operation Integrity Test ======\n")

    P_A_val_sym = Symbol("PA_val_SACOI", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_SACOI", solver_INT_TYPE)
    
    A_L = Symbol("A_L_SACOI", solver_INT_TYPE)
    B_L = Symbol("B_L_SACOI", solver_INT_TYPE)
    C_L = Symbol("C_L_SACOI", solver_INT_TYPE)
    D_L = Symbol("D_L_SACOI", solver_INT_TYPE) 
    E_L = Symbol("E_L_SACOI", solver_INT_TYPE) 
    W_L = Symbol("W_L_SACOI", solver_INT_TYPE) 

    Fp1_L_coi5 = Symbol("Fp1_L_SACOI5", solver_INT_TYPE)
    Fp2_L_coi5 = Symbol("Fp2_L_SACOI5", solver_INT_TYPE)
    Fp3_L_coi5 = Symbol("Fp3_L_SACOI5", solver_INT_TYPE)


    for current_local_span_S_py in LOCAL_SPANS_TO_TEST:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        effective_omega_for_print = 3 if current_local_span_S_py >=3 else (2 if current_local_span_S_py == 2 else 1)
        print(f"\n\n===== SIMPLE ADAPTIVE CHAINED OP TESTS WITH S = {current_local_span_S_py} (maps to Omega_eff_C = {effective_omega_for_print}) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        all_local_inputs = [A_L, B_L, C_L, D_L, E_L, W_L, Fp1_L_coi5, Fp2_L_coi5, Fp3_L_coi5]
        for inp_val_sym in all_local_inputs: 
            s.add_assertion(And(inp_val_sym >= P_A_val_sym, inp_val_sym <= P_B_val_sym))

        # --- SACOI-1: FOIL-like Expansion: (A_L+B_L)*(C_L+D_L) ~ ((A_L*C_L)+(A_L*D_L)) + ((B_L*C_L)+(B_L*D_L)) ---
        s.push()
        sum_ab_c1 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L, B_L, P_A_val_sym, P_B_val_sym, "sAB_sacoi1")
        sum_cd_c1 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, C_L, D_L, P_A_val_sym, P_B_val_sym, "sCD_sacoi1")
        lhs_sacoi1 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, sum_ab_c1["val_L_sym"], sum_cd_c1["val_L_sym"], P_A_val_sym, P_B_val_sym, "lhs_sacoi1")

        prod_ac_c1 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, A_L, C_L, P_A_val_sym, P_B_val_sym, "pAC_sacoi1")
        prod_ad_c1 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, A_L, D_L, P_A_val_sym, P_B_val_sym, "pAD_sacoi1")
        prod_bc_c1 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, B_L, C_L, P_A_val_sym, P_B_val_sym, "pBC_sacoi1")
        prod_bd_c1 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, B_L, D_L, P_A_val_sym, P_B_val_sym, "pBD_sacoi1")
        sum_acad_c1 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, prod_ac_c1["val_L_sym"], prod_ad_c1["val_L_sym"], P_A_val_sym, P_B_val_sym, "sACAD_sacoi1")
        sum_bcbd_c1 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, prod_bc_c1["val_L_sym"], prod_bd_c1["val_L_sym"], P_A_val_sym, P_B_val_sym, "sBCBD_sacoi1")
        rhs_sacoi1 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, sum_acad_c1["val_L_sym"], sum_bcbd_c1["val_L_sym"], P_A_val_sym, P_B_val_sym, "rhs_sacoi1")
        
        prop_sacoi1 = avc_equiv_local_val(lhs_sacoi1["val_L_sym"], rhs_sacoi1["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_sacoi1 = (sum_ab_c1["defining_assertions"] + sum_cd_c1["defining_assertions"] + lhs_sacoi1["defining_assertions"] +
                        prod_ac_c1["defining_assertions"] + prod_ad_c1["defining_assertions"] + prod_bc_c1["defining_assertions"] + prod_bd_c1["defining_assertions"] +
                        sum_acad_c1["defining_assertions"] + sum_bcbd_c1["defining_assertions"] + rhs_sacoi1["defining_assertions"])
        prove_or_find_counterexample(s, f"SACOI-1 FOIL-like (S={current_local_span_S_py})", setup_sacoi1, prop_sacoi1,
                                     [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,D_L,lhs_sacoi1["val_L_sym"],rhs_sacoi1["val_L_sym"]], 
                                     op_result_dicts_for_debug=[sum_ab_c1, sum_cd_c1, lhs_sacoi1, prod_ac_c1, prod_ad_c1, prod_bc_c1, prod_bd_c1, sum_acad_c1, sum_bcbd_c1, rhs_sacoi1])
        s.pop()

        # --- SACOI-2: Zero Chain: (((A_L*B_L)/B_L)-A_L)*C_L ~ ZS_L ---
        if current_local_span_S_py >= 2: 
            s.push()
            s.add_assertion(is_local_DFI_val(B_L, P_A_val_sym, P_B_val_sym)) 
            
            prod_ab_c2 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, A_L, B_L, P_A_val_sym, P_B_val_sym, "pAB_sacoi2")
            div_pab_b_c2 = define_local_op_simple_adaptive_archetype_result(define_raw_div_canonical_result, prod_ab_c2["val_L_sym"], B_L, P_A_val_sym, P_B_val_sym, "dAB_B_sacoi2")
            sub_term_a_c2 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_sub_canonical_result, div_pab_b_c2["val_L_sym"], A_L, P_A_val_sym, P_B_val_sym, "sT_A_sacoi2")
            lhs_sacoi2 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, sub_term_a_c2["val_L_sym"], C_L, P_A_val_sym, P_B_val_sym, "lhs_sacoi2")

            prop_sacoi2 = is_local_ZS_val(lhs_sacoi2["val_L_sym"], P_A_val_sym)
            setup_sacoi2 = (prod_ab_c2["defining_assertions"] + div_pab_b_c2["defining_assertions"] + 
                            sub_term_a_c2["defining_assertions"] + lhs_sacoi2["defining_assertions"])
            prove_or_find_counterexample(s, f"SACOI-2 Zero Chain (B_L is DFI) (S={current_local_span_S_py})", setup_sacoi2, prop_sacoi2,
                                         [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,lhs_sacoi2["val_L_sym"]],
                                         op_result_dicts_for_debug=[prod_ab_c2, div_pab_b_c2, sub_term_a_c2, lhs_sacoi2])
            s.pop()
        else:
            print(f"--- SKIPPING SACOI-2 for S={current_local_span_S_py} (Requires DFI for B_L) ---")

        # --- SACOI-3: Mixed Add/Sub: (A_L+B_L)-C_L ~ A_L+(B_L-C_L) ---
        s.push()
        sum_ab_c3 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L, B_L, P_A_val_sym, P_B_val_sym, "sAB_sacoi3")
        lhs_sacoi3 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_sub_canonical_result, sum_ab_c3["val_L_sym"], C_L, P_A_val_sym, P_B_val_sym, "lhs_sacoi3")
        sub_bc_c3 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_sub_canonical_result, B_L, C_L, P_A_val_sym, P_B_val_sym, "sBC_sacoi3")
        rhs_sacoi3 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L, sub_bc_c3["val_L_sym"], P_A_val_sym, P_B_val_sym, "rhs_sacoi3")
        prop_sacoi3 = avc_equiv_local_val(lhs_sacoi3["val_L_sym"], rhs_sacoi3["val_L_sym"], P_A_val_sym, P_B_val_sym) # Corrected variable name
        setup_sacoi3 = (sum_ab_c3["defining_assertions"] + lhs_sacoi3["defining_assertions"] + 
                        sub_bc_c3["defining_assertions"] + rhs_sacoi3["defining_assertions"])
        prove_or_find_counterexample(s, f"SACOI-3 Mixed Add/Sub (S={current_local_span_S_py})", setup_sacoi3, prop_sacoi3,
                                     [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,lhs_sacoi3["val_L_sym"],rhs_sacoi3["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_c3, lhs_sacoi3, sub_bc_c3, rhs_sacoi3])
        s.pop()
        
        # --- SACOI-5: Iterated Subtraction from Areo: (((AS_L - Fp1_L) - Fp2_L) - Fp3_L) ~ AS_L ---
        if current_local_span_S_py >= 4: 
            s.push()
            s.add_assertion(Equals(Fp1_L_coi5, P_A_val_sym + Int(1)))
            s.add_assertion(Equals(Fp2_L_coi5, P_A_val_sym + Int(2)))
            s.add_assertion(Equals(Fp3_L_coi5, P_A_val_sym + Int(3)))
            s.add_assertion(is_local_DFI_val(Fp1_L_coi5, P_A_val_sym, P_B_val_sym))
            s.add_assertion(is_local_DFI_val(Fp2_L_coi5, P_A_val_sym, P_B_val_sym))
            s.add_assertion(is_local_DFI_val(Fp3_L_coi5, P_A_val_sym, P_B_val_sym))

            term1_c5 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_sub_canonical_result, P_B_val_sym, Fp1_L_coi5, P_A_val_sym, P_B_val_sym, "t1_sacoi5")
            term2_c5 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_sub_canonical_result, term1_c5["val_L_sym"], Fp2_L_coi5, P_A_val_sym, P_B_val_sym, "t2_sacoi5")
            lhs_sacoi5 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_sub_canonical_result, term2_c5["val_L_sym"], Fp3_L_coi5, P_A_val_sym, P_B_val_sym, "lhs_sacoi5")
            
            prop_sacoi5 = is_local_AS_val(lhs_sacoi5["val_L_sym"], P_B_val_sym)
            setup_sacoi5 = (term1_c5["defining_assertions"] + term2_c5["defining_assertions"] + lhs_sacoi5["defining_assertions"])
            prove_or_find_counterexample(s, f"SACOI-5 Iterated Sub from AS_L ~ AS_L (S={current_local_span_S_py})", setup_sacoi5, prop_sacoi5,
                                         [P_A_val_sym,P_B_val_sym,Fp1_L_coi5,Fp2_L_coi5,Fp3_L_coi5,lhs_sacoi5["val_L_sym"]], 
                                         op_result_dicts_for_debug=[term1_c5, term2_c5, lhs_sacoi5])
            s.pop()
        else:
            print(f"--- SKIPPING SACOI-5 for S={current_local_span_S_py} (Requires S>=4 for 3 distinct DFIs) ---")

        # --- SACOI-6: Path Dependence from Additive Non-Associativity ---
        if current_local_span_S_py >= 3: 
            s.push()
            s.add_assertion(is_local_DFI_val(A_L, P_A_val_sym, P_B_val_sym)) 
            s.add_assertion(is_local_DFI_val(B_L, P_A_val_sym, P_B_val_sym)) 
            s.add_assertion(is_local_DFI_val(C_L, P_A_val_sym, P_B_val_sym)) 
            s.add_assertion(is_local_DFI_val(W_L, P_A_val_sym, P_B_val_sym)) 

            sum_ab_c6 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L, B_L, P_A_val_sym, P_B_val_sym, "sAB_sacoi6")
            lhs_add_c6 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, sum_ab_c6["val_L_sym"], C_L, P_A_val_sym, P_B_val_sym, "lhsAdd_sacoi6")
            sum_bc_c6 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, B_L, C_L, P_A_val_sym, P_B_val_sym, "sBC_sacoi6")
            rhs_add_c6 = define_local_op_simple_adaptive_archetype_result(define_smart_raw_add_canonical_result, A_L, sum_bc_c6["val_L_sym"], P_A_val_sym, P_B_val_sym, "rhsAdd_sacoi6")
            
            # SACOI-6.1: (LHS_add) * W_L ~ (RHS_add) * W_L
            lhs_mul_c6 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, lhs_add_c6["val_L_sym"], W_L, P_A_val_sym, P_B_val_sym, "lhsMul_sacoi6")
            rhs_mul_c6 = define_local_op_simple_adaptive_archetype_result(define_raw_mul_canonical_result, rhs_add_c6["val_L_sym"], W_L, P_A_val_sym, P_B_val_sym, "rhsMul_sacoi6")
            prop_sacoi61 = avc_equiv_local_val(lhs_mul_c6["val_L_sym"], rhs_mul_c6["val_L_sym"], P_A_val_sym, P_B_val_sym)
            setup_sacoi61 = (sum_ab_c6["defining_assertions"] + lhs_add_c6["defining_assertions"] + sum_bc_c6["defining_assertions"] + rhs_add_c6["defining_assertions"] +
                             lhs_mul_c6["defining_assertions"] + rhs_mul_c6["defining_assertions"]) # Corrected variable name
            prove_or_find_counterexample(s, f"SACOI-6.1 PathDepMul (S={current_local_span_S_py})", setup_sacoi61, 
                                         prop_sacoi61, # Corrected variable name
                                         [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,W_L,lhs_add_c6["val_L_sym"],rhs_add_c6["val_L_sym"],lhs_mul_c6["val_L_sym"],rhs_mul_c6["val_L_sym"]],
                                         op_result_dicts_for_debug=[sum_ab_c6,lhs_add_c6,sum_bc_c6,rhs_add_c6,lhs_mul_c6,rhs_mul_c6])

            # SACOI-6.2: (LHS_add) / W_L ~ (RHS_add) / W_L (W_L is DFI already constrained)
            lhs_div_c6 = define_local_op_simple_adaptive_archetype_result(define_raw_div_canonical_result, lhs_add_c6["val_L_sym"], W_L, P_A_val_sym, P_B_val_sym, "lhsDiv_sacoi6")
            rhs_div_c6 = define_local_op_simple_adaptive_archetype_result(define_raw_div_canonical_result, rhs_add_c6["val_L_sym"], W_L, P_A_val_sym, P_B_val_sym, "rhsDiv_sacoi6")
            prop_sacoi62 = avc_equiv_local_val(lhs_div_c6["val_L_sym"], rhs_div_c6["val_L_sym"], P_A_val_sym, P_B_val_sym)
            setup_sacoi62 = (sum_ab_c6["defining_assertions"] + lhs_add_c6["defining_assertions"] + sum_bc_c6["defining_assertions"] + rhs_add_c6["defining_assertions"] +
                             lhs_div_c6["defining_assertions"] + rhs_div_c6["defining_assertions"]) 
            prove_or_find_counterexample(s, f"SACOI-6.2 PathDepDiv (S={current_local_span_S_py})", setup_sacoi62, prop_sacoi62,
                                         [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,W_L,lhs_add_c6["val_L_sym"],rhs_add_c6["val_L_sym"],lhs_div_c6["val_L_sym"],rhs_div_c6["val_L_sym"]],
                                         op_result_dicts_for_debug=[sum_ab_c6,lhs_add_c6,sum_bc_c6,rhs_add_c6,lhs_div_c6,rhs_div_c6])
            s.pop()
        else:
            print(f"--- SKIPPING SACOI-6 for S={current_local_span_S_py} (Additive non-assoc stress test for S>=3 in Simple Adaptive) ---")

        del s
        print("-" * 80)

    print("\n====== AVC Simple Adaptive Chained Operation Integrity Test Complete ======")