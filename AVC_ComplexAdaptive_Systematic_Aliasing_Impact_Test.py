# Script Name: AVC_ComplexAdaptive_Systematic_Aliasing_Impact_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Optional

# --- Configuration ---
# Requirement 2 (Deeper Dive): Systematic Aliasing Impact in Complex Adaptive Model
# Focus on S > Omega_eff_C-1 where Omega_eff_C = 7 (i.e., S > 6)
LOCAL_SPANS_TO_TEST = [8, 10] 
DEFAULT_P_A_OFFSET = 0
COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY = 7 

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
                                      i1_canon_repr: Dict[str, Any], i2_canon_repr: Optional[Dict[str, Any]], # i2 can be None for unary
                                      result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    # For binary operations, i2_canon_repr should not be None.
    # This simplified version assumes i2_canon_repr is provided for binary ops.
    if i2_canon_repr is None and op_logic_builder_func.__name__ not in ["some_unary_op_logic_builder"]: # Example
        raise ValueError(f"i2_canon_repr cannot be None for binary operation {op_logic_builder_func.__name__}")
        
    res_repr["definition"] = op_logic_builder_func(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
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
    map_to_false_if_omega_is_1 = FALSE()
    map_to_fp1_if_omega_is_2 = Equals(arch_repr["val"], Int(1))
    
    cap_val_for_complex_dfi = Int(complex_omega_py_val - 1)
    # Ensure k_L_val used for mapping is positive, default to 1 if it somehow became <=0 for DFI.
    # is_L_DFI_cond implies k_L_val > 0.
    val_if_omega_eff_is_complex_mapped = Ite(k_L_val > cap_val_for_complex_dfi,
                                             cap_val_for_complex_dfi, # Capped value
                                             Ite(k_L_val <= Int(0), Int(1), k_L_val)) # k_L if not capped and >0, else 1 (safety for non-DFI values)
    
    val_assertions.append(
        Implies(arch_repr["is_finite"],
            Ite(Equals(Omega_eff_C_sym, Int(1)), map_to_false_if_omega_is_1,
            Ite(Equals(Omega_eff_C_sym, Int(2)), map_to_fp1_if_omega_is_2,
                                                Equals(arch_repr["val"], val_if_omega_eff_is_complex_mapped)
            )))
    )
    # This final constraint ensures the canonical finite value is valid for its Omega_eff_C_sym
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))
    return arch_repr, kind_assertions + val_assertions

def map_complex_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any],
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode,
    Omega_eff_C_sym: FNode, complex_omega_py_val: int
) -> FNode:
    val_from_fp_if_omega_eff_is_1 = PB_sym
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))
    
    # S_sym >= 3, Omega_eff_C_sym is complex_omega_py_val (e.g. 7)
    # Arch_Res_Repr["val"] is v_C from [1, complex_omega_py_val - 1]
    map_val_complex = Ite(Equals(S_sym, Int(1)), PB_sym, # No local DFI
                     Ite(Equals(S_sym, Int(2)), # Local DFI is PA+1
                         Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), 
                                                                 PB_sym), # Should only get Fp_C(1) if Omega_eff_C was 2
                         # S_sym >= 3
                         Ite( (PA_sym + Arch_Res_Repr["val"]) < PB_sym, # Does PA_sym + v_C fit in local DFI?
                              PA_sym + Arch_Res_Repr["val"],
                              PB_sym - Int(1)) # Cap at last local DFI step (PB-1), only if S_sym >= 2 for DFI to exist.
                        ))

    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                      Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         map_val_complex))
                                                         
    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
                                         fp_result_val
           ))

def define_local_op_complex_adaptive_archetype_result(
    op_canonical_definer_func: Callable,
    X_L_val_sym: FNode, Y_L_val_sym: Optional[FNode], 
    P_A_val_sym: FNode, P_B_val_sym: FNode, result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    S_val_sym = P_B_val_sym - P_A_val_sym
    complex_omega_smt = Int(COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY)
    Omega_eff_C_sym = determine_effective_canonical_omega_complex(S_val_sym, complex_omega_smt)

    X_canon_repr, x_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, f"{result_name_prefix_local}_xc")
    defining_assertions_for_local_op.extend(x_canon_assertions)
    
    Y_canon_repr_for_op = None
    Y_canon_repr_for_debug = None
    if Y_L_val_sym is not None:
        Y_canon_repr, y_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
            Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, f"{result_name_prefix_local}_yc")
        defining_assertions_for_local_op.extend(y_canon_assertions)
        Y_canon_repr_for_op = Y_canon_repr
        Y_canon_repr_for_debug = Y_canon_repr
    
    Res_canon_repr = op_canonical_definer_func( 
        X_canon_repr, Y_canon_repr_for_op, f"{result_name_prefix_local}_resc", Omega_eff_C_sym
    )

    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])
    
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_complex_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY)
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
    print("====== AVC Complex Adaptive Systematic Aliasing Impact Test ======\n")

    P_A_val_sym = Symbol("PA_val_CompAlias", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_CompAlias", solver_INT_TYPE)
    
    La1_L_val = Symbol("La1_L_CompAlias", solver_INT_TYPE) 
    La2_L_val = Symbol("La2_L_CompAlias", solver_INT_TYPE) 
    Lb_L_val  = Symbol("Lb_L_CompAlias", solver_INT_TYPE)

    op_definers_map = {
        "Add": lambda i1, i2, name, omega: define_operation_canonical_result(smart_raw_add_logic_builder, i1, i2, name, omega),
        "Sub": lambda i1, i2, name, omega: define_operation_canonical_result(smart_raw_sub_canonical_logic_builder, i1, i2, name, omega),
        "Mul": lambda i1, i2, name, omega: define_operation_canonical_result(raw_mul_logic_builder, i1, i2, name, omega),
        "Div": lambda i1, i2, name, omega: define_operation_canonical_result(raw_div_logic_builder, i1, i2, name, omega),
    }

    for current_local_span_S_py in LOCAL_SPANS_TO_TEST:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        
        if current_local_span_S_py < 3: continue 
        
        effective_omega_py = COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY
        effective_omega_smt = Int(effective_omega_py)

        print(f"\n\n===== COMPLEX ADAPTIVE ALIASING (S={current_local_span_S_py}, maps to Omega_eff_C={effective_omega_py}) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        max_canon_fp_val = effective_omega_py - 1
        
        # Define pairs of aliased inputs (La1_L, La2_L) for the current span S
        # These are local k_L values that map to the same canonical Fp_C due to capping
        # We are interested in k_L values that are > max_canon_fp_val but < current_local_span_S_py
        aliased_pairs_kL_values = []
        if current_local_span_S_py > max_canon_fp_val + 1: # Need at least two distinct k_L that cap
            # Example: S=8, max_canon_fp=6. kL1=6 (maps to Fp_C(6)), kL2=7 (maps to Fp_C(6))
            aliased_pairs_kL_values.append( (max_canon_fp_val, max_canon_fp_val + 1) )
            if current_local_span_S_py > max_canon_fp_val + 2:
                # Example: S=10, max_canon_fp=6
                # Pair 1: kL1=6, kL2=7 (both map to Fp_C(6)) - already added if S>=8
                # Pair 2: kL1=7, kL2=8 (both map to Fp_C(6))
                aliased_pairs_kL_values.append( (max_canon_fp_val + 1, max_canon_fp_val + 2) )
                if current_local_span_S_py > max_canon_fp_val + 3: # S=10 -> max_canon_fp+3 = 9
                     aliased_pairs_kL_values.append( (max_canon_fp_val + 2, max_canon_fp_val + 3) )


        if not aliased_pairs_kL_values:
            print(f"--- No suitable DFI aliasing pairs for S={current_local_span_S_py} that cap to Fp_C({max_canon_fp_val}). Skipping aliasing tests for this span. ---")
            del s
            continue

        # Define common third operands Lb_L
        Lb_operands_specs = []
        Lb_operands_specs.append({"name": "Lb_is_ZS", "k_L_val_py": 0})
        Lb_operands_specs.append({"name": "Lb_is_AS", "k_L_val_py": current_local_span_S_py})
        if current_local_span_S_py >= 2: 
            Lb_operands_specs.append({"name": "Lb_is_Fp1", "k_L_val_py": 1})
        if current_local_span_S_py >= 4 : # Ensure PA+3 is valid DFI and distinct enough
            Lb_operands_specs.append({"name": "Lb_is_FpMid", "k_L_val_py": 3})
        if current_local_span_S_py >= 7 : # Ensure PA+6 is valid DFI
            Lb_operands_specs.append({"name": "Lb_is_FpMaxCanon", "k_L_val_py": max_canon_fp_val})


        for kL1_py, kL2_py in aliased_pairs_kL_values:
            la1_val_py = DEFAULT_P_A_OFFSET + kL1_py
            la2_val_py = DEFAULT_P_A_OFFSET + kL2_py
            
            # Ensure these k_L values are valid DFI steps for the current span S
            if not (1 <= kL1_py < current_local_span_S_py and 1 <= kL2_py < current_local_span_S_py):
                continue

            print(f"\n--- Testing Aliased Pair: La1_L (local k_L={kL1_py}) vs La2_L (local k_L={kL2_py}) ---")
            s.push() 

            s.add_assertion(Equals(La1_L_val, P_A_val_sym + Int(kL1_py)))
            s.add_assertion(Equals(La2_L_val, P_A_val_sym + Int(kL2_py)))
            s.add_assertion(is_local_DFI_val(La1_L_val, P_A_val_sym, P_B_val_sym))
            s.add_assertion(is_local_DFI_val(La2_L_val, P_A_val_sym, P_B_val_sym))
            s.add_assertion(Not(Equals(La1_L_val, La2_L_val))) # Ensure they are numerically distinct local values
            
            # Mapping Check (Optional, for debugging the test setup itself)
            s.push()
            map_la1_repr, map_la1_asserts = map_local_to_complex_adaptive_archetype_input_repr(La1_L_val, P_A_val_sym, P_B_val_sym, current_local_span_S_smt, effective_omega_smt, effective_omega_py, "chk_La1_map")
            map_la2_repr, map_la2_asserts = map_local_to_complex_adaptive_archetype_input_repr(La2_L_val, P_A_val_sym, P_B_val_sym, current_local_span_S_smt, effective_omega_smt, effective_omega_py, "chk_La2_map")
            # Both should map to Fp_C(max_canon_fp_val) if they are capped, or their respective min(k,max_canon_fp_val)
            # The key is that map_la1_repr["val"] should equal map_la2_repr["val"]
            map_check_prop = And(map_la1_repr["is_finite"], map_la2_repr["is_finite"], Equals(map_la1_repr["val"], map_la2_repr["val"]))
            map_check_setup = map_la1_asserts + map_la2_asserts
            prove_or_find_counterexample(s, f"  Mapping Check: La1_L(k={kL1_py}), La2_L(k={kL2_py}) map to same Canon Fp_Val",
                                         map_check_setup, map_check_prop, 
                                         model_vars_to_print=[P_A_val_sym, P_B_val_sym, La1_L_val, map_la1_repr, La2_L_val, map_la2_repr],
                                         print_model_on_fail=True) # Crucial to see if mapping is as expected
            s.pop()


            for lb_spec in Lb_operands_specs:
                # Ensure Lb is valid for current span
                if not (0 <= lb_spec["k_L_val_py"] <= current_local_span_S_py): continue
                # Ensure Lb_L is not one of the aliased inputs if it's a DFI, to avoid A op A situations directly
                if lb_spec["name"] not in ["Lb_is_ZS", "Lb_is_AS"]:
                    if lb_spec["k_L_val_py"] == kL1_py or lb_spec["k_L_val_py"] == kL2_py:
                        continue

                s.push() 
                s.add_assertion(Equals(Lb_L_val, P_A_val_sym + Int(lb_spec["k_L_val_py"])))
                if lb_spec["name"] == "Lb_is_ZS": s.add_assertion(is_local_ZS_val(Lb_L_val, P_A_val_sym))
                elif lb_spec["name"] == "Lb_is_AS": s.add_assertion(is_local_AS_val(Lb_L_val, P_B_val_sym))
                else: s.add_assertion(is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym))

                for op_name_str, op_definer_lambda in op_definers_map.items():
                    test_id_suffix = f"S{current_local_span_S_py}_La1k{kL1_py}vsLa2k{kL2_py}_{lb_spec['name']}_{op_name_str}"
                    
                    op_r1 = define_local_op_complex_adaptive_archetype_result(op_definer_lambda, La1_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, f"r1_{test_id_suffix}")
                    op_r2 = define_local_op_complex_adaptive_archetype_result(op_definer_lambda, La2_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, f"r2_{test_id_suffix}")
                    conc = avc_equiv_local_val(op_r1["val_L_sym"], op_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
                    
                    property_title = f"OpEquiv {op_name_str} (Lb={lb_spec['name']}): op(kL={kL1_py},Lb)~op(kL={kL2_py},Lb)"
                    prove_or_find_counterexample(s, property_title,
                                                 op_r1["defining_assertions"] + op_r2["defining_assertions"], conc,
                                                 model_vars_to_print=[P_A_val_sym,P_B_val_sym,La1_L_val,La2_L_val,Lb_L_val, op_r1["val_L_sym"],op_r2["val_L_sym"]],
                                                 op_result_dicts_for_debug=[op_r1, op_r2])
                s.pop() 
            s.pop() 
        del s
        print("-" * 80)

    print("\n====== AVC Complex Adaptive Systematic Aliasing Impact Test Complete ======")