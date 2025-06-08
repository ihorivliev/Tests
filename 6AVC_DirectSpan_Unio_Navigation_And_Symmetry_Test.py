# Script Name: AVC_DirectSpan_Unio_Navigation_And_Symmetry_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Optional

# --- Configuration ---
LOCAL_SPANS_TO_TEST = [3, 5, 7] 
DEFAULT_P_A_OFFSET = 0

# --- Phase 1: Foundational Definitions (Canonical AVC - used by Direct Span) ---
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

def define_canonical_op_result(op_logic_builder_func: Callable,
                               i1_canon_repr: Dict[str, Any], i2_canon_repr: Optional[Dict[str, Any]], 
                               result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    if i2_canon_repr is None and op_logic_builder_func.__name__ not in ["some_unary_op_logic_builder_if_we_had_one"]: 
        raise ValueError(f"i2_canon_repr cannot be None for binary operation {op_logic_builder_func.__name__}")
    res_repr["definition"] = op_logic_builder_func(i1_canon_repr, i2_canon_repr, res_repr, current_omega_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_smt)))
    return res_repr

# --- Phase 3: Local Frame (Direct Span Model) Definitions ---
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

def map_local_val_to_canonical_repr_direct_span(
    Local_val_sym: FNode, PA_sym: FNode, S_canonical_omega_sym: FNode, arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    arch_repr = create_intensity_representation(arch_name_prefix)
    k_L_val = Local_val_sym - PA_sym 
    is_Canon_ZS_cond = Equals(k_L_val, Int(0))
    is_Canon_AS_cond = Equals(k_L_val, S_canonical_omega_sym)
    is_Canon_Fp_cond = And(k_L_val > Int(0), k_L_val < S_canonical_omega_sym)
    
    kind_assertions = [arch_repr["constraints"]]
    kind_assertions.append(Implies(is_Canon_ZS_cond, And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_Canon_AS_cond, And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_Canon_Fp_cond, And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"])))
    
    val_assertions = [Implies(arch_repr["is_areo"], Equals(arch_repr["val"], S_canonical_omega_sym))]
    val_assertions.append(Implies(arch_repr["is_finite"], Equals(arch_repr["val"], k_L_val)))
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < S_canonical_omega_sym)))
    
    return arch_repr, kind_assertions + val_assertions

def map_canonical_repr_to_local_val_direct_span(
    Arch_Res_Repr: Dict[str, Any], PA_sym: FNode, S_canonical_omega_sym: FNode 
) -> FNode:
    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PA_sym + S_canonical_omega_sym, 
                                         PA_sym + Arch_Res_Repr["val"] 
           ))

def define_local_op_direct_span_result(
    op_logic_builder_func: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode,
    P_A_val_sym: FNode, P_B_val_sym: FNode, result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    S_val_sym = P_B_val_sym - P_A_val_sym 

    X_canon_repr, x_canon_assertions = map_local_val_to_canonical_repr_direct_span(
        X_L_val_sym, P_A_val_sym, S_val_sym, f"{result_name_prefix_local}_xc")
    defining_assertions_for_local_op.extend(x_canon_assertions)
    
    Y_canon_repr, y_canon_assertions = map_local_val_to_canonical_repr_direct_span(
        Y_L_val_sym, P_A_val_sym, S_val_sym, f"{result_name_prefix_local}_yc")
    defining_assertions_for_local_op.extend(y_canon_assertions)
    
    Res_canon_repr = define_canonical_op_result(op_logic_builder_func, 
        X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", S_val_sym 
    )
    defining_assertions_for_local_op.append(Res_canon_repr["definition"]) 
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"]) 
    
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_canonical_repr_to_local_val_direct_span(
        Res_canon_repr, P_A_val_sym, S_val_sym)
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))
    
    debug_info = {"X_L_val_dbg": X_L_val_sym, "X_canon_repr_dbg": X_canon_repr,
                  "Y_L_val_dbg": Y_L_val_sym, "Y_canon_repr_dbg": Y_canon_repr,
                  "Res_canon_repr_dbg": Res_canon_repr, 
                  "S_val_sym_dbg": S_val_sym, 
                  "parent_dict_name_for_debug": result_name_prefix_local }
                  
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
                            s_val_str = f"{solver.get_value(s_val_dbg)}" if s_val_dbg and s_val_dbg in solver.get_model() else "?"
                            print(f"      Local Span S_val (used as Omega_Canonical)={s_val_str}")

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
    print("====== AVC Direct Span Cyclic Asymmetry Exploration Test ======\n")

    P_A_val_sym = Symbol("PA_val_DSCAsym", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_DSCAsym", solver_INT_TYPE)
    
    X_L_val_fixed = Symbol("XL_val_DSCAsym", solver_INT_TYPE) 
    TargetDFI_L_val = Symbol("TargetDFI_L_DSCAsym", solver_INT_TYPE)


    for current_local_span_S_py in LOCAL_SPANS_TO_TEST:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py) 
        N_STEPS = current_local_span_S_py 

        print(f"\n\n===== DIRECT SPAN CYCLIC ASYMMETRY TEST WITH S = {current_local_span_S_py} (N_Steps = {N_STEPS}) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        if current_local_span_S_py < 2: # Needs DFI for X_L
            print(f"--- SKIPPING S={current_local_span_S_py} (Requires DFI for X_L) ---")
            del s
            continue
        
        s.add_assertion(Equals(X_L_val_fixed, P_A_val_sym + Int(1)))
        s.add_assertion(is_local_DFI_val(X_L_val_fixed, P_A_val_sym, P_B_val_sym))

        # --- Ascent Phase to reach AS_L (common for all paths) ---
        # This sequence of operations defines AS_reached_val symbolically
        current_R_L_val = P_A_val_sym 
        ascent_setup_assertions = []
        ascent_ops_debug_info = []
        
        for i in range(N_STEPS):
            op_res_dict = define_local_op_direct_span_result(
                smart_raw_add_logic_builder, 
                current_R_L_val, 
                X_L_val_fixed, 
                P_A_val_sym, P_B_val_sym, f"R{i+1}_S{current_local_span_S_py}"
            )
            ascent_setup_assertions.extend(op_res_dict["defining_assertions"])
            current_R_L_val = op_res_dict["val_L_sym"]
            ascent_ops_debug_info.append(op_res_dict)
        AS_reached_val = current_R_L_val # Symbolic FNode representing the value after N additions

        # --- Path 1 (Subtractive Descent - Control from previous test) ---
        s.push()
        current_S1_L_val = AS_reached_val
        path1_setup_assertions = list(ascent_setup_assertions) # Start with ascent assertions
        path1_ops_debug_info = list(ascent_ops_debug_info)

        for j in range(N_STEPS):
            op_res_dict = define_local_op_direct_span_result(
                smart_raw_sub_canonical_logic_builder,
                current_S1_L_val,
                X_L_val_fixed,
                P_A_val_sym, P_B_val_sym, f"P1_S{j+1}_S{current_local_span_S_py}"
            )
            path1_setup_assertions.extend(op_res_dict["defining_assertions"])
            current_S1_L_val = op_res_dict["val_L_sym"]
            path1_ops_debug_info.append(op_res_dict)
        Res1_L_val = current_S1_L_val
        
        prop_path1_is_AS = is_local_AS_val(Res1_L_val, P_B_val_sym)
        prove_or_find_counterexample(s, f"CPATH_A1: Path 1 (Sub Descent) results in AS_L (S={current_local_span_S_py})", 
                                     path1_setup_assertions, prop_path1_is_AS,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, X_L_val_fixed, AS_reached_val, Res1_L_val],
                                     op_result_dicts_for_debug=path1_ops_debug_info)
        s.pop()

        # --- Path 2 (Subtractive Reset then Emerge) ---
        s.push()
        path2_setup_assertions = list(ascent_setup_assertions)
        path2_ops_debug_info = list(ascent_ops_debug_info)

        temp_p2 = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, AS_reached_val, P_B_val_sym, P_A_val_sym, P_B_val_sym, f"Temp_P2_S{current_local_span_S_py}")
        path2_setup_assertions.extend(temp_p2["defining_assertions"])
        path2_ops_debug_info.append(temp_p2)
        
        Res2_L = define_local_op_direct_span_result(smart_raw_add_logic_builder, temp_p2["val_L_sym"], X_L_val_fixed, P_A_val_sym, P_B_val_sym, f"Res2_S{current_local_span_S_py}")
        path2_setup_assertions.extend(Res2_L["defining_assertions"])
        path2_ops_debug_info.append(Res2_L)

        prop_path2_is_XL = Equals(Res2_L["val_L_sym"], X_L_val_fixed)
        prove_or_find_counterexample(s, f"CPATH_B1: (AS_reached-AS_L)+X_L ~ X_L (S={current_local_span_S_py})", 
                                     path2_setup_assertions, prop_path2_is_XL,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, X_L_val_fixed, AS_reached_val, temp_p2["val_L_sym"], Res2_L["val_L_sym"]],
                                     op_result_dicts_for_debug=path2_ops_debug_info)
        s.pop()
        
        # --- Path 3 (Additive "Perturbation" of AS) ---
        s.push()
        path3_setup_assertions = list(ascent_setup_assertions)
        path3_ops_debug_info = list(ascent_ops_debug_info)

        Res3_L = define_local_op_direct_span_result(smart_raw_add_logic_builder, AS_reached_val, X_L_val_fixed, P_A_val_sym, P_B_val_sym, f"Res3_S{current_local_span_S_py}")
        path3_setup_assertions.extend(Res3_L["defining_assertions"])
        path3_ops_debug_info.append(Res3_L)

        prop_path3_is_XL = Equals(Res3_L["val_L_sym"], X_L_val_fixed)
        prove_or_find_counterexample(s, f"CPATH_B2: AS_reached+X_L ~ X_L (S={current_local_span_S_py})", 
                                     path3_setup_assertions, prop_path3_is_XL,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, X_L_val_fixed, AS_reached_val, Res3_L["val_L_sym"]],
                                     op_result_dicts_for_debug=path3_ops_debug_info)
        s.pop()

        # --- Path 4 (Subtract then Add from AS) ---
        s.push()
        path4_setup_assertions = list(ascent_setup_assertions)
        path4_ops_debug_info = list(ascent_ops_debug_info)

        temp_p4 = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, AS_reached_val, X_L_val_fixed, P_A_val_sym, P_B_val_sym, f"Temp_P4_S{current_local_span_S_py}")
        path4_setup_assertions.extend(temp_p4["defining_assertions"])
        path4_ops_debug_info.append(temp_p4)

        Res4_L = define_local_op_direct_span_result(smart_raw_add_logic_builder, temp_p4["val_L_sym"], X_L_val_fixed, P_A_val_sym, P_B_val_sym, f"Res4_S{current_local_span_S_py}")
        path4_setup_assertions.extend(Res4_L["defining_assertions"])
        path4_ops_debug_info.append(Res4_L)

        prop_path4_is_XL = Equals(Res4_L["val_L_sym"], X_L_val_fixed)
        prove_or_find_counterexample(s, f"CPATH_C1: (AS_reached-X_L)+X_L ~ X_L (S={current_local_span_S_py})", 
                                     path4_setup_assertions, prop_path4_is_XL,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, X_L_val_fixed, AS_reached_val, temp_p4["val_L_sym"], Res4_L["val_L_sym"]],
                                     op_result_dicts_for_debug=path4_ops_debug_info)
        s.pop()

        # --- Path 5 (Add then Subtract from AS) ---
        s.push()
        path5_setup_assertions = list(ascent_setup_assertions)
        path5_ops_debug_info = list(ascent_ops_debug_info)

        temp_p5 = define_local_op_direct_span_result(smart_raw_add_logic_builder, AS_reached_val, X_L_val_fixed, P_A_val_sym, P_B_val_sym, f"Temp_P5_S{current_local_span_S_py}")
        path5_setup_assertions.extend(temp_p5["defining_assertions"])
        path5_ops_debug_info.append(temp_p5)
        
        Res5_L = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, temp_p5["val_L_sym"], X_L_val_fixed, P_A_val_sym, P_B_val_sym, f"Res5_S{current_local_span_S_py}")
        path5_setup_assertions.extend(Res5_L["defining_assertions"])
        path5_ops_debug_info.append(Res5_L)
        
        prop_path5_is_ZS = is_local_ZS_val(Res5_L["val_L_sym"], P_A_val_sym)
        prove_or_find_counterexample(s, f"CPATH_C2: (AS_reached+X_L)-X_L ~ ZS_L (S={current_local_span_S_py})", 
                                     path5_setup_assertions, prop_path5_is_ZS,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, X_L_val_fixed, AS_reached_val, temp_p5["val_L_sym"], Res5_L["val_L_sym"]],
                                     op_result_dicts_for_debug=path5_ops_debug_info)
        s.pop()
        
        del s
        print("-" * 80)

    print("\n====== AVC Direct Span Cyclic Asymmetry Exploration Test Complete ======")