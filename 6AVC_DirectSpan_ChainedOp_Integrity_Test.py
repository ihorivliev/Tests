# Script Name: AVC_DirectSpan_ChainedOp_Integrity_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Optional

# --- Configuration ---
LOCAL_SPANS_TO_TEST = [2, 3, 5, 7] 
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

def avc_equiv_canonical(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any]) -> FNode: # For canonical results
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"])
    finite_finite_equal_val = And(i1_repr["is_finite"],
                                 i2_repr["is_finite"],
                                 Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Phase 2: Canonical Raw Operations Definitions ---
# These builders take current_omega_smt which, for Direct Span, will be the local span S_val_sym
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
    Arch_Res_Repr: Dict[str, Any], PA_sym: FNode, S_canonical_omega_sym: FNode # S is the Omega here
) -> FNode:
    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PA_sym + S_canonical_omega_sym, # Map AS_C back to PB
                                         PA_sym + Arch_Res_Repr["val"] 
           ))

def define_local_op_direct_span_result(
    op_logic_builder_func: Callable, # This is the canonical logic builder itself
    X_L_val_sym: FNode, Y_L_val_sym: FNode,
    P_A_val_sym: FNode, P_B_val_sym: FNode, result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    S_val_sym = P_B_val_sym - P_A_val_sym # This S_val_sym IS the Omega for canonical operations

    X_canon_repr, x_canon_assertions = map_local_val_to_canonical_repr_direct_span(
        X_L_val_sym, P_A_val_sym, S_val_sym, f"{result_name_prefix_local}_xc")
    defining_assertions_for_local_op.extend(x_canon_assertions)
    
    Y_canon_repr, y_canon_assertions = map_local_val_to_canonical_repr_direct_span(
        Y_L_val_sym, P_A_val_sym, S_val_sym, f"{result_name_prefix_local}_yc")
    defining_assertions_for_local_op.extend(y_canon_assertions)
    
    # Directly use the canonical op logic builder
    Res_canon_repr = define_canonical_op_result(op_logic_builder_func, 
        X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", S_val_sym 
    )
    defining_assertions_for_local_op.append(Res_canon_repr["definition"]) # This is the logic And(...)
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"]) # Base constraints + AS val constraint
    
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_canonical_repr_to_local_val_direct_span(
        Res_canon_repr, P_A_val_sym, S_val_sym)
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))
    
    debug_info = {"X_L_val_dbg": X_L_val_sym, "X_canon_repr_dbg": X_canon_repr,
                  "Y_L_val_dbg": Y_L_val_sym, "Y_canon_repr_dbg": Y_canon_repr,
                  "Res_canon_repr_dbg": Res_canon_repr, 
                  "S_val_sym_dbg": S_val_sym, # S_val_sym is the Omega for Direct Span
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
    print("====== AVC Direct Span Chained Operation Integrity Test ======\n")

    P_A_val_sym = Symbol("PA_val_DSCOI", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_DSCOI", solver_INT_TYPE)
    
    A_L = Symbol("A_L_DSCOI", solver_INT_TYPE)
    B_L = Symbol("B_L_DSCOI", solver_INT_TYPE)
    C_L = Symbol("C_L_DSCOI", solver_INT_TYPE)
    D_L = Symbol("D_L_DSCOI", solver_INT_TYPE)
    E_L = Symbol("E_L_DSCOI", solver_INT_TYPE) 
    W_L = Symbol("W_L_DSCOI", solver_INT_TYPE) 

    Fp1_L_coi5 = Symbol("Fp1_L_DSCOI5", solver_INT_TYPE)
    Fp2_L_coi5 = Symbol("Fp2_L_DSCOI5", solver_INT_TYPE)
    Fp3_L_coi5 = Symbol("Fp3_L_DSCOI5", solver_INT_TYPE)


    for current_local_span_S_py in LOCAL_SPANS_TO_TEST:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== DIRECT SPAN CHAINED OP TESTS WITH S = {current_local_span_S_py} (Omega_Canonical = S) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        all_local_inputs = [A_L, B_L, C_L, D_L, E_L, W_L, Fp1_L_coi5, Fp2_L_coi5, Fp3_L_coi5]
        for inp_val_sym in all_local_inputs: 
            s.add_assertion(And(inp_val_sym >= P_A_val_sym, inp_val_sym <= P_B_val_sym))

        # --- DSCOI-1: FOIL-like Expansion: (A_L+B_L)*(C_L+D_L) ~ ((A_L*C_L)+(A_L*D_L)) + ((B_L*C_L)+(B_L*D_L)) ---
        s.push()
        sum_ab_c1 = define_local_op_direct_span_result(smart_raw_add_logic_builder, A_L, B_L, P_A_val_sym, P_B_val_sym, "sAB_dscoi1")
        sum_cd_c1 = define_local_op_direct_span_result(smart_raw_add_logic_builder, C_L, D_L, P_A_val_sym, P_B_val_sym, "sCD_dscoi1")
        lhs_dscoi1 = define_local_op_direct_span_result(raw_mul_logic_builder, sum_ab_c1["val_L_sym"], sum_cd_c1["val_L_sym"], P_A_val_sym, P_B_val_sym, "lhs_dscoi1")

        prod_ac_c1 = define_local_op_direct_span_result(raw_mul_logic_builder, A_L, C_L, P_A_val_sym, P_B_val_sym, "pAC_dscoi1")
        prod_ad_c1 = define_local_op_direct_span_result(raw_mul_logic_builder, A_L, D_L, P_A_val_sym, P_B_val_sym, "pAD_dscoi1")
        prod_bc_c1 = define_local_op_direct_span_result(raw_mul_logic_builder, B_L, C_L, P_A_val_sym, P_B_val_sym, "pBC_dscoi1")
        prod_bd_c1 = define_local_op_direct_span_result(raw_mul_logic_builder, B_L, D_L, P_A_val_sym, P_B_val_sym, "pBD_dscoi1")
        sum_acad_c1 = define_local_op_direct_span_result(smart_raw_add_logic_builder, prod_ac_c1["val_L_sym"], prod_ad_c1["val_L_sym"], P_A_val_sym, P_B_val_sym, "sACAD_dscoi1")
        sum_bcbd_c1 = define_local_op_direct_span_result(smart_raw_add_logic_builder, prod_bc_c1["val_L_sym"], prod_bd_c1["val_L_sym"], P_A_val_sym, P_B_val_sym, "sBCBD_dscoi1")
        rhs_dscoi1 = define_local_op_direct_span_result(smart_raw_add_logic_builder, sum_acad_c1["val_L_sym"], sum_bcbd_c1["val_L_sym"], P_A_val_sym, P_B_val_sym, "rhs_dscoi1")
        
        prop_dscoi1 = avc_equiv_local_val(lhs_dscoi1["val_L_sym"], rhs_dscoi1["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_dscoi1 = (sum_ab_c1["defining_assertions"] + sum_cd_c1["defining_assertions"] + lhs_dscoi1["defining_assertions"] +
                        prod_ac_c1["defining_assertions"] + prod_ad_c1["defining_assertions"] + prod_bc_c1["defining_assertions"] + prod_bd_c1["defining_assertions"] +
                        sum_acad_c1["defining_assertions"] + sum_bcbd_c1["defining_assertions"] + rhs_dscoi1["defining_assertions"])
        prove_or_find_counterexample(s, f"DSCOI-1 FOIL-like (S={current_local_span_S_py})", setup_dscoi1, prop_dscoi1,
                                     [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,D_L,lhs_dscoi1["val_L_sym"],rhs_dscoi1["val_L_sym"]], 
                                     op_result_dicts_for_debug=[sum_ab_c1, sum_cd_c1, lhs_dscoi1, prod_ac_c1, prod_ad_c1, prod_bc_c1, prod_bd_c1, sum_acad_c1, sum_bcbd_c1, rhs_dscoi1])
        s.pop()

        # --- DSCOI-2: Zero Chain: (((A_L*B_L)/B_L)-A_L)*C_L ~ ZS_L ---
        if current_local_span_S_py >= 2: 
            s.push()
            s.add_assertion(is_local_DFI_val(B_L, P_A_val_sym, P_B_val_sym)) 
            
            prod_ab_c2 = define_local_op_direct_span_result(raw_mul_logic_builder, A_L, B_L, P_A_val_sym, P_B_val_sym, "pAB_dscoi2")
            div_pab_b_c2 = define_local_op_direct_span_result(raw_div_logic_builder, prod_ab_c2["val_L_sym"], B_L, P_A_val_sym, P_B_val_sym, "dAB_B_dscoi2")
            sub_term_a_c2 = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, div_pab_b_c2["val_L_sym"], A_L, P_A_val_sym, P_B_val_sym, "sT_A_dscoi2")
            lhs_dscoi2 = define_local_op_direct_span_result(raw_mul_logic_builder, sub_term_a_c2["val_L_sym"], C_L, P_A_val_sym, P_B_val_sym, "lhs_dscoi2")

            prop_dscoi2 = is_local_ZS_val(lhs_dscoi2["val_L_sym"], P_A_val_sym)
            setup_dscoi2 = (prod_ab_c2["defining_assertions"] + div_pab_b_c2["defining_assertions"] + 
                            sub_term_a_c2["defining_assertions"] + lhs_dscoi2["defining_assertions"])
            prove_or_find_counterexample(s, f"DSCOI-2 Zero Chain (B_L is DFI) (S={current_local_span_S_py})", setup_dscoi2, prop_dscoi2,
                                         [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,lhs_dscoi2["val_L_sym"]],
                                         op_result_dicts_for_debug=[prod_ab_c2, div_pab_b_c2, sub_term_a_c2, lhs_dscoi2])
            s.pop()
        else:
            print(f"--- SKIPPING DSCOI-2 for S={current_local_span_S_py} (Requires DFI for B_L) ---")

        # --- DSCOI-3: Mixed Add/Sub: (A_L+B_L)-C_L ~ A_L+(B_L-C_L) ---
        s.push()
        sum_ab_c3 = define_local_op_direct_span_result(smart_raw_add_logic_builder, A_L, B_L, P_A_val_sym, P_B_val_sym, "sAB_dscoi3")
        lhs_dscoi3 = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, sum_ab_c3["val_L_sym"], C_L, P_A_val_sym, P_B_val_sym, "lhs_dscoi3")
        sub_bc_c3 = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, B_L, C_L, P_A_val_sym, P_B_val_sym, "sBC_dscoi3")
        rhs_dscoi3 = define_local_op_direct_span_result(smart_raw_add_logic_builder, A_L, sub_bc_c3["val_L_sym"], P_A_val_sym, P_B_val_sym, "rhs_dscoi3")
        prop_dscoi3 = avc_equiv_local_val(lhs_dscoi3["val_L_sym"], rhs_dscoi3["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_dscoi3 = (sum_ab_c3["defining_assertions"] + lhs_dscoi3["defining_assertions"] + 
                        sub_bc_c3["defining_assertions"] + rhs_dscoi3["defining_assertions"])
        prove_or_find_counterexample(s, f"DSCOI-3 Mixed Add/Sub (S={current_local_span_S_py})", setup_dscoi3, prop_dscoi3,
                                     [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,lhs_dscoi3["val_L_sym"],rhs_dscoi3["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_c3, lhs_dscoi3, sub_bc_c3, rhs_dscoi3])
        s.pop()
        
        # --- DSCOI-5: Iterated Subtraction from Areo: (((AS_L - Fp1_L) - Fp2_L) - Fp3_L) ~ AS_L ---
        if current_local_span_S_py >= 4: 
            s.push()
            s.add_assertion(Equals(Fp1_L_coi5, P_A_val_sym + Int(1)))
            s.add_assertion(Equals(Fp2_L_coi5, P_A_val_sym + Int(2)))
            s.add_assertion(Equals(Fp3_L_coi5, P_A_val_sym + Int(3)))
            s.add_assertion(is_local_DFI_val(Fp1_L_coi5, P_A_val_sym, P_B_val_sym))
            s.add_assertion(is_local_DFI_val(Fp2_L_coi5, P_A_val_sym, P_B_val_sym))
            s.add_assertion(is_local_DFI_val(Fp3_L_coi5, P_A_val_sym, P_B_val_sym))

            term1_c5 = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, P_B_val_sym, Fp1_L_coi5, P_A_val_sym, P_B_val_sym, "t1_dscoi5")
            term2_c5 = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, term1_c5["val_L_sym"], Fp2_L_coi5, P_A_val_sym, P_B_val_sym, "t2_dscoi5")
            lhs_dscoi5 = define_local_op_direct_span_result(smart_raw_sub_canonical_logic_builder, term2_c5["val_L_sym"], Fp3_L_coi5, P_A_val_sym, P_B_val_sym, "lhs_dscoi5")
            
            prop_dscoi5 = is_local_AS_val(lhs_dscoi5["val_L_sym"], P_B_val_sym)
            setup_dscoi5 = (term1_c5["defining_assertions"] + term2_c5["defining_assertions"] + lhs_dscoi5["defining_assertions"])
            prove_or_find_counterexample(s, f"DSCOI-5 Iterated Sub from AS_L ~ AS_L (S={current_local_span_S_py})", setup_dscoi5, prop_dscoi5,
                                         [P_A_val_sym,P_B_val_sym,Fp1_L_coi5,Fp2_L_coi5,Fp3_L_coi5,lhs_dscoi5["val_L_sym"]], 
                                         op_result_dicts_for_debug=[term1_c5, term2_c5, lhs_dscoi5])
            s.pop()
        else:
            print(f"--- SKIPPING DSCOI-5 for S={current_local_span_S_py} (Requires S>=4 for 3 distinct DFIs) ---")

        # --- DSCOI-6: Path Dependence from Additive Non-Associativity ---
        if current_local_span_S_py >= 3: # Additive non-associativity expected for S=Omega>=3
            s.push()
            s.add_assertion(is_local_DFI_val(A_L, P_A_val_sym, P_B_val_sym)) 
            s.add_assertion(is_local_DFI_val(B_L, P_A_val_sym, P_B_val_sym)) 
            s.add_assertion(is_local_DFI_val(C_L, P_A_val_sym, P_B_val_sym)) 
            s.add_assertion(is_local_DFI_val(W_L, P_A_val_sym, P_B_val_sym)) 

            sum_ab_c6 = define_local_op_direct_span_result(smart_raw_add_logic_builder, A_L, B_L, P_A_val_sym, P_B_val_sym, "sAB_dscoi6")
            lhs_add_c6 = define_local_op_direct_span_result(smart_raw_add_logic_builder, sum_ab_c6["val_L_sym"], C_L, P_A_val_sym, P_B_val_sym, "lhsAdd_dscoi6")
            sum_bc_c6 = define_local_op_direct_span_result(smart_raw_add_logic_builder, B_L, C_L, P_A_val_sym, P_B_val_sym, "sBC_dscoi6")
            rhs_add_c6 = define_local_op_direct_span_result(smart_raw_add_logic_builder, A_L, sum_bc_c6["val_L_sym"], P_A_val_sym, P_B_val_sym, "rhsAdd_dscoi6")
            
            # DSCOI-6.1: (LHS_add) * W_L ~ (RHS_add) * W_L
            lhs_mul_c6 = define_local_op_direct_span_result(raw_mul_logic_builder, lhs_add_c6["val_L_sym"], W_L, P_A_val_sym, P_B_val_sym, "lhsMul_dscoi6")
            rhs_mul_c6 = define_local_op_direct_span_result(raw_mul_logic_builder, rhs_add_c6["val_L_sym"], W_L, P_A_val_sym, P_B_val_sym, "rhsMul_dscoi6")
            prop_dscoi61 = avc_equiv_local_val(lhs_mul_c6["val_L_sym"], rhs_mul_c6["val_L_sym"], P_A_val_sym, P_B_val_sym)
            setup_dscoi61 = (sum_ab_c6["defining_assertions"] + lhs_add_c6["defining_assertions"] + sum_bc_c6["defining_assertions"] + rhs_add_c6["defining_assertions"] +
                             lhs_mul_c6["defining_assertions"] + rhs_mul_c6["defining_assertions"])
            prove_or_find_counterexample(s, f"DSCOI-6.1 PathDepMul (S={current_local_span_S_py})", setup_dscoi61, 
                                         prop_dscoi61,
                                         [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,W_L,lhs_add_c6["val_L_sym"],rhs_add_c6["val_L_sym"],lhs_mul_c6["val_L_sym"],rhs_mul_c6["val_L_sym"]],
                                         op_result_dicts_for_debug=[sum_ab_c6,lhs_add_c6,sum_bc_c6,rhs_add_c6,lhs_mul_c6,rhs_mul_c6])

            # DSCOI-6.2: (LHS_add) / W_L ~ (RHS_add) / W_L (W_L is DFI already constrained)
            lhs_div_c6 = define_local_op_direct_span_result(raw_div_logic_builder, lhs_add_c6["val_L_sym"], W_L, P_A_val_sym, P_B_val_sym, "lhsDiv_dscoi6")
            rhs_div_c6 = define_local_op_direct_span_result(raw_div_logic_builder, rhs_add_c6["val_L_sym"], W_L, P_A_val_sym, P_B_val_sym, "rhsDiv_dscoi6")
            prop_dscoi62 = avc_equiv_local_val(lhs_div_c6["val_L_sym"], rhs_div_c6["val_L_sym"], P_A_val_sym, P_B_val_sym)
            setup_dscoi62 = (sum_ab_c6["defining_assertions"] + lhs_add_c6["defining_assertions"] + sum_bc_c6["defining_assertions"] + rhs_add_c6["defining_assertions"] +
                             lhs_div_c6["defining_assertions"] + rhs_div_c6["defining_assertions"]) 
            prove_or_find_counterexample(s, f"DSCOI-6.2 PathDepDiv (S={current_local_span_S_py})", setup_dscoi62, prop_dscoi62,
                                         [P_A_val_sym,P_B_val_sym,A_L,B_L,C_L,W_L,lhs_add_c6["val_L_sym"],rhs_add_c6["val_L_sym"],lhs_div_c6["val_L_sym"],rhs_div_c6["val_L_sym"]],
                                         op_result_dicts_for_debug=[sum_ab_c6,lhs_add_c6,sum_bc_c6,rhs_add_c6,lhs_div_c6,rhs_div_c6])
            s.pop()
        else:
            print(f"--- SKIPPING DSCOI-6 for S={current_local_span_S_py} (Additive non-assoc relevant for S>=3) ---")

        del s
        print("-" * 80)

    print("\n====== AVC Direct Span Chained Operation Integrity Test Complete ======")