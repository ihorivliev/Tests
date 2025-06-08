# Script Name: AVC_General_Division_ComplexAdaptive_Test.py
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
    # Symbolic quotient and remainder for Fp / Fp
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE)
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE)

    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])

    # Rule: X / Unio_C -> AS_C
    formulas.append(Implies(divisor_is_unio,
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt))
    ))

    # Rules when divisor is Fp_C
    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), # Divisor is Fp_C
        Or(
            # ZS_C / Fp_C -> ZS_C
            And(i1["is_zero"],
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            # AS_C / Fp_C -> AS_C
            And(i1["is_areo"],
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
            # Fp_C(x) / Fp_C(y)
            And(i1["is_finite"],
                # Standard integer division constraints
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), # x = q*y + r
                    rem_sym >= Int(0),
                    rem_sym < i2["val"]), # 0 <= r < y
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)), # Divides cleanly to a Positive Natural quotient q
                    Ite(q_sym >= current_omega_smt, # Apply Omega threshold to quotient
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)), # q >= Omega -> AS_C
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym)) # q < Omega -> Fp_C(q)
                    ),
                    # Does not divide cleanly to a PosNat (remainder != 0 or quotient <= 0) -> AS_C
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt))
                )
            )
        )
    ))
    return And(formulas)

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
    val_if_omega_eff_is_complex_mapped = Ite(k_L_val > cap_val_for_complex_dfi,
                                             cap_val_for_complex_dfi,
                                             Ite(k_L_val <= Int(0), Int(1), k_L_val))
    
    val_assertions.append(
        Implies(arch_repr["is_finite"],
            Ite(Equals(Omega_eff_C_sym, Int(1)), map_to_false_if_omega_is_1,
            Ite(Equals(Omega_eff_C_sym, Int(2)), map_to_fp1_if_omega_is_2,
                                                Equals(arch_repr["val"], val_if_omega_eff_is_complex_mapped)
            )))
    )
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))
    return arch_repr, kind_assertions + val_assertions

def map_complex_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any],
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode,
    Omega_eff_C_sym: FNode, complex_omega_py_val: int
) -> FNode:
    val_from_fp_if_omega_eff_is_1 = PB_sym
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))
    
    map_val_complex = Ite(Equals(S_sym, Int(1)), PB_sym,
                     Ite(Equals(S_sym, Int(2)),
                         Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym),
                         Ite( (PA_sym + Arch_Res_Repr["val"]) < PB_sym,
                              PA_sym + Arch_Res_Repr["val"],
                              PB_sym - Int(1))
                        ))

    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                      Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         map_val_complex))
                                                         
    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
                                         fp_result_val
           ))

def define_local_op_complex_adaptive_archetype_result(
    op_canonical_result_definer_func: Callable,
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
    
    if Y_L_val_sym is not None:
        Y_canon_repr, y_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
            Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, f"{result_name_prefix_local}_yc")
        defining_assertions_for_local_op.extend(y_canon_assertions)
        Res_canon_repr = op_canonical_result_definer_func( 
            X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", Omega_eff_C_sym
        )
    else: # Should only be for hypothetical unary operations, not used in this script
        Y_canon_repr = None # Explicitly set to None
        Res_canon_repr = op_canonical_result_definer_func( 
            X_canon_repr, None, f"{result_name_prefix_local}_resc", Omega_eff_C_sym
        )

    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])
    
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_complex_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY)
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))
    
    debug_info = {"X_L_val_dbg": X_L_val_sym, "X_canon_repr_dbg": X_canon_repr,
                  "Y_L_val_dbg": Y_L_val_sym, "Y_canon_repr_dbg": Y_canon_repr, # Y_canon_repr can be None if Y_L_val_sym was None
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
    print("====== AVC General Division Complex Adaptive Test ======\n")

    P_A_val_sym = Symbol("PA_val_gdivcadap", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_gdivcadap", solver_INT_TYPE)
    
    A_L_val = Symbol("A_L_gdivcadap", solver_INT_TYPE)
    B_L_val = Symbol("B_L_gdivcadap", solver_INT_TYPE)
    C_L_val = Symbol("C_L_gdivcadap", solver_INT_TYPE)
    
    A1_L_val = Symbol("A1_L_gdivcadap", solver_INT_TYPE) 
    A2_L_val = Symbol("A2_L_gdivcadap", solver_INT_TYPE)
    B1_L_val = Symbol("B1_L_gdivcadap", solver_INT_TYPE)
    B2_L_val = Symbol("B2_L_gdivcadap", solver_INT_TYPE)
    
    Fp1_L_val = Symbol("Fp1_L_gdivcadap", solver_INT_TYPE) 
    DFI_for_cancel_B = Symbol("DFIB_L_gdivcadap", solver_INT_TYPE)


    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        effective_omega_for_print = COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY if current_local_span_S_py >=3 else (2 if current_local_span_S_py == 2 else 1)
        print(f"\n\n===== COMPLEX ADAPTIVE DIVISION TESTS WITH Local Span S = {current_local_span_S_py} (maps to Omega_eff_C = {effective_omega_for_print}) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        all_adaptive_test_inputs = [A_L_val, B_L_val, C_L_val, A1_L_val, A2_L_val, B1_L_val, B2_L_val, Fp1_L_val, DFI_for_cancel_B]
        for inp_val_sym in all_adaptive_test_inputs:
            s.add_assertion(And(inp_val_sym >= P_A_val_sym, inp_val_sym <= P_B_val_sym)) # Ensure inputs are within local frame
        
        # --- GDIV-CAdap-0: Well-Definedness ---
        s.push()
        prem_gdiv_cadap0 = And(avc_equiv_local_val(A1_L_val, A2_L_val, P_A_val_sym, P_B_val_sym),
                                avc_equiv_local_val(B1_L_val, B2_L_val, P_A_val_sym, P_B_val_sym))
        res1_gdiv0 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A1_L_val, B1_L_val, P_A_val_sym, P_B_val_sym, f"r1ca_gd0_S{current_local_span_S_py}")
        res2_gdiv0 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A2_L_val, B2_L_val, P_A_val_sym, P_B_val_sym, f"r2ca_gd0_S{current_local_span_S_py}")
        conc_gdiv0 = avc_equiv_local_val(res1_gdiv0["val_L_sym"], res2_gdiv0["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gdiv0 = [prem_gdiv_cadap0] + res1_gdiv0["defining_assertions"] + res2_gdiv0["defining_assertions"]
        prove_or_find_counterexample(s, f"GDIV-CAdap-0 Well-Defined (S={current_local_span_S_py})", setup_gdiv0, conc_gdiv0, 
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A1_L_val, A2_L_val, B1_L_val, B2_L_val, res1_gdiv0["val_L_sym"], res2_gdiv0["val_L_sym"]],
                                     op_result_dicts_for_debug=[res1_gdiv0, res2_gdiv0])
        s.pop()

        # --- GDIV-CAdap-1: A_L / ZS_L ~ AS_L ---
        s.push()
        res_gdiv1 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A_L_val, P_A_val_sym, P_A_val_sym, P_B_val_sym, f"r_gd1ca_S{current_local_span_S_py}")
        prop_gdiv1 = is_local_AS_val(res_gdiv1["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"GDIV-CAdap-1 A_L / ZS_L ~ AS_L (S={current_local_span_S_py})", res_gdiv1["defining_assertions"], prop_gdiv1,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gdiv1["val_L_sym"]], op_result_dicts_for_debug=[res_gdiv1])
        s.pop()

        # --- GDIV-CAdap-2: A_L / AS_L ~ AS_L ---
        s.push()
        res_gdiv2 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A_L_val, P_B_val_sym, P_A_val_sym, P_B_val_sym, f"r_gd2ca_S{current_local_span_S_py}")
        prop_gdiv2 = is_local_AS_val(res_gdiv2["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"GDIV-CAdap-2 A_L / AS_L ~ AS_L (S={current_local_span_S_py})", res_gdiv2["defining_assertions"], prop_gdiv2,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gdiv2["val_L_sym"]], op_result_dicts_for_debug=[res_gdiv2])
        s.pop()
        
        # --- GDIV-CAdap-3: ZS_L / A_L ~ Expected ---
        s.push()
        res_gdiv3 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, P_A_val_sym, A_L_val, P_A_val_sym, P_B_val_sym, f"r_gd3ca_S{current_local_span_S_py}")
        A_L_canon_temp_g3, a_l_canon_asserts_temp_g3 = map_local_to_complex_adaptive_archetype_input_repr(A_L_val, P_A_val_sym, P_B_val_sym, current_local_span_S_smt, Int(effective_omega_for_print), COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, "temp_AL_gd3")
        # Add constraints for A_L's canonical form for this test's context
        current_setup_g3 = res_gdiv3["defining_assertions"] + a_l_canon_asserts_temp_g3
        expected_val_gdiv3 = Ite(A_L_canon_temp_g3["is_finite"], P_A_val_sym, P_B_val_sym) 
        prop_gdiv3 = avc_equiv_local_val(res_gdiv3["val_L_sym"], expected_val_gdiv3, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"GDIV-CAdap-3 ZS_L / A_L ~ Expected (S={current_local_span_S_py})", current_setup_g3, prop_gdiv3,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gdiv3["val_L_sym"], expected_val_gdiv3, A_L_canon_temp_g3], 
                                     op_result_dicts_for_debug=[res_gdiv3])
        s.pop()

        # --- GDIV-CAdap-4: AS_L / A_L ~ AS_L ---
        s.push()
        res_gdiv4 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, P_B_val_sym, A_L_val, P_A_val_sym, P_B_val_sym, f"r_gd4ca_S{current_local_span_S_py}")
        prop_gdiv4 = is_local_AS_val(res_gdiv4["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"GDIV-CAdap-4 AS_L / A_L ~ AS_L (S={current_local_span_S_py})", res_gdiv4["defining_assertions"], prop_gdiv4,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gdiv4["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_gdiv4])
        s.pop()

        # --- GDIV-CAdap-5: Commutativity: A_L / B_L ~ B_L / A_L ---
        s.push()
        if current_local_span_S_py >= 3:
             s.add_assertion(Equals(A_L_val, P_A_val_sym + Int(1))) 
             s.add_assertion(Equals(B_L_val, P_A_val_sym + Int(2))) 
        elif current_local_span_S_py == 2:
             s.add_assertion(Equals(A_L_val, P_A_val_sym + Int(1))) 
             s.add_assertion(Equals(B_L_val, P_B_val_sym))
        # For S=1, A_L and B_L are general (PA or PB)

        res1_gdiv5 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"r1_gd5ca_S{current_local_span_S_py}")
        res2_gdiv5 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, B_L_val, A_L_val, P_A_val_sym, P_B_val_sym, f"r2_gd5ca_S{current_local_span_S_py}")
        prop_gdiv5 = avc_equiv_local_val(res1_gdiv5["val_L_sym"], res2_gdiv5["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gdiv5 = res1_gdiv5["defining_assertions"] + res2_gdiv5["defining_assertions"]
        prove_or_find_counterexample(s, f"GDIV-CAdap-5 Commutativity (S={current_local_span_S_py})", setup_gdiv5, prop_gdiv5,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, B_L_val, res1_gdiv5["val_L_sym"], res2_gdiv5["val_L_sym"]],
                                     op_result_dicts_for_debug=[res1_gdiv5, res2_gdiv5])
        s.pop()

        # --- GDIV-CAdap-6: Associativity: (A_L / B_L) / C_L ~ A_L / (B_L / C_L) ---
        s.push()
        if current_local_span_S_py >= 2: # DFI inputs make sense
            s.add_assertion(is_local_DFI_val(A_L_val, P_A_val_sym, P_B_val_sym))
            s.add_assertion(is_local_DFI_val(B_L_val, P_A_val_sym, P_B_val_sym))
            s.add_assertion(is_local_DFI_val(C_L_val, P_A_val_sym, P_B_val_sym))

            div_ab_gdiv6 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"divAB_gd6ca_S{current_local_span_S_py}")
            lhs_gdiv6 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, div_ab_gdiv6["val_L_sym"], C_L_val, P_A_val_sym, P_B_val_sym, f"lhs_gd6ca_S{current_local_span_S_py}")
            div_bc_gdiv6 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, B_L_val, C_L_val, P_A_val_sym, P_B_val_sym, f"divBC_gd6ca_S{current_local_span_S_py}")
            rhs_gdiv6 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A_L_val, div_bc_gdiv6["val_L_sym"], P_A_val_sym, P_B_val_sym, f"rhs_gd6ca_S{current_local_span_S_py}")
            prop_gdiv6 = avc_equiv_local_val(lhs_gdiv6["val_L_sym"], rhs_gdiv6["val_L_sym"], P_A_val_sym, P_B_val_sym)
            setup_gdiv6 = div_ab_gdiv6["defining_assertions"] + lhs_gdiv6["defining_assertions"] + div_bc_gdiv6["defining_assertions"] + rhs_gdiv6["defining_assertions"]
            prove_or_find_counterexample(s, f"GDIV-CAdap-6 Associativity (DFIs) (S={current_local_span_S_py})", setup_gdiv6, prop_gdiv6,
                                         model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,B_L_val,C_L_val,lhs_gdiv6["val_L_sym"],rhs_gdiv6["val_L_sym"]],
                                         op_result_dicts_for_debug=[div_ab_gdiv6,lhs_gdiv6,div_bc_gdiv6,rhs_gdiv6])
        else:
            print(f"--- SKIPPING GDIV-CAdap-6 for S={current_local_span_S_py} (DFI inputs not possible) ---")
        s.pop()

        # --- GDIV-CAdap-7: Right Identity (A_L / Fp_L(1) ~ A_L) ---
        if current_local_span_S_py >= 2:
            s.push()
            s.add_assertion(Equals(Fp1_L_val, P_A_val_sym + Int(1)))
            s.add_assertion(is_local_DFI_val(Fp1_L_val, P_A_val_sym, P_B_val_sym))

            res_gdiv7 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A_L_val, Fp1_L_val, P_A_val_sym, P_B_val_sym, f"r_gd7ca_S{current_local_span_S_py}")
            prop_gdiv7 = avc_equiv_local_val(res_gdiv7["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
            prove_or_find_counterexample(s, f"GDIV-CAdap-7 A_L / Fp_L(1) ~ A_L (S={current_local_span_S_py})", res_gdiv7["defining_assertions"], prop_gdiv7,
                                         model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,Fp1_L_val,res_gdiv7["val_L_sym"]],
                                         op_result_dicts_for_debug=[res_gdiv7])
            s.pop()
        else:
            print(f"--- SKIPPING GDIV-CAdap-7 for S={current_local_span_S_py} (No DFI for Fp_L(1)) ---")
            
        # --- GDIV-CAdap-8: Fp_L(k) / Fp_L(k) ~ Fp_L(1) (if S>=2, k is a DFI) ---
        if current_local_span_S_py >= 2:
            s.push()
            s.add_assertion(is_local_DFI_val(A_L_val, P_A_val_sym, P_B_val_sym))
            
            expected_Fp1_val_sym = P_A_val_sym + Int(1)
            
            res_gdiv8 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A_L_val, A_L_val, P_A_val_sym, P_B_val_sym, f"r_gd8ca_S{current_local_span_S_py}")
            # Check if the local result is equivalent to local PA+1
            prop_gdiv8_equiv = avc_equiv_local_val(res_gdiv8["val_L_sym"], expected_Fp1_val_sym, P_A_val_sym, P_B_val_sym)
            
            # Stronger check: ensure the canonical result was Fp_C(1)
            res_gdiv8_canon_repr_for_check = res_gdiv8.get("debug_info",{}).get("Res_canon_repr_dbg")
            prop_gdiv8_canon_is_fp1 = FALSE() # Default to false if not found
            if res_gdiv8_canon_repr_for_check:
                 prop_gdiv8_canon_is_fp1 = And(res_gdiv8_canon_repr_for_check["is_finite"], Equals(res_gdiv8_canon_repr_for_check["val"], Int(1)))
            
            prop_gdiv8_final = And(prop_gdiv8_equiv, prop_gdiv8_canon_is_fp1)

            prove_or_find_counterexample(s, f"GDIV-CAdap-8 Fp_L(k)/Fp_L(k) ~ Fp_L(1) & Canonically Fp_C(1) (S={current_local_span_S_py})", 
                                         res_gdiv8["defining_assertions"], prop_gdiv8_final,
                                         model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,res_gdiv8["val_L_sym"], expected_Fp1_val_sym, res_gdiv8_canon_repr_for_check],
                                         op_result_dicts_for_debug=[res_gdiv8])
            s.pop()
        else:
            print(f"--- SKIPPING GDIV-CAdap-8 for S={current_local_span_S_py} (No DFI for Fp_L(k)) ---")
            
        # --- GDIV-CAdap-9: Cancellation 1: (A_L * B_L_DFI) / B_L_DFI ~ A_L ---
        if current_local_span_S_py >= 2:
            s.push()
            s.add_assertion(is_local_DFI_val(DFI_for_cancel_B, P_A_val_sym, P_B_val_sym))

            prod_ab_gdiv9 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A_L_val, DFI_for_cancel_B, P_A_val_sym, P_B_val_sym, f"prodAB_gd9ca_S{current_local_span_S_py}")
            res_div_gdiv9 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, prod_ab_gdiv9["val_L_sym"], DFI_for_cancel_B, P_A_val_sym, P_B_val_sym, f"resDiv_gd9ca_S{current_local_span_S_py}")
            prop_gdiv9 = avc_equiv_local_val(res_div_gdiv9["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
            setup_gdiv9 = prod_ab_gdiv9["defining_assertions"] + res_div_gdiv9["defining_assertions"]
            prove_or_find_counterexample(s, f"GDIV-CAdap-9 (A_L*B_DFI)/B_DFI ~ A_L (S={current_local_span_S_py})", setup_gdiv9, prop_gdiv9,
                                         model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,DFI_for_cancel_B,prod_ab_gdiv9["val_L_sym"],res_div_gdiv9["val_L_sym"]],
                                         op_result_dicts_for_debug=[prod_ab_gdiv9,res_div_gdiv9])
            s.pop()
        else:
            print(f"--- SKIPPING GDIV-CAdap-9 for S={current_local_span_S_py} ---")

        # --- GDIV-CAdap-10: Cancellation 2: (A_L / B_L_DFI) * B_L_DFI ~ A_L, if A_L / B_L_DFI is DFI_L ---
        if current_local_span_S_py >= 2:
            s.push()
            s.add_assertion(is_local_DFI_val(DFI_for_cancel_B, P_A_val_sym, P_B_val_sym))

            div_ab_gdiv10 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, A_L_val, DFI_for_cancel_B, P_A_val_sym, P_B_val_sym, f"divAB_gd10ca_S{current_local_span_S_py}")
            s.add_assertion(is_local_DFI_val(div_ab_gdiv10["val_L_sym"], P_A_val_sym, P_B_val_sym)) # Premise: result of division is DFI_L
            
            res_mul_gdiv10 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, div_ab_gdiv10["val_L_sym"], DFI_for_cancel_B, P_A_val_sym, P_B_val_sym, f"resMul_gd10ca_S{current_local_span_S_py}")
            prop_gdiv10 = avc_equiv_local_val(res_mul_gdiv10["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
            # Add div_ab_gdiv10 assertions to the setup for prove_or_find_counterexample
            setup_gdiv10 = div_ab_gdiv10["defining_assertions"] + res_mul_gdiv10["defining_assertions"]
            prove_or_find_counterexample(s, f"GDIV-CAdap-10 (A_L/B_DFI)*B_DFI ~ A_L if div is DFI (S={current_local_span_S_py})", setup_gdiv10, prop_gdiv10,
                                         model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,DFI_for_cancel_B,div_ab_gdiv10["val_L_sym"],res_mul_gdiv10["val_L_sym"]],
                                         op_result_dicts_for_debug=[div_ab_gdiv10,res_mul_gdiv10])
            s.pop()
        else:
            print(f"--- SKIPPING GDIV-CAdap-10 for S={current_local_span_S_py} ---")

        del s
        print("-" * 80)

    print("\n====== AVC General Division Complex Adaptive Test Complete ======")