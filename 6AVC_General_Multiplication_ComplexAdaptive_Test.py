# Script Name: AVC_General_Multiplication_ComplexAdaptive_Test.py
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
    # Annihilation by Zero
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) )) # ZS * X -> ZS
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) )) # X * ZS -> ZS (if X not ZS)

    # Areo interactions (excluding ZS which is covered above)
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]), # AS * AS -> AS
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]), # AS * Fp
                            Ite(i2["val"] > Int(0), # AS * Fp(>0) -> AS
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) # AS * Fp(<=0) -> ZS (Fp constraint val>0 makes this branch unreachable for valid Fp)
                               )))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]), # Fp * AS
                            Ite(i1["val"] > Int(0), # Fp(>0) * AS -> AS
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) # Fp(<=0) * AS -> ZS
                               )))
    # Finite * Finite
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_prod >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)), # Prod >= Omega -> AS
                                Ite(val_prod <= Int(0), # Prod <= 0 (e.g. if signs were allowed, or if Fp could be non-positive)
                                    And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), # -> ZS
                                    And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)) # Prod < Omega & >0 -> Fp
                                   )
                               )))
    return And(formulas)

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
    # Ensure k_L_val maps to Fp_C > 0. If k_L_val is 0 (Local_val_sym == PA_sym), is_L_DFI_cond is false.
    # Capping ensures k_L_val (if large) doesn't exceed canonical DFI range.
    # Smallest DFI is k_L_val=1.
    val_if_omega_eff_is_complex_mapped = Ite(k_L_val > cap_val_for_complex_dfi,
                                             cap_val_for_complex_dfi,
                                             Ite(k_L_val <= Int(0), Int(1), k_L_val)) # Default to 1 if non-positive k_L, though DFI implies k_L>0
    
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
    
    # For S_sym >= 3 (maps to Omega_eff_C = complex_omega_py_val, e.g. 7)
    # Arch_Res_Repr["val"] is v_C from [1, complex_omega_py_val - 1]
    # Map back to PA_sym + v_C, but ensure it's a valid local DFI ( < PB_sym )
    # If PA_sym + v_C >= PB_sym, it means v_C is too large for the local span S_sym,
    # so map to the largest local DFI, which is PB_sym - 1 (if S_sym >=2).
    # If S_sym=1, there's no DFI, so any Fp_C result should map to AS_L (PB_sym).
    # If S_sym=2, DFI is PA+1.
    map_val_complex = Ite(Equals(S_sym, Int(1)), PB_sym,
                     Ite(Equals(S_sym, Int(2)),
                         Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym), # Fp_C(1) from Omega_eff=2 -> PA+1; others (AS) to PB
                         # S_sym >= 3, Omega_eff_C is complex_omega_py_val (e.g. 7)
                         Ite( (PA_sym + Arch_Res_Repr["val"]) < PB_sym,
                              PA_sym + Arch_Res_Repr["val"],
                              PB_sym - Int(1)) # Cap at last local DFI step if PA_sym + v_C is too large
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
    Y_canon_repr, y_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, f"{result_name_prefix_local}_yc")
    defining_assertions_for_local_op.extend(y_canon_assertions)
    
    Res_canon_repr = op_canonical_result_definer_func( 
        X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", Omega_eff_C_sym
    )
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
            simple_vars_printed_this_context = set()
            for var_item in model_vars_to_print:
                if isinstance(var_item, FNode) and var_item.is_symbol():
                    if var_item.symbol_name() not in simple_vars_printed_this_context:
                        print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
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
    print("====== AVC General Multiplication Complex Adaptive Test ======\n")

    P_A_val_sym = Symbol("PA_val_gmulcadap", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_gmulcadap", solver_INT_TYPE)
    
    A_L_val = Symbol("A_L_gmulcadap", solver_INT_TYPE)
    B_L_val = Symbol("B_L_gmulcadap", solver_INT_TYPE)
    C_L_val = Symbol("C_L_gmulcadap", solver_INT_TYPE)
    
    A1_L_val = Symbol("A1_L_gmulcadap", solver_INT_TYPE)
    A2_L_val = Symbol("A2_L_gmulcadap", solver_INT_TYPE)
    B1_L_val = Symbol("B1_L_gmulcadap", solver_INT_TYPE)
    B2_L_val = Symbol("B2_L_gmulcadap", solver_INT_TYPE)
    
    Fp1_L_val = Symbol("Fp1_L_gmulcadap", solver_INT_TYPE) # For identity test

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        effective_omega_for_print = COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY if current_local_span_S_py >=3 else (2 if current_local_span_S_py == 2 else 1)
        print(f"\n\n===== COMPLEX ADAPTIVE MULTIPLICATION TESTS WITH Local Span S = {current_local_span_S_py} (maps to Omega_eff_C = {effective_omega_for_print}) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        all_adaptive_test_inputs = [A_L_val, B_L_val, C_L_val, A1_L_val, A2_L_val, B1_L_val, B2_L_val, Fp1_L_val]
        for inp_val_sym in all_adaptive_test_inputs:
            s.add_assertion(And(inp_val_sym >= P_A_val_sym, inp_val_sym <= P_B_val_sym))
        
        # --- GMUL-CAdap-0: Well-Definedness ---
        s.push()
        prem_gmul_cadap0 = And(avc_equiv_local_val(A1_L_val, A2_L_val, P_A_val_sym, P_B_val_sym),
                                avc_equiv_local_val(B1_L_val, B2_L_val, P_A_val_sym, P_B_val_sym))
        res1_gmul0 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A1_L_val, B1_L_val, P_A_val_sym, P_B_val_sym, f"r1ca_gm0_S{current_local_span_S_py}")
        res2_gmul0 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A2_L_val, B2_L_val, P_A_val_sym, P_B_val_sym, f"r2ca_gm0_S{current_local_span_S_py}")
        conc_gmul0 = avc_equiv_local_val(res1_gmul0["val_L_sym"], res2_gmul0["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gmul0 = [prem_gmul_cadap0] + res1_gmul0["defining_assertions"] + res2_gmul0["defining_assertions"]
        prove_or_find_counterexample(s, f"GMUL-CAdap-0 Well-Defined (S={current_local_span_S_py})", setup_gmul0, conc_gmul0, 
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A1_L_val, A2_L_val, B1_L_val, B2_L_val, res1_gmul0["val_L_sym"], res2_gmul0["val_L_sym"]],
                                     op_result_dicts_for_debug=[res1_gmul0, res2_gmul0])
        s.pop()

        # --- GMUL-CAdap-1: ZS_L * A_L ~ ZS_L ---
        s.push()
        res_gmul1 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, P_A_val_sym, A_L_val, P_A_val_sym, P_B_val_sym, f"r_gm1ca_S{current_local_span_S_py}")
        prop_gmul1 = is_local_ZS_val(res_gmul1["val_L_sym"], P_A_val_sym)
        prove_or_find_counterexample(s, f"GMUL-CAdap-1 ZS_L * A_L ~ ZS_L (S={current_local_span_S_py})", res_gmul1["defining_assertions"], prop_gmul1,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gmul1["val_L_sym"]], op_result_dicts_for_debug=[res_gmul1])
        s.pop()

        # --- GMUL-CAdap-2: A_L * ZS_L ~ ZS_L ---
        s.push()
        res_gmul2 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A_L_val, P_A_val_sym, P_A_val_sym, P_B_val_sym, f"r_gm2ca_S{current_local_span_S_py}")
        prop_gmul2 = is_local_ZS_val(res_gmul2["val_L_sym"], P_A_val_sym)
        prove_or_find_counterexample(s, f"GMUL-CAdap-2 A_L * ZS_L ~ ZS_L (S={current_local_span_S_py})", res_gmul2["defining_assertions"], prop_gmul2,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gmul2["val_L_sym"]], op_result_dicts_for_debug=[res_gmul2])
        s.pop()

        # --- GMUL-CAdap-3: AS_L * A_L ~ ExpectedResult_L ---
        # Expected: ZS_L if A_L is ZS_L. Else AS_L (if A_L is DFI_L or AS_L)
        s.push()
        res_gmul3 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, P_B_val_sym, A_L_val, P_A_val_sym, P_B_val_sym, f"r_gm3ca_S{current_local_span_S_py}")
        
        # Define expected result based on A_L's nature
        # Map A_L to canonical A_C to determine its kind for expectation
        A_L_canon_temp, a_l_canon_asserts_temp = map_local_to_complex_adaptive_archetype_input_repr(A_L_val, P_A_val_sym, P_B_val_sym, current_local_span_S_smt, Int(effective_omega_for_print), COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, "temp_AL_gm3")
        s.add_assertions(a_l_canon_asserts_temp)

        expected_val_gmul3 = Ite(A_L_canon_temp["is_zero"], P_A_val_sym, P_B_val_sym) # if A_L maps to ZS_C -> ZS_L, else AS_L
        prop_gmul3 = avc_equiv_local_val(res_gmul3["val_L_sym"], expected_val_gmul3, P_A_val_sym, P_B_val_sym)
        
        prove_or_find_counterexample(s, f"GMUL-CAdap-3 AS_L * A_L ~ Expected (S={current_local_span_S_py})", res_gmul3["defining_assertions"], prop_gmul3,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gmul3["val_L_sym"], expected_val_gmul3, A_L_canon_temp], 
                                     op_result_dicts_for_debug=[res_gmul3])
        s.pop()
        
        # --- GMUL-CAdap-4: A_L * AS_L ~ ExpectedResult_L --- (Similar to GMUL-CAdap-3 due to commutativity)
        s.push()
        res_gmul4 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A_L_val, P_B_val_sym, P_A_val_sym, P_B_val_sym, f"r_gm4ca_S{current_local_span_S_py}")
        A_L_canon_temp_g4, a_l_canon_asserts_temp_g4 = map_local_to_complex_adaptive_archetype_input_repr(A_L_val, P_A_val_sym, P_B_val_sym, current_local_span_S_smt, Int(effective_omega_for_print), COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, "temp_AL_gm4")
        s.add_assertions(a_l_canon_asserts_temp_g4)
        expected_val_gmul4 = Ite(A_L_canon_temp_g4["is_zero"], P_A_val_sym, P_B_val_sym)
        prop_gmul4 = avc_equiv_local_val(res_gmul4["val_L_sym"], expected_val_gmul4, P_A_val_sym, P_B_val_sym)
        
        prove_or_find_counterexample(s, f"GMUL-CAdap-4 A_L * AS_L ~ Expected (S={current_local_span_S_py})", res_gmul4["defining_assertions"], prop_gmul4,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, res_gmul4["val_L_sym"],expected_val_gmul4, A_L_canon_temp_g4],
                                     op_result_dicts_for_debug=[res_gmul4])
        s.pop()

        # --- GMUL-CAdap-5: Commutativity: A_L * B_L ~ B_L * A_L ---
        s.push()
        res1_gmul5 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"r1_gm5ca_S{current_local_span_S_py}")
        res2_gmul5 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, B_L_val, A_L_val, P_A_val_sym, P_B_val_sym, f"r2_gm5ca_S{current_local_span_S_py}")
        prop_gmul5 = avc_equiv_local_val(res1_gmul5["val_L_sym"], res2_gmul5["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gmul5 = res1_gmul5["defining_assertions"] + res2_gmul5["defining_assertions"]
        prove_or_find_counterexample(s, f"GMUL-CAdap-5 Commutativity (S={current_local_span_S_py})", setup_gmul5, prop_gmul5,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, A_L_val, B_L_val, res1_gmul5["val_L_sym"], res2_gmul5["val_L_sym"]],
                                     op_result_dicts_for_debug=[res1_gmul5, res2_gmul5])
        s.pop()

        # --- GMUL-CAdap-6: Associativity: (A_L * B_L) * C_L ~ A_L * (B_L * C_L) ---
        # Use DFI inputs to stress this
        s.push()
        s.add_assertion(is_local_DFI_val(A_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(B_L_val, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI_val(C_L_val, P_A_val_sym, P_B_val_sym))

        prod_ab_gmul6 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A_L_val, B_L_val, P_A_val_sym, P_B_val_sym, f"prodAB_gm6ca_S{current_local_span_S_py}")
        lhs_gmul6 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, prod_ab_gmul6["val_L_sym"], C_L_val, P_A_val_sym, P_B_val_sym, f"lhs_gm6ca_S{current_local_span_S_py}")
        prod_bc_gmul6 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, B_L_val, C_L_val, P_A_val_sym, P_B_val_sym, f"prodBC_gm6ca_S{current_local_span_S_py}")
        rhs_gmul6 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A_L_val, prod_bc_gmul6["val_L_sym"], P_A_val_sym, P_B_val_sym, f"rhs_gm6ca_S{current_local_span_S_py}")
        prop_gmul6 = avc_equiv_local_val(lhs_gmul6["val_L_sym"], rhs_gmul6["val_L_sym"], P_A_val_sym, P_B_val_sym)
        setup_gmul6 = prod_ab_gmul6["defining_assertions"] + lhs_gmul6["defining_assertions"] + prod_bc_gmul6["defining_assertions"] + rhs_gmul6["defining_assertions"]
        prove_or_find_counterexample(s, f"GMUL-CAdap-6 Associativity (DFIs) (S={current_local_span_S_py})", setup_gmul6, prop_gmul6,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,B_L_val,C_L_val,lhs_gmul6["val_L_sym"],rhs_gmul6["val_L_sym"]],
                                     op_result_dicts_for_debug=[prod_ab_gmul6,lhs_gmul6,prod_bc_gmul6,rhs_gmul6])
        s.pop()

        # --- GMUL-CAdap-7: Multiplicative Identity (using Local PA+1 as Fp_L(1) candidate) ---
        if current_local_span_S_py >= 2: # Fp_L(1) = PA_L+1 can exist
            s.push()
            s.add_assertion(Equals(Fp1_L_val, P_A_val_sym + Int(1)))
            s.add_assertion(is_local_DFI_val(Fp1_L_val, P_A_val_sym, P_B_val_sym)) # Ensure PA+1 is DFI

            res_gmul7 = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, A_L_val, Fp1_L_val, P_A_val_sym, P_B_val_sym, f"r_gm7ca_S{current_local_span_S_py}")
            prop_gmul7 = avc_equiv_local_val(res_gmul7["val_L_sym"], A_L_val, P_A_val_sym, P_B_val_sym)
            setup_gmul7 = res_gmul7["defining_assertions"]
            prove_or_find_counterexample(s, f"GMUL-CAdap-7 A_L * Fp_L(1) ~ A_L (S={current_local_span_S_py})", setup_gmul7, prop_gmul7,
                                         model_vars_to_print=[P_A_val_sym,P_B_val_sym,A_L_val,Fp1_L_val,res_gmul7["val_L_sym"]],
                                         op_result_dicts_for_debug=[res_gmul7])
            s.pop()
        else:
            print(f"--- SKIPPING GMUL-CAdap-7 for S={current_local_span_S_py} (No DFI for Fp_L(1)) ---")


        del s
        print("-" * 80)

    print("\n====== AVC General Multiplication Complex Adaptive Test Complete ======")