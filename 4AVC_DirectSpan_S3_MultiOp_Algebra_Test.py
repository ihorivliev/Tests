from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# For this script, we are HARDCODING the local span to 3 (P_A=0, P_B=3)
# This is the simplest span where smart_raw_add becomes non-associative.
LOCAL_SPAN_S_PY = 3
DEFAULT_P_A_OFFSET = 0

# --- Phase 1: Foundational Definitions (Canonical AVC) ---
# (Copied from previous robust scripts like AVC_Adaptive_Division_Properties_Test.py)
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

# --- Phase 2: Canonical Raw Operations Definitions (Parameterized by current_omega_smt) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
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
                            Ite(val_sum >= current_omega_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) 
                            )))
    return And(formulas)

def define_smart_raw_add_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                          result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_smt)
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

def define_raw_mul_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                    result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_smt)
    return res_repr

def raw_div_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode: 
    formulas = [] 
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE) 
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE) 

    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])
    formulas.append(Implies(divisor_is_unio, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), 
        Or( 
            And(i1["is_zero"], 
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), 
            And(i1["is_areo"],  
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(i1["is_finite"], 
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), 
                    rem_sym >= Int(0), 
                    rem_sym < i2["val"]), 
                
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)), 
                    Ite(q_sym >= current_omega_smt, 
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym)) 
                    ), 
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]))
                )
            )
        )
    ))
    return And(formulas)

def define_raw_div_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                     result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_div_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_smt)
    return res_repr

def raw_sub_from_Unio_Areo_aspect_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    # i1 is Unio (ZS or AS), i2 is DFI. Result is always AS.
    # This is Postulate 6.3 (Conceptual Diminution from Unio – The Transfinite Bridge to Finitude)
    # U⊖c X_DFI → U (engaging Areo-potential of U)
    # And by implication, ZS - X_DFI also has to go to AS (Unio) if it goes "below zero".
    
    # Simplified for this test: If i1 is ZS or AS, and i2 is Fp, result is AS.
    # This also covers P2.2.iv (A - X_DFI = A)
    is_i1_unio = Or(i1["is_zero"], i1["is_areo"])
    
    # Result is AS if i1 is Unio and i2 is DFI.
    # If i2 is not DFI (i.e., ZS or AS), the behavior is less defined by this specific postulate,
    # but U-U or U-ZS or U-AS would likely still be U (AS).
    # For simplicity and to match the core intent of P6.3 and P2.2.iv for DFI subtrahends:
    return Implies(And(is_i1_unio, i2["is_finite"]), # Unio - DFI
                   And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])))
    # Note: A more complete raw_sub would need to define other cases, but this suffices for P6.3 idea.

def define_raw_sub_from_Unio_Areo_aspect_canonical_result(
    i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
    result_name_prefix: str, current_omega_smt: FNode
) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_sub_from_Unio_Areo_aspect_logic_builder(
        i1_canon_repr, i2_canon_repr, res_repr, current_omega_smt
    )
    return res_repr

# --- Phase 3: Local Frame Definitions and Transformations (Direct Span S as Omega_C) ---
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
            Equals(X1_L_val_sym, X2_L_val_sym))
    )

def define_local_op_direct_span_result(
    op_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str
) -> Dict[str, Any]:
    all_defining_assertions = []
    current_S_val_sym = P_B_val_sym - P_A_val_sym

    X_canon_repr = create_intensity_representation(f"{result_name_prefix_local}_xc")
    Y_canon_repr = create_intensity_representation(f"{result_name_prefix_local}_yc")
    all_defining_assertions.extend([X_canon_repr["constraints"], Y_canon_repr["constraints"]])

    val_X_for_canon = X_L_val_sym - P_A_val_sym
    all_defining_assertions.append(
        Ite(is_local_ZS_val(X_L_val_sym, P_A_val_sym), 
            And(X_canon_repr["is_zero"], Not(X_canon_repr["is_areo"]), Not(X_canon_repr["is_finite"])),
        Ite(is_local_AS_val(X_L_val_sym, P_B_val_sym),
            And(X_canon_repr["is_areo"], Equals(X_canon_repr["val"], current_S_val_sym), Not(X_canon_repr["is_zero"]), Not(X_canon_repr["is_finite"])), # AS_C val is S
            And(X_canon_repr["is_finite"], Equals(X_canon_repr["val"], val_X_for_canon),
                val_X_for_canon > Int(0), val_X_for_canon < current_S_val_sym, Not(X_canon_repr["is_zero"]), Not(X_canon_repr["is_areo"])) 
        ))
    )
    val_Y_for_canon = Y_L_val_sym - P_A_val_sym
    all_defining_assertions.append(
        Ite(is_local_ZS_val(Y_L_val_sym, P_A_val_sym),
            And(Y_canon_repr["is_zero"], Not(Y_canon_repr["is_areo"]), Not(Y_canon_repr["is_finite"])),
        Ite(is_local_AS_val(Y_L_val_sym, P_B_val_sym),
            And(Y_canon_repr["is_areo"], Equals(Y_canon_repr["val"], current_S_val_sym), Not(Y_canon_repr["is_zero"]), Not(Y_canon_repr["is_finite"])), # AS_C val is S
            And(Y_canon_repr["is_finite"], Equals(Y_canon_repr["val"], val_Y_for_canon),
                val_Y_for_canon > Int(0), val_Y_for_canon < current_S_val_sym, Not(Y_canon_repr["is_zero"]), Not(Y_canon_repr["is_areo"]))
        ))
    )
    
    Res_canon_repr = op_canonical_result_definer(
        X_canon_repr, Y_canon_repr, 
        f"{result_name_prefix_local}_resc", 
        current_S_val_sym 
    )
    all_defining_assertions.append(Res_canon_repr["definition"])
    all_defining_assertions.append(Res_canon_repr["constraints"])

    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = Ite(Res_canon_repr["is_zero"], P_A_val_sym,
                                 Ite(Res_canon_repr["is_areo"], P_B_val_sym,
                                     P_A_val_sym + Res_canon_repr["val"]
                                 ))
    all_defining_assertions.append(Equals(Res_L_val_sym, local_result_value_formula))

    debug_info = {
        "X_L_val_dbg": X_L_val_sym, "X_canon_repr_dbg": X_canon_repr,
        "Y_L_val_dbg": Y_L_val_sym, "Y_canon_repr_dbg": Y_canon_repr,
        "Res_canon_repr_dbg": Res_canon_repr, 
        "S_val_sym_dbg": current_S_val_sym,
        "parent_dict_name_for_debug": result_name_prefix_local
    }
    return {
        "val_L_sym": Res_L_val_sym, 
        "defining_assertions": all_defining_assertions,
        "debug_info": debug_info
    }

# --- Phase 4: Generic Property Prover ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, 
                                 model_vars_to_print: List[Any] = [],
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
                print("  DEBUG Canonical Representations & Results in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "debug_info" in op_res_dict:
                        debug_info = op_res_dict["debug_info"]
                        if isinstance(debug_info, dict) and id(debug_info) not in printed_debug_info_ids: 
                            printed_debug_info_ids.add(id(debug_info))
                            op_name_for_print = debug_info.get("parent_dict_name_for_debug", "Op")
                            s_val_dbg = debug_info.get('S_val_sym_dbg')
                            s_val_str = f"{solver.get_value(s_val_dbg)}" if s_val_dbg and s_val_dbg in solver.get_model() else "?"
                            print(f"    Context for '{op_name_for_print}' (Local Span S_val/Omega_C = {s_val_str}):")

                            for repr_key_tuple in [("X_L_val_dbg", "X_canon_repr_dbg"), 
                                                   ("Y_L_val_dbg", "Y_canon_repr_dbg"), 
                                                   (None, "Res_canon_repr_dbg")]:
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
    print(f"====== AVC Direct Span S={LOCAL_SPAN_S_PY} Multi-Operation Algebra Test ======\n")

    s = Solver(name="z3")
    
    # Define Local Frame (Hardcoded for S=3)
    P_A_val_sym = Symbol("PA_S3", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_S3", solver_INT_TYPE)
    S_val_sym = Symbol("S_S3", solver_INT_TYPE)

    s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
    s.add_assertion(Equals(S_val_sym, Int(LOCAL_SPAN_S_PY)))
    s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + S_val_sym))
    s.add_assertion(S_val_sym > Int(0)) # Ensure span is positive

    # Symbolic local intensity values (their actual integer values in the local frame)
    La_L_val = Symbol("La_L_S3", solver_INT_TYPE)
    Lb_L_val = Symbol("Lb_L_S3", solver_INT_TYPE)
    Lc_L_val = Symbol("Lc_L_S3", solver_INT_TYPE)
    Ld_L_val = Symbol("Ld_L_S3", solver_INT_TYPE) # For more complex laws if needed

    # Base assertions for inputs to be valid within the local frame [PA, PB]
    # For most tests, La, Lb, Lc will be symbolic and generally constrained.
    # Specific tests (like DFI Haven) will add stricter constraints (e.g., is_local_DFI_val).
    general_inputs_setup = [
        And(La_L_val >= P_A_val_sym, La_L_val <= P_B_val_sym),
        And(Lb_L_val >= P_A_val_sym, Lb_L_val <= P_B_val_sym),
        And(Lc_L_val >= P_A_val_sym, Lc_L_val <= P_B_val_sym),
        And(Ld_L_val >= P_A_val_sym, Ld_L_val <= P_B_val_sym)
    ]
    s.add_assertions(general_inputs_setup)


    # --- Test Group MO-1: Re-verify Basic Algebraic Properties for S=3 (Baseline) ---
    print(f"--- Test Group MO-1: Baseline Algebraic Properties for S={LOCAL_SPAN_S_PY} ---")
    s.push() # Context for MO-1
    # For these tests, let La, Lb, Lc be symbolic local DFI values for hardest case
    s.add_assertion(is_local_DFI_val(La_L_val, P_A_val_sym, P_B_val_sym))
    s.add_assertion(is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym))
    s.add_assertion(is_local_DFI_val(Lc_L_val, P_A_val_sym, P_B_val_sym))

    # MO-1.1: Additive Associativity (Expected: FAIL for S=3)
    sum_ab_mo11 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "mo11_sum_ab")
    lhs_mo11 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, sum_ab_mo11["val_L_sym"], Lc_L_val, P_A_val_sym, P_B_val_sym, "mo11_lhs")
    sum_bc_mo11 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo11_sum_bc")
    rhs_mo11 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_L_val, sum_bc_mo11["val_L_sym"], P_A_val_sym, P_B_val_sym, "mo11_rhs")
    prop_mo11 = avc_equiv_local_val(lhs_mo11["val_L_sym"], rhs_mo11["val_L_sym"], P_A_val_sym, P_B_val_sym)
    prove_or_find_counterexample(s, f"MO-1.1 Add Assoc (S={LOCAL_SPAN_S_PY}, DFIs)",
                                 sum_ab_mo11["defining_assertions"] + lhs_mo11["defining_assertions"] + sum_bc_mo11["defining_assertions"] + rhs_mo11["defining_assertions"],
                                 prop_mo11, model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, La_L_val, Lb_L_val, Lc_L_val, lhs_mo11["val_L_sym"], rhs_mo11["val_L_sym"]],
                                 op_result_dicts_for_debug=[sum_ab_mo11, lhs_mo11, sum_bc_mo11, rhs_mo11])

    # MO-1.2: Multiplicative Associativity (Expected: PROVE for S=3)
    prod_ab_mo12 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "mo12_prod_ab")
    lhs_mo12 = define_local_op_direct_span_result(define_raw_mul_canonical_result, prod_ab_mo12["val_L_sym"], Lc_L_val, P_A_val_sym, P_B_val_sym, "mo12_lhs")
    prod_bc_mo12 = define_local_op_direct_span_result(define_raw_mul_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo12_prod_bc")
    rhs_mo12 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, prod_bc_mo12["val_L_sym"], P_A_val_sym, P_B_val_sym, "mo12_rhs")
    prop_mo12 = avc_equiv_local_val(lhs_mo12["val_L_sym"], rhs_mo12["val_L_sym"], P_A_val_sym, P_B_val_sym)
    prove_or_find_counterexample(s, f"MO-1.2 Mul Assoc (S={LOCAL_SPAN_S_PY}, DFIs)",
                                 prod_ab_mo12["defining_assertions"] + lhs_mo12["defining_assertions"] + prod_bc_mo12["defining_assertions"] + rhs_mo12["defining_assertions"],
                                 prop_mo12, model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, La_L_val, Lb_L_val, Lc_L_val, lhs_mo12["val_L_sym"], rhs_mo12["val_L_sym"]],
                                 op_result_dicts_for_debug=[prod_ab_mo12, lhs_mo12, prod_bc_mo12, rhs_mo12])

    # MO-1.3: Distributivity (Mul over Add) (Expected: FAIL for S=3)
    sum_bc_mo13 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo13_sum_bc")
    lhs_mo13 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, sum_bc_mo13["val_L_sym"], P_A_val_sym, P_B_val_sym, "mo13_lhs")
    prod_ab_mo13 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "mo13_prod_ab")
    prod_ac_mo13 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo13_prod_ac")
    rhs_mo13 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ab_mo13["val_L_sym"], prod_ac_mo13["val_L_sym"], P_A_val_sym, P_B_val_sym, "mo13_rhs")
    prop_mo13 = avc_equiv_local_val(lhs_mo13["val_L_sym"], rhs_mo13["val_L_sym"], P_A_val_sym, P_B_val_sym)
    prove_or_find_counterexample(s, f"MO-1.3 Distrib (S={LOCAL_SPAN_S_PY}, DFIs)",
                                 sum_bc_mo13["defining_assertions"] + lhs_mo13["defining_assertions"] + prod_ab_mo13["defining_assertions"] + prod_ac_mo13["defining_assertions"] + rhs_mo13["defining_assertions"],
                                 prop_mo13, model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, La_L_val, Lb_L_val, Lc_L_val, lhs_mo13["val_L_sym"], rhs_mo13["val_L_sym"]],
                                 op_result_dicts_for_debug=[sum_bc_mo13, lhs_mo13, prod_ab_mo13, prod_ac_mo13, rhs_mo13])
    s.pop() # End context for MO-1


    # --- Test Group MO-2: More Complex Interactions & Division for S=3 ---
    print(f"\n--- Test Group MO-2: Complex Interactions & Division for S={LOCAL_SPAN_S_PY} ---")
    s.push() # Context for MO-2
    # La, Lb, Lc are general local values (can be ZS, AS, DFI) for these tests
    # general_inputs_setup is already added globally for the S=3 loop

    # MO-2.1: Right Distributivity: (a + b) * c ~ (a * c) + (b * c) (Expected: FAIL for S=3 if DFIs)
    s.push() # Inner context for MO-2.1 DFI inputs
    s.add_assertion(is_local_DFI_val(La_L_val, P_A_val_sym, P_B_val_sym))
    s.add_assertion(is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym))
    s.add_assertion(is_local_DFI_val(Lc_L_val, P_A_val_sym, P_B_val_sym))
    sum_ab_mo21 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "mo21_sum_ab")
    lhs_mo21 = define_local_op_direct_span_result(define_raw_mul_canonical_result, sum_ab_mo21["val_L_sym"], Lc_L_val, P_A_val_sym, P_B_val_sym, "mo21_lhs")
    prod_ac_mo21 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo21_prod_ac")
    prod_bc_mo21 = define_local_op_direct_span_result(define_raw_mul_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo21_prod_bc")
    rhs_mo21 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ac_mo21["val_L_sym"], prod_bc_mo21["val_L_sym"], P_A_val_sym, P_B_val_sym, "mo21_rhs")
    prop_mo21 = avc_equiv_local_val(lhs_mo21["val_L_sym"], rhs_mo21["val_L_sym"], P_A_val_sym, P_B_val_sym)
    prove_or_find_counterexample(s, f"MO-2.1 Right Distrib (S={LOCAL_SPAN_S_PY}, DFIs)",
                                 sum_ab_mo21["defining_assertions"] + lhs_mo21["defining_assertions"] + prod_ac_mo21["defining_assertions"] + prod_bc_mo21["defining_assertions"] + rhs_mo21["defining_assertions"],
                                 prop_mo21, model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, La_L_val, Lb_L_val, Lc_L_val, lhs_mo21["val_L_sym"], rhs_mo21["val_L_sym"]],
                                 op_result_dicts_for_debug=[sum_ab_mo21, lhs_mo21, prod_ac_mo21, prod_bc_mo21, rhs_mo21])
    s.pop()

    # MO-2.2: Division Distributivity over Addition (Left): a / (b + c) ~ (a / b) + (a / c) (Expected: FAIL)
    sum_bc_mo22 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo22_sum_bc")
    lhs_mo22 = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, sum_bc_mo22["val_L_sym"], P_A_val_sym, P_B_val_sym, "mo22_lhs")
    div_ab_mo22 = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "mo22_div_ab")
    div_ac_mo22 = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo22_div_ac")
    rhs_mo22 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, div_ab_mo22["val_L_sym"], div_ac_mo22["val_L_sym"], P_A_val_sym, P_B_val_sym, "mo22_rhs")
    prop_mo22 = avc_equiv_local_val(lhs_mo22["val_L_sym"], rhs_mo22["val_L_sym"], P_A_val_sym, P_B_val_sym)
    prove_or_find_counterexample(s, f"MO-2.2 Div Distrib over Add (Left) (S={LOCAL_SPAN_S_PY})",
                                 sum_bc_mo22["defining_assertions"] + lhs_mo22["defining_assertions"] + div_ab_mo22["defining_assertions"] + div_ac_mo22["defining_assertions"] + rhs_mo22["defining_assertions"],
                                 prop_mo22, model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, La_L_val, Lb_L_val, Lc_L_val, lhs_mo22["val_L_sym"], rhs_mo22["val_L_sym"]],
                                 op_result_dicts_for_debug=[sum_bc_mo22, lhs_mo22, div_ab_mo22, div_ac_mo22, rhs_mo22])
    
    # MO-2.3: Division Distributivity over Addition (Right): (a + b) / c vs (a / c) + (b / c) (Expected: FAIL)
    sum_ab_mo23 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "mo23_sum_ab")
    lhs_mo23 = define_local_op_direct_span_result(define_raw_div_canonical_result, sum_ab_mo23["val_L_sym"], Lc_L_val, P_A_val_sym, P_B_val_sym, "mo23_lhs")
    div_ac_mo23 = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo23_div_ac")
    div_bc_mo23 = define_local_op_direct_span_result(define_raw_div_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "mo23_div_bc")
    rhs_mo23 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, div_ac_mo23["val_L_sym"], div_bc_mo23["val_L_sym"], P_A_val_sym, P_B_val_sym, "mo23_rhs")
    prop_mo23 = avc_equiv_local_val(lhs_mo23["val_L_sym"], rhs_mo23["val_L_sym"], P_A_val_sym, P_B_val_sym)
    prove_or_find_counterexample(s, f"MO-2.3 Div Distrib over Add (Right) (S={LOCAL_SPAN_S_PY})",
                                 sum_ab_mo23["defining_assertions"] + lhs_mo23["defining_assertions"] + div_ac_mo23["defining_assertions"] + div_bc_mo23["defining_assertions"] + rhs_mo23["defining_assertions"],
                                 prop_mo23, model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, La_L_val, Lb_L_val, Lc_L_val, lhs_mo23["val_L_sym"], rhs_mo23["val_L_sym"]],
                                 op_result_dicts_for_debug=[sum_ab_mo23, lhs_mo23, div_ac_mo23, div_bc_mo23, rhs_mo23])

    s.pop() # End context for MO-2
    
    # --- Test Group MO-3: Interactions with raw_sub_from_Unio_Areo_aspect ---
    print(f"\n--- Test Group MO-3: Interactions with Subtraction for S={LOCAL_SPAN_S_PY} ---")
    s.push() # Context for MO-3
    
    # MO-3.1: (Local_AS - Lb_DFI) + Lc_DFI vs Local_AS - (Lb_DFI - Lc_DFI) (conceptual, not direct test)
    # raw_sub_from_Unio_Areo_aspect is specific: Unio - DFI -> AS. So (AS - DFI) -> AS.
    # (P_B - Lb_DFI) + Lc_DFI where Lb_DFI is local DFI
    # P_B - Lb_DFI -> P_B (Local AS)
    # P_B + Lc_DFI -> Lc_DFI (if Lc_DFI mapped to FpC and P_B to AS_C, and smart_add) or P_B if Lc_DFI is ZS/AS.
    
    # More direct test: (P_A - Lb_DFI) ~ P_B  (where Lb_DFI is a DFI value)
    # P_A - Lb_DFI means local ZS - local DFI. This maps to ZS_C - Fp_C.
    # Per Postulate 6.3 (Conceptual Diminution from Unio), U - X_DFI -> U (engaging Areo-potential).
    # If ZS is part of U, and subtraction from ZS "goes below zero", it should hit Unio via Areo aspect.
    # Our current raw_sub_from_Unio_Areo_aspect_logic_builder ensures:
    # if i1 is ZS or AS, and i2 is DFI, result is AS.
    s.add_assertion(is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym)) # Lb is DFI
    
    res_sub_PA_Lb = define_local_op_direct_span_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, 
                                                       P_A_val_sym, Lb_L_val, 
                                                       P_A_val_sym, P_B_val_sym, "mo31_sub_PA_Lb")
    prop_mo31 = is_local_AS_val(res_sub_PA_Lb["val_L_sym"], P_B_val_sym)
    prove_or_find_counterexample(s, f"MO-3.1 (P_A - Lb_DFI) ~ P_B (S={LOCAL_SPAN_S_PY})",
                                 res_sub_PA_Lb["defining_assertions"], prop_mo31,
                                 model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, Lb_L_val, res_sub_PA_Lb["val_L_sym"]],
                                 op_result_dicts_for_debug=[res_sub_PA_Lb])

    # MO-3.2: (P_B - Lb_DFI) ~ P_B
    res_sub_PB_Lb = define_local_op_direct_span_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, 
                                                       P_B_val_sym, Lb_L_val, 
                                                       P_A_val_sym, P_B_val_sym, "mo32_sub_PB_Lb")
    prop_mo32 = is_local_AS_val(res_sub_PB_Lb["val_L_sym"], P_B_val_sym)
    prove_or_find_counterexample(s, f"MO-3.2 (P_B - Lb_DFI) ~ P_B (S={LOCAL_SPAN_S_PY})",
                                 res_sub_PB_Lb["defining_assertions"], prop_mo32,
                                 model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, Lb_L_val, res_sub_PB_Lb["val_L_sym"]],
                                 op_result_dicts_for_debug=[res_sub_PB_Lb])
    s.pop() # End context for MO-3

    del s # Release solver for this span
    print("-" * 80)

    print(f"\n====== AVC Direct Span S={LOCAL_SPAN_S_PY} Multi-Operation Algebra Test Complete ======")