from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any

# --- Configuration ---
LOCAL_SPAN_S_PY = 2 # Focusing only on S=2 for this specific test
DEFAULT_P_A_OFFSET = 0

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
            X_canon_repr["is_zero"],
        Ite(is_local_AS_val(X_L_val_sym, P_B_val_sym),
            And(X_canon_repr["is_areo"], Equals(X_canon_repr["val"], current_S_val_sym)),
            And(X_canon_repr["is_finite"], Equals(X_canon_repr["val"], val_X_for_canon),
                val_X_for_canon > Int(0), val_X_for_canon < current_S_val_sym) 
        ))
    )
    val_Y_for_canon = Y_L_val_sym - P_A_val_sym
    all_defining_assertions.append(
        Ite(is_local_ZS_val(Y_L_val_sym, P_A_val_sym),
            Y_canon_repr["is_zero"],
        Ite(is_local_AS_val(Y_L_val_sym, P_B_val_sym),
            And(Y_canon_repr["is_areo"], Equals(Y_canon_repr["val"], current_S_val_sym)),
            And(Y_canon_repr["is_finite"], Equals(Y_canon_repr["val"], val_Y_for_canon),
                val_Y_for_canon > Int(0), val_Y_for_canon < current_S_val_sym)
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
                        if isinstance(debug_info, dict) and id(debug_info) not in printed_debug_info_ids: # Avoid re-printing shared debug info
                            printed_debug_info_ids.add(id(debug_info))
                            op_name_for_print = debug_info.get("parent_dict_name_for_debug", "Op")
                            s_val_dbg = debug_info.get('S_val_sym_dbg')
                            s_val_str = f"{solver.get_value(s_val_dbg)}" if s_val_dbg and s_val_dbg in solver.get_model() else "?"
                            print(f"    Context for '{op_name_for_print}' (Local Span S_val/Omega_C = {s_val_str}):")

                            for repr_key_prefix in ["X", "Y", "Res"]:
                                repr_dict_dbg = debug_info.get(f"{repr_key_prefix}_canon_repr_dbg")
                                if repr_dict_dbg and isinstance(repr_dict_dbg, dict) and "name" in repr_dict_dbg:
                                    val_str_node = f"V={solver.get_value(repr_dict_dbg['val'])}" if repr_dict_dbg['val'] in solver.get_model() else "V=?"
                                    is_z_str_node = f"Z={solver.get_value(repr_dict_dbg['is_zero'])}" if repr_dict_dbg['is_zero'] in solver.get_model() else "Z=?"
                                    is_a_str_node = f"A={solver.get_value(repr_dict_dbg['is_areo'])}" if repr_dict_dbg['is_areo'] in solver.get_model() else "A=?"
                                    is_f_str_node = f"F={solver.get_value(repr_dict_dbg['is_finite'])}" if repr_dict_dbg['is_finite'] in solver.get_model() else "F=?"
                                    print(f"      {repr_dict_dbg['name']} (Canon): {is_z_str_node}, {is_a_str_node}, {is_f_str_node}, {val_str_node}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Relativistic Division S=2 Commutativity Focus Test ======\n")

    s = Solver(name="z3")
    current_S_smt = Int(LOCAL_SPAN_S_PY) # Fixed Span S=2 for this test

    PA_val = Symbol("PA_val_s2comm", solver_INT_TYPE)
    PB_val = Symbol("PB_val_s2comm", solver_INT_TYPE)
    
    s.add_assertion(Equals(PA_val, Int(DEFAULT_P_A_OFFSET)))
    s.add_assertion(Equals(PB_val, PA_val + current_S_smt)) # PB_val = PA_val + 2

    # Specific Local Values for Targeted Tests
    # For S=2, Local values can be PA, PA+1 (DFI), PB
    La_L_val_target = Symbol("La_L_s2comm", solver_INT_TYPE)
    Lb_L_val_target = Symbol("Lb_L_s2comm", solver_INT_TYPE)

    # Test Cases for Commutativity RD-1.S2: La / Lb ~ Lb / La
    test_scenarios_s2_comm = [
        ("DFI_L / ZS_L", [Equals(La_L_val_target, PA_val + Int(1)), Equals(Lb_L_val_target, PA_val)]),
        ("DFI_L / AS_L", [Equals(La_L_val_target, PA_val + Int(1)), Equals(Lb_L_val_target, PB_val)]),
        ("ZS_L / AS_L",  [Equals(La_L_val_target, PA_val),       Equals(Lb_L_val_target, PB_val)]),
        # Symmetric cases are covered by the definition of commutativity test
    ]

    print(f"--- Testing RD-1 (Commutativity of raw_div_local) for specific S=2 cases ---")
    for scenario_name, specific_constraints in test_scenarios_s2_comm:
        s.push()
        # Assert general validity of La, Lb within the frame [PA, PB]
        s.add_assertion(And(La_L_val_target >= PA_val, La_L_val_target <= PB_val))
        s.add_assertion(And(Lb_L_val_target >= PA_val, Lb_L_val_target <= PB_val))
        # Apply specific constraints for this scenario
        s.add_assertions(specific_constraints)

        op_name_ab = f"rd1_s2_ab_{scenario_name.replace(' / ','_div_').replace(' ','')}"
        op_name_ba = f"rd1_s2_ba_{scenario_name.replace(' / ','_div_').replace(' ','')}"

        res_ab_div_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val_target, Lb_L_val_target, PA_val, PB_val, op_name_ab)
        res_ba_div_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, Lb_L_val_target, La_L_val_target, PA_val, PB_val, op_name_ba)
        
        property_rd1_s2_specific = avc_equiv_local_val(res_ab_div_dict["val_L_sym"], res_ba_div_dict["val_L_sym"], PA_val, PB_val)
        
        all_assertions_scenario = res_ab_div_dict["defining_assertions"] + res_ba_div_dict["defining_assertions"]
        
        prove_or_find_counterexample(s, f"RD-1 Commutativity S=2 - Scenario: {scenario_name}",
                                     all_assertions_scenario,
                                     property_rd1_s2_specific, 
                                     model_vars_to_print=[PA_val, PB_val, La_L_val_target, Lb_L_val_target, res_ab_div_dict["val_L_sym"], res_ba_div_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_ab_div_dict, res_ba_div_dict])
        s.pop()

    del s
    print("\n====== AVC Relativistic Division S=2 Commutativity Focus Test Complete ======")