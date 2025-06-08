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

def avc_equiv_local_val(X1_L_val_sym: FNode, X2_L_val_sym: FNode, 
                        P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    # Local Equivalence based on local SMT integer values
    is_X1_L_ZS = Equals(X1_L_val_sym, P_A_val_sym)
    is_X1_L_AS = Equals(X1_L_val_sym, P_B_val_sym)
    is_X1_L_DFI = And(X1_L_val_sym > P_A_val_sym, X1_L_val_sym < P_B_val_sym)

    is_X2_L_ZS = Equals(X2_L_val_sym, P_A_val_sym)
    is_X2_L_AS = Equals(X2_L_val_sym, P_B_val_sym)
    is_X2_L_DFI = And(X2_L_val_sym > P_A_val_sym, X2_L_val_sym < P_B_val_sym)

    return Or(
        And(is_X1_L_ZS, is_X2_L_ZS),
        And(is_X1_L_AS, is_X2_L_AS),
        And(is_X1_L_ZS, is_X2_L_AS), # Local Unio
        And(is_X1_L_AS, is_X2_L_ZS), # Local Unio
        And(is_X1_L_DFI, is_X2_L_DFI, Equals(X1_L_val_sym, X2_L_val_sym))
    )

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
                    rem_sym < i2["val"] # Assumes i2.is_finite => i2.val > 0
                    ), 
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
# ADDING MISSING HELPER FUNCTIONS HERE
def is_local_ZS_val(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS_val(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI_val(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    # A local DFI exists only if span P_B_val_sym - P_A_val_sym > 1
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)
# END OF ADDED HELPER FUNCTIONS

def define_local_op_direct_span_result(
    op_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str,
    X_L_kind_force: str = None, 
    Y_L_kind_force: str = None 
) -> Dict[str, Any]:

    all_defining_assertions = []
    current_S_val_sym = P_B_val_sym - P_A_val_sym

    X_canon_repr = create_intensity_representation(f"{result_name_prefix_local}_xc")
    Y_canon_repr = create_intensity_representation(f"{result_name_prefix_local}_yc")
    all_defining_assertions.extend([X_canon_repr["constraints"], Y_canon_repr["constraints"]])

    val_X_for_canon = X_L_val_sym - P_A_val_sym
    is_X_L_ZS = is_local_ZS_val(X_L_val_sym, P_A_val_sym) # Now defined
    is_X_L_AS = is_local_AS_val(X_L_val_sym, P_B_val_sym) # Now defined
    # is_X_L_DFI = is_local_DFI_val(X_L_val_sym, P_A_val_sym, P_B_val_sym) # Not strictly needed if using ITE

    if X_L_kind_force == "ZS":
        all_defining_assertions.append(X_canon_repr["is_zero"])
        all_defining_assertions.append(Not(X_canon_repr["is_areo"]))
        all_defining_assertions.append(Not(X_canon_repr["is_finite"]))
    elif X_L_kind_force == "AS":
        all_defining_assertions.append(X_canon_repr["is_areo"])
        all_defining_assertions.append(Equals(X_canon_repr["val"], current_S_val_sym))
        all_defining_assertions.append(Not(X_canon_repr["is_zero"]))
        all_defining_assertions.append(Not(X_canon_repr["is_finite"]))
    elif X_L_kind_force == "DFI":
        all_defining_assertions.append(X_canon_repr["is_finite"])
        all_defining_assertions.append(Equals(X_canon_repr["val"], val_X_for_canon))
        all_defining_assertions.append(val_X_for_canon > Int(0)) # Constraint for canonical DFI
        all_defining_assertions.append(val_X_for_canon < current_S_val_sym) # Constraint for canonical DFI
        all_defining_assertions.append(Not(X_canon_repr["is_zero"]))
        all_defining_assertions.append(Not(X_canon_repr["is_areo"]))
    else: 
        all_defining_assertions.append(
            Ite(is_X_L_ZS, 
                And(X_canon_repr["is_zero"], Not(X_canon_repr["is_areo"]), Not(X_canon_repr["is_finite"])),
            Ite(is_X_L_AS, 
                And(X_canon_repr["is_areo"], Equals(X_canon_repr["val"], current_S_val_sym), Not(X_canon_repr["is_zero"]), Not(X_canon_repr["is_finite"])),
                And(X_canon_repr["is_finite"], Equals(X_canon_repr["val"], val_X_for_canon),
                    val_X_for_canon > Int(0), val_X_for_canon < current_S_val_sym, Not(X_canon_repr["is_zero"]), Not(X_canon_repr["is_areo"])) 
            ))
        )

    val_Y_for_canon = Y_L_val_sym - P_A_val_sym
    is_Y_L_ZS = is_local_ZS_val(Y_L_val_sym, P_A_val_sym) # Now defined
    is_Y_L_AS = is_local_AS_val(Y_L_val_sym, P_B_val_sym) # Now defined

    if Y_L_kind_force == "ZS":
        all_defining_assertions.append(Y_canon_repr["is_zero"])
        all_defining_assertions.append(Not(Y_canon_repr["is_areo"]))
        all_defining_assertions.append(Not(Y_canon_repr["is_finite"]))
    elif Y_L_kind_force == "AS":
        all_defining_assertions.append(Y_canon_repr["is_areo"])
        all_defining_assertions.append(Equals(Y_canon_repr["val"], current_S_val_sym))
        all_defining_assertions.append(Not(Y_canon_repr["is_zero"]))
        all_defining_assertions.append(Not(Y_canon_repr["is_finite"]))
    elif Y_L_kind_force == "DFI":
        all_defining_assertions.append(Y_canon_repr["is_finite"])
        all_defining_assertions.append(Equals(Y_canon_repr["val"], val_Y_for_canon))
        all_defining_assertions.append(val_Y_for_canon > Int(0))
        all_defining_assertions.append(val_Y_for_canon < current_S_val_sym)
        all_defining_assertions.append(Not(Y_canon_repr["is_zero"]))
        all_defining_assertions.append(Not(Y_canon_repr["is_areo"]))
    else: 
        all_defining_assertions.append(
            Ite(is_Y_L_ZS, 
                And(Y_canon_repr["is_zero"], Not(Y_canon_repr["is_areo"]), Not(Y_canon_repr["is_finite"])),
            Ite(is_Y_L_AS, 
                And(Y_canon_repr["is_areo"], Equals(Y_canon_repr["val"], current_S_val_sym), Not(Y_canon_repr["is_zero"]), Not(Y_canon_repr["is_finite"])),
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
    print("====== AVC Relativistic Division S=2 Commutativity Hardcore Test ======\n")

    s = Solver(name="z3")
    current_S_smt = Int(LOCAL_SPAN_S_PY) # Fixed Span S=2

    PA_val = Symbol("PA_val_s2h", solver_INT_TYPE) 
    PB_val = Symbol("PB_val_s2h", solver_INT_TYPE)
    
    s.add_assertion(Equals(PA_val, Int(DEFAULT_P_A_OFFSET)))
    s.add_assertion(Equals(PB_val, PA_val + current_S_smt))

    # Define the specific local values for the DFI/ZS case
    # Case 1: La = DFI_L(P_A+1), Lb = ZS_L(P_A)
    # For S=2, P_A+1 is the only DFI.
    La_val_case1 = PA_val + Int(1) # This represents Local DFI with value P_A+1
    Lb_val_case1 = PA_val       # This represents Local ZS with value P_A

    print(f"--- Testing RD-1 Commutativity S=2 - HARDCORE Scenario: DFI_L / ZS_L ---")
    s.push()
    # Assert specific values for this test (they are effectively concrete relative to PA_val)
    # The define_local_op_direct_span_result will use these values and forced kinds.

    op_name_ab_c1 = f"s2h_ab_dfi_div_zs"
    op_name_ba_c1 = f"s2h_ba_zs_div_dfi"

    res_dfi_div_zs_dict = define_local_op_direct_span_result(
        define_raw_div_canonical_result, 
        La_val_case1, Lb_val_case1, 
        PA_val, PB_val, op_name_ab_c1,
        X_L_kind_force="DFI", Y_L_kind_force="ZS" 
    )
    res_zs_div_dfi_dict = define_local_op_direct_span_result(
        define_raw_div_canonical_result,
        Lb_val_case1, La_val_case1, 
        PA_val, PB_val, op_name_ba_c1,
        X_L_kind_force="ZS", Y_L_kind_force="DFI" 
    )
    
    property_comm_c1 = avc_equiv_local_val(
        res_dfi_div_zs_dict["val_L_sym"], 
        res_zs_div_dfi_dict["val_L_sym"], 
        PA_val, PB_val
    )
    
    all_assertions_c1 = res_dfi_div_zs_dict["defining_assertions"] + \
                        res_zs_div_dfi_dict["defining_assertions"]
    
    # To print concrete local values in case of failure
    La_val_c1_concrete = Symbol("La_val_c1_val", solver_INT_TYPE)
    Lb_val_c1_concrete = Symbol("Lb_val_c1_val", solver_INT_TYPE)
    s.add_assertion(Equals(La_val_c1_concrete, La_val_case1))
    s.add_assertion(Equals(Lb_val_c1_concrete, Lb_val_case1))

    prove_or_find_counterexample(s, f"RD-1 Commutativity S=2 Hardcore - DFI_L / ZS_L",
                                 all_assertions_c1,
                                 property_comm_c1, 
                                 model_vars_to_print=[PA_val, PB_val, La_val_c1_concrete, Lb_val_c1_concrete, 
                                                      res_dfi_div_zs_dict["val_L_sym"], 
                                                      res_zs_div_dfi_dict["val_L_sym"]],
                                 op_result_dicts_for_debug=[res_dfi_div_zs_dict, res_zs_div_dfi_dict])
    s.pop()

    # Case 2: La = DFI_L(P_A+1), Lb = AS_L(P_B)
    La_val_case2 = PA_val + Int(1)
    Lb_val_case2 = PB_val

    print(f"\n--- Testing RD-1 Commutativity S=2 - HARDCORE Scenario: DFI_L / AS_L ---")
    s.push()
    op_name_ab_c2 = f"s2h_ab_dfi_div_as"
    op_name_ba_c2 = f"s2h_ba_as_div_dfi"

    res_dfi_div_as_dict = define_local_op_direct_span_result(
        define_raw_div_canonical_result,
        La_val_case2, Lb_val_case2,
        PA_val, PB_val, op_name_ab_c2,
        X_L_kind_force="DFI", Y_L_kind_force="AS"
    )
    res_as_div_dfi_dict = define_local_op_direct_span_result(
        define_raw_div_canonical_result,
        Lb_val_case2, La_val_case2, 
        PA_val, PB_val, op_name_ba_c2,
        X_L_kind_force="AS", Y_L_kind_force="DFI"
    )
    property_comm_c2 = avc_equiv_local_val(
        res_dfi_div_as_dict["val_L_sym"],
        res_as_div_dfi_dict["val_L_sym"],
        PA_val, PB_val
    )
    all_assertions_c2 = res_dfi_div_as_dict["defining_assertions"] + \
                        res_as_div_dfi_dict["defining_assertions"]
    
    La_val_c2_concrete = Symbol("La_val_c2_val", solver_INT_TYPE)
    Lb_val_c2_concrete = Symbol("Lb_val_c2_val", solver_INT_TYPE)
    s.add_assertion(Equals(La_val_c2_concrete, La_val_case2))
    s.add_assertion(Equals(Lb_val_c2_concrete, Lb_val_case2))

    prove_or_find_counterexample(s, f"RD-1 Commutativity S=2 Hardcore - DFI_L / AS_L",
                                 all_assertions_c2,
                                 property_comm_c2,
                                 model_vars_to_print=[PA_val, PB_val, La_val_c2_concrete, Lb_val_c2_concrete,
                                                      res_dfi_div_as_dict["val_L_sym"],
                                                      res_as_div_dfi_dict["val_L_sym"]],
                                 op_result_dicts_for_debug=[res_dfi_div_as_dict, res_as_div_dfi_dict])
    s.pop()

    # Case 3: La = ZS_L(P_A), Lb = AS_L(P_B)
    La_val_case3 = PA_val
    Lb_val_case3 = PB_val
    print(f"\n--- Testing RD-1 Commutativity S=2 - HARDCORE Scenario: ZS_L / AS_L ---")
    s.push()
    op_name_ab_c3 = f"s2h_ab_zs_div_as"
    op_name_ba_c3 = f"s2h_ba_as_div_zs"

    res_zs_div_as_dict = define_local_op_direct_span_result(
        define_raw_div_canonical_result,
        La_val_case3, Lb_val_case3,
        PA_val, PB_val, op_name_ab_c3,
        X_L_kind_force="ZS", Y_L_kind_force="AS"
    )
    res_as_div_zs_dict = define_local_op_direct_span_result(
        define_raw_div_canonical_result,
        Lb_val_case3, La_val_case3, 
        PA_val, PB_val, op_name_ba_c3,
        X_L_kind_force="AS", Y_L_kind_force="ZS"
    )
    property_comm_c3 = avc_equiv_local_val(
        res_zs_div_as_dict["val_L_sym"],
        res_as_div_zs_dict["val_L_sym"],
        PA_val, PB_val
    )
    all_assertions_c3 = res_zs_div_as_dict["defining_assertions"] + \
                        res_as_div_zs_dict["defining_assertions"]
    
    La_val_c3_concrete = Symbol("La_val_c3_val", solver_INT_TYPE)
    Lb_val_c3_concrete = Symbol("Lb_val_c3_val", solver_INT_TYPE)
    s.add_assertion(Equals(La_val_c3_concrete, La_val_case3))
    s.add_assertion(Equals(Lb_val_c3_concrete, Lb_val_case3))
    
    prove_or_find_counterexample(s, f"RD-1 Commutativity S=2 Hardcore - ZS_L / AS_L",
                                 all_assertions_c3,
                                 property_comm_c3,
                                 model_vars_to_print=[PA_val, PB_val, La_val_c3_concrete, Lb_val_c3_concrete,
                                                      res_zs_div_as_dict["val_L_sym"],
                                                      res_as_div_zs_dict["val_L_sym"]],
                                 op_result_dicts_for_debug=[res_zs_div_as_dict, res_as_div_zs_dict])
    s.pop()

    del s
    print("\n====== AVC Relativistic Division S=2 Commutativity Hardcore Test Complete ======")