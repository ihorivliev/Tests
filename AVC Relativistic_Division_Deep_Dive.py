from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST_WITH_S2 = [2, 3, 5, 7] # Local Spans S to test
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

# --- Phase 2: Canonical Raw Operations Definitions (Parameterized by current_omega_smt) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) 
    )))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) 
    )))
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
    formulas.append(Implies(divisor_is_unio, # X / Unio -> Areo (Unio) 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), # Divisor is Finite(p2)
        Or( 
            And(i1["is_zero"], # ZS / F(p2) => ZS
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), 
            And(i1["is_areo"],  # AS / F(p2) => AS
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(i1["is_finite"], # F(p1) / F(p2)
                # Assert the division algorithm for integers
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), 
                    rem_sym >= Int(0), 
                    rem_sym < i2["val"]), # i2["val"] > 0 is from i2's own constraints 
                
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)), # Divides cleanly to a Positive Natural
                    Ite(q_sym >= current_omega_smt, # Apply Omega threshold to quotient
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # Result is Areo 
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym)) # Result is Finite(quotient) 
                    ), 
                    # Does not divide cleanly to a PosNat (remainder != 0 or quotient <= 0)
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) # Result is Areo (Unio)
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

    # For debugging the mapping:
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
    print("====== AVC Relativistic Division Deep Dive ======\n")

    PA_val = Symbol("PA_val_rdd", solver_INT_TYPE) # rdd for RelativisticDivisionDive
    PB_val = Symbol("PB_val_rdd", solver_INT_TYPE)
    S_val = Symbol("S_val_rdd", solver_INT_TYPE)

    La_L_val = Symbol("La_L_rdd", solver_INT_TYPE)
    Lb_L_val = Symbol("Lb_L_rdd", solver_INT_TYPE)
    Lc_L_val = Symbol("Lc_L_rdd", solver_INT_TYPE)

    for current_span_py in OMEGA_VARIANTS_TO_TEST_WITH_S2:
        s = Solver(name="z3")
        current_S_smt = Int(current_span_py)
        print(f"\n\n===== TESTING RELATIVISTIC DIVISION WITH LOCAL SPAN S = {current_span_py} =====\n")

        s.add_assertion(Equals(PA_val, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(S_val, current_S_smt))
        s.add_assertion(S_val > Int(0)) 
        s.add_assertion(Equals(PB_val, PA_val + S_val))
        
        # Common setup for general local values La, Lb, Lc
        general_inputs_setup = [
            And(La_L_val >= PA_val, La_L_val <= PB_val),
            And(Lb_L_val >= PA_val, Lb_L_val <= PB_val),
            And(Lc_L_val >= PA_val, Lc_L_val <= PB_val)
        ]
        s.add_assertions(general_inputs_setup) # Assert once for all tests with this span

        # --- Test RD-0: Well-Definedness of raw_div_local_direct_span ---
        L_i1 = Symbol("L_i1_rdd", solver_INT_TYPE); L_j1 = Symbol("L_j1_rdd", solver_INT_TYPE)
        L_i2 = Symbol("L_i2_rdd", solver_INT_TYPE); L_j2 = Symbol("L_j2_rdd", solver_INT_TYPE)
        wd_setup = [
            And(L_i1 >= PA_val, L_i1 <= PB_val), And(L_j1 >= PA_val, L_j1 <= PB_val),
            And(L_i2 >= PA_val, L_i2 <= PB_val), And(L_j2 >= PA_val, L_j2 <= PB_val),
            avc_equiv_local_val(L_i1, L_i2, PA_val, PB_val),
            avc_equiv_local_val(L_j1, L_j2, PA_val, PB_val)
        ]
        res1_wd_div_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, L_i1, L_j1, PA_val, PB_val, f"rd0_res1_s{current_span_py}")
        res2_wd_div_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, L_i2, L_j2, PA_val, PB_val, f"rd0_res2_s{current_span_py}")
        prop_rd0 = avc_equiv_local_val(res1_wd_div_dict["val_L_sym"], res2_wd_div_dict["val_L_sym"], PA_val, PB_val)
        prove_or_find_counterexample(s, f"RD-0 raw_div_local respects avc_equiv_local (S={current_span_py})",
                                     wd_setup + res1_wd_div_dict["defining_assertions"] + res2_wd_div_dict["defining_assertions"],
                                     prop_rd0, 
                                     model_vars_to_print=[PA_val, PB_val, S_val, L_i1, L_j1, L_i2, L_j2, res1_wd_div_dict["val_L_sym"], res2_wd_div_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[res1_wd_div_dict, res2_wd_div_dict])

        # --- Test RD-1: Commutativity of raw_div_local_direct_span ---
        res_ab_div_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, Lb_L_val, PA_val, PB_val, f"rd1_ab_s{current_span_py}")
        res_ba_div_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, Lb_L_val, La_L_val, PA_val, PB_val, f"rd1_ba_s{current_span_py}")
        prop_rd1 = avc_equiv_local_val(res_ab_div_dict["val_L_sym"], res_ba_div_dict["val_L_sym"], PA_val, PB_val)
        prove_or_find_counterexample(s, f"RD-1 Commutativity of raw_div_local (S={current_span_py})",
                                     res_ab_div_dict["defining_assertions"] + res_ba_div_dict["defining_assertions"],
                                     prop_rd1, 
                                     model_vars_to_print=[PA_val, PB_val, S_val, La_L_val, Lb_L_val, res_ab_div_dict["val_L_sym"], res_ba_div_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_ab_div_dict, res_ba_div_dict])

        # --- Test RD-2: Associativity of raw_div_local_direct_span ---
        # (La / Lb) / Lc  vs La / (Lb / Lc)
        div_ab_L_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, Lb_L_val, PA_val, PB_val, f"rd2_div_ab_s{current_span_py}")
        lhs_div_L_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, div_ab_L_dict["val_L_sym"], Lc_L_val, PA_val, PB_val, f"rd2_lhs_s{current_span_py}")
        div_bc_L_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, Lb_L_val, Lc_L_val, PA_val, PB_val, f"rd2_div_bc_s{current_span_py}")
        rhs_div_L_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, div_bc_L_dict["val_L_sym"], PA_val, PB_val, f"rd2_rhs_s{current_span_py}")
        prop_rd2 = avc_equiv_local_val(lhs_div_L_dict["val_L_sym"], rhs_div_L_dict["val_L_sym"], PA_val, PB_val)
        all_rd2_asserts = div_ab_L_dict["defining_assertions"] + lhs_div_L_dict["defining_assertions"] + \
                          div_bc_L_dict["defining_assertions"] + rhs_div_L_dict["defining_assertions"]
        prove_or_find_counterexample(s, f"RD-2 Associativity of raw_div_local (S={current_span_py})",
                                     all_rd2_asserts, prop_rd2,
                                     model_vars_to_print=[PA_val, PB_val, S_val, La_L_val, Lb_L_val, Lc_L_val, lhs_div_L_dict["val_L_sym"], rhs_div_L_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[div_ab_L_dict, lhs_div_L_dict, div_bc_L_dict, rhs_div_L_dict])
        
        # --- Test RD-3: (La * Lb) / Lb ~ La ---
        s.push() # New context for Lb constrained to be DFI
        s.add_assertion(is_local_DFI_val(Lb_L_val, PA_val, PB_val)) # Lb is DFI
        
        prod_ab_mul_dict = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, Lb_L_val, PA_val, PB_val, f"rd3_prod_ab_s{current_span_py}")
        res_div_lb_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, prod_ab_mul_dict["val_L_sym"], Lb_L_val, PA_val, PB_val, f"rd3_res_div_s{current_span_py}")
        prop_rd3 = avc_equiv_local_val(res_div_lb_dict["val_L_sym"], La_L_val, PA_val, PB_val)
        all_rd3_asserts = prod_ab_mul_dict["defining_assertions"] + res_div_lb_dict["defining_assertions"]
        prove_or_find_counterexample(s, f"RD-3 (La*_L Lb_DFI)/_L Lb_DFI ~_L La (S={current_span_py})",
                                     all_rd3_asserts, prop_rd3,
                                     model_vars_to_print=[PA_val, PB_val, S_val, La_L_val, Lb_L_val, prod_ab_mul_dict["val_L_sym"], res_div_lb_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[prod_ab_mul_dict, res_div_lb_dict])
        s.pop()

        # --- Test RD-4: (La / Lb) * Lb ~ La (Lb is DFI; La/Lb results in DFI) ---
        s.push()
        s.add_assertion(is_local_DFI_val(Lb_L_val, PA_val, PB_val)) # Lb is DFI
        
        div_ab_clean_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, Lb_L_val, PA_val, PB_val, f"rd4_div_ab_s{current_span_py}")
        # Add constraint that the division result is DFI_L
        s.add_assertion(is_local_DFI_val(div_ab_clean_dict["val_L_sym"], PA_val, PB_val)) # Crucial constraint
        
        res_mul_lb_dict = define_local_op_direct_span_result(define_raw_mul_canonical_result, div_ab_clean_dict["val_L_sym"], Lb_L_val, PA_val, PB_val, f"rd4_res_mul_s{current_span_py}")
        prop_rd4 = avc_equiv_local_val(res_mul_lb_dict["val_L_sym"], La_L_val, PA_val, PB_val)
        all_rd4_asserts = div_ab_clean_dict["defining_assertions"] + res_mul_lb_dict["defining_assertions"]
        prove_or_find_counterexample(s, f"RD-4 (La/_L Lb_DFI)*_L Lb_DFI ~_L La (if La/_L Lb_DFI is DFI_L) (S={current_span_py})",
                                     all_rd4_asserts, prop_rd4,
                                     model_vars_to_print=[PA_val, PB_val, S_val, La_L_val, Lb_L_val, div_ab_clean_dict["val_L_sym"], res_mul_lb_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[div_ab_clean_dict, res_mul_lb_dict])
        s.pop()
        
        # --- Test RD-7: Behavior with Local Poles as Divisor ---
        # RD-7.1: La_L /_L PA_val (Local ZS)
        res_div_by_zs_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, PA_val, PA_val, PB_val, f"rd71_div_zs_s{current_span_py}")
        prop_rd71 = is_local_AS_val(res_div_by_zs_dict["val_L_sym"], PB_val) # Expect Local AS
        prove_or_find_counterexample(s, f"RD-7.1 La_L /_L PA_val (Local ZS) ~ Local AS (S={current_span_py})",
                                     res_div_by_zs_dict["defining_assertions"], prop_rd71,
                                     model_vars_to_print=[PA_val, PB_val, S_val, La_L_val, res_div_by_zs_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_div_by_zs_dict])

        # RD-7.2: La_L /_L PB_val (Local AS)
        res_div_by_as_dict = define_local_op_direct_span_result(define_raw_div_canonical_result, La_L_val, PB_val, PA_val, PB_val, f"rd72_div_as_s{current_span_py}")
        prop_rd72 = is_local_AS_val(res_div_by_as_dict["val_L_sym"], PB_val) # Expect Local AS
        prove_or_find_counterexample(s, f"RD-7.2 La_L /_L PB_val (Local AS) ~ Local AS (S={current_span_py})",
                                     res_div_by_as_dict["defining_assertions"], prop_rd72,
                                     model_vars_to_print=[PA_val, PB_val, S_val, La_L_val, res_div_by_as_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_div_by_as_dict])

        del s 
        print("-" * 80)

    print("\n====== AVC Relativistic Division Deep Dive Complete ======")