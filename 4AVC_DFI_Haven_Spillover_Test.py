from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [2, 3, 5, 7] # Local Spans S to test
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

# --- Phase 2: Canonical Raw Operations Definitions ---
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
            And(X_canon_repr["is_areo"], Equals(X_canon_repr["val"], current_S_val_sym), Not(X_canon_repr["is_zero"]), Not(X_canon_repr["is_finite"])), 
            And(X_canon_repr["is_finite"], Equals(X_canon_repr["val"], val_X_for_canon),
                val_X_for_canon > Int(0), val_X_for_canon < current_S_val_sym, Not(X_canon_repr["is_zero"]), Not(X_canon_repr["is_areo"])) 
        ))
    )
    val_Y_for_canon = Y_L_val_sym - P_A_val_sym
    all_defining_assertions.append(
        Ite(is_local_ZS_val(Y_L_val_sym, P_A_val_sym),
            And(Y_canon_repr["is_zero"], Not(Y_canon_repr["is_areo"]), Not(Y_canon_repr["is_finite"])),
        Ite(is_local_AS_val(Y_L_val_sym, P_B_val_sym),
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
    print("====== AVC DFI Haven Spillover Test ======\n")

    P_A_val_sym = Symbol("PA_spill", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_spill", solver_INT_TYPE)
    S_val_sym = Symbol("S_spill", solver_INT_TYPE) # Explicit Span symbol for clarity in debug

    La_L_val = Symbol("La_L_spill", solver_INT_TYPE)
    Lb_L_val = Symbol("Lb_L_spill", solver_INT_TYPE)
    Lc_L_val = Symbol("Lc_L_spill", solver_INT_TYPE)

    for current_span_py in OMEGA_VARIANTS_TO_TEST:
        s = Solver(name="z3")
        current_S_smt = Int(current_span_py)
        print(f"\n\n===== TESTING DFI HAVEN SPILLOVER WITH LOCAL SPAN S = {current_span_py} =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(S_val_sym, current_S_smt)) # Define S_val_sym
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + S_val_sym))
        s.add_assertion(S_val_sym > Int(0)) 

        # Inputs La, Lb, Lc are symbolic local DFIs
        base_dfi_inputs_setup = [
            is_local_DFI_val(La_L_val, P_A_val_sym, P_B_val_sym),
            is_local_DFI_val(Lb_L_val, P_A_val_sym, P_B_val_sym),
            is_local_DFI_val(Lc_L_val, P_A_val_sym, P_B_val_sym)
        ]

        # --- Test LDS-1: Left Distributivity with Sum_BC Spillover to AS_L ---
        print(f"--- Test LDS-1: Left Distrib with Sum_BC -> AS_L (S={current_span_py}) ---")
        s.push()
        s.add_assertions(base_dfi_inputs_setup)
        
        # Define sum_bc_L = Lb_L_val +_L Lc_L_val
        sum_bc_LDS1 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "lds1_sum_bc")
        # Critical Constraint: Force this sum to be Local AS_L
        s.add_assertion(is_local_AS_val(sum_bc_LDS1["val_L_sym"], P_B_val_sym))

        # LHS: La_L_val *_L sum_bc_LDS1 (which is AS_L)
        lhs_LDS1 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, sum_bc_LDS1["val_L_sym"], P_A_val_sym, P_B_val_sym, "lds1_lhs")

        # RHS: (La_L_val *_L Lb_L_val) +_L (La_L_val *_L Lc_L_val)
        prod_ab_LDS1 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "lds1_prod_ab")
        prod_ac_LDS1 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "lds1_prod_ac")
        rhs_LDS1 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ab_LDS1["val_L_sym"], prod_ac_LDS1["val_L_sym"], P_A_val_sym, P_B_val_sym, "lds1_rhs")
        
        prop_LDS1 = avc_equiv_local_val(lhs_LDS1["val_L_sym"], rhs_LDS1["val_L_sym"], P_A_val_sym, P_B_val_sym)
        all_LDS1_assertions = sum_bc_LDS1["defining_assertions"] + lhs_LDS1["defining_assertions"] + \
                              prod_ab_LDS1["defining_assertions"] + prod_ac_LDS1["defining_assertions"] + rhs_LDS1["defining_assertions"]
        
        prove_or_find_counterexample(s, f"LDS-1 Left Distrib (Sum_BC forced AS_L, S={current_span_py})",
                                     all_LDS1_assertions, prop_LDS1,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, La_L_val, Lb_L_val, Lc_L_val, 
                                                          sum_bc_LDS1["val_L_sym"], lhs_LDS1["val_L_sym"], 
                                                          prod_ab_LDS1["val_L_sym"], prod_ac_LDS1["val_L_sym"], rhs_LDS1["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_bc_LDS1, lhs_LDS1, prod_ab_LDS1, prod_ac_LDS1, rhs_LDS1])
        s.pop()

        # --- Test RDS-1: Right Distributivity with Sum_AB Spillover to AS_L ---
        print(f"\n--- Test RDS-1: Right Distrib with Sum_AB -> AS_L (S={current_span_py}) ---")
        s.push()
        s.add_assertions(base_dfi_inputs_setup)

        # Define sum_ab_L = La_L_val +_L Lb_L_val
        sum_ab_RDS1 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_L_val, Lb_L_val, P_A_val_sym, P_B_val_sym, "rds1_sum_ab")
        # Critical Constraint: Force this sum to be Local AS_L
        s.add_assertion(is_local_AS_val(sum_ab_RDS1["val_L_sym"], P_B_val_sym))

        # LHS: sum_ab_RDS1 (which is AS_L) *_L Lc_L_val
        lhs_RDS1 = define_local_op_direct_span_result(define_raw_mul_canonical_result, sum_ab_RDS1["val_L_sym"], Lc_L_val, P_A_val_sym, P_B_val_sym, "rds1_lhs")

        # RHS: (La_L_val *_L Lc_L_val) +_L (Lb_L_val *_L Lc_L_val)
        prod_ac_RDS1 = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "rds1_prod_ac")
        prod_bc_RDS1 = define_local_op_direct_span_result(define_raw_mul_canonical_result, Lb_L_val, Lc_L_val, P_A_val_sym, P_B_val_sym, "rds1_prod_bc")
        rhs_RDS1 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ac_RDS1["val_L_sym"], prod_bc_RDS1["val_L_sym"], P_A_val_sym, P_B_val_sym, "rds1_rhs")

        prop_RDS1 = avc_equiv_local_val(lhs_RDS1["val_L_sym"], rhs_RDS1["val_L_sym"], P_A_val_sym, P_B_val_sym)
        all_RDS1_assertions = sum_ab_RDS1["defining_assertions"] + lhs_RDS1["defining_assertions"] + \
                              prod_ac_RDS1["defining_assertions"] + prod_bc_RDS1["defining_assertions"] + rhs_RDS1["defining_assertions"]

        prove_or_find_counterexample(s, f"RDS-1 Right Distrib (Sum_AB forced AS_L, S={current_span_py})",
                                     all_RDS1_assertions, prop_RDS1,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, S_val_sym, La_L_val, Lb_L_val, Lc_L_val,
                                                          sum_ab_RDS1["val_L_sym"], lhs_RDS1["val_L_sym"],
                                                          prod_ac_RDS1["val_L_sym"], prod_bc_RDS1["val_L_sym"], rhs_RDS1["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_RDS1, lhs_RDS1, prod_ac_RDS1, prod_bc_RDS1, rhs_RDS1])
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC DFI Haven Spillover Test Complete ======")