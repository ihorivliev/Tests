from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7] 
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
                                res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode:
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
                            Ite(val_sum >= current_omega_eff_c_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) 
                            )))
    return And(formulas)

def define_smart_raw_add_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                          result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode:
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
                            Ite(val_prod >= current_omega_eff_c_smt, And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
    return And(formulas)

def define_raw_mul_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                    result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

def raw_div_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode: 
    formulas = [] 
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE) 
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE) 
    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])
    formulas.append(Implies(divisor_is_unio, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), 
        Or( 
            And(i1["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), 
            And(i1["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(i1["is_finite"], 
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), rem_sym >= Int(0), rem_sym < i2["val"]), 
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)), 
                    Ite(q_sym >= current_omega_eff_c_smt, 
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))), 
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) )))))
    return And(formulas)

def define_raw_div_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                     result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_div_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

def raw_sub_from_Unio_Areo_aspect_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                                res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode:
    is_i1_unio_component = Or(i1["is_zero"], i1["is_areo"])
    result_as_AS_C = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]))
    # This implies res["val"] would be current_omega_eff_c_smt if res is AS_C,
    # which should be handled by res's own constraints if its kind is set to AS_C.
    # The definition of AS_C should tie its val to current_omega_eff_c_smt.

    # Core definition based on Postulate 6.3 and P2.2.iv: Unio - DFI -> AS
    core_def = Implies(And(is_i1_unio_component, i2["is_finite"]), result_as_AS_C)

    # Totality for SMT: Other cases also default to AS_C for this specific operation
    # This means any use of this op where i1 is not Unio, or i2 is not DFI, yields AS_C.
    # This simplifies analysis of this specific op but means it's not a general subtraction.
    full_def = Ite(
        And(is_i1_unio_component, i2["is_finite"]),
        result_as_AS_C, 
        result_as_AS_C 
    )
    # Add constraint that if result is AS_C, its value is current_omega_eff_c_smt
    # This is implicitly handled by create_intensity_representation + map_local_to_adaptive for AS_C kind
    # but can be made explicit here too for res.
    # No, this is circular. The logic builder for res should not re-assert res.val based on res.is_areo.
    # That's for the create_intensity_representation and mapping functions.
    # The logic builder only sets the *kind* flags for res.
    # The val for AS_C is defined when the canonical AS_C representation is created or mapped to.
    # Let's assume res_repr["val"] is appropriately handled when res_repr["is_areo"] becomes True.
    return full_def


def define_raw_sub_from_Unio_Areo_aspect_canonical_result(
    i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
    result_name_prefix: str, current_omega_eff_c_smt: FNode
) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    # Add specific val constraint if res becomes AS
    # This should be done when AS_C is defined, not here. The logic builder just determines the kind.
    # The canonical representation of AS_C should have its val tied to current_omega_eff_c_smt
    # This happens in map_local_to_adaptive_archetype_input_repr for inputs,
    # and must be ensured for results by op_canonical_result_definer.
    # The create_intensity_representation doesn't know about omega.
    # Okay, the raw_sub_from_Unio_Areo_aspect_logic_builder defines res.is_areo.
    # The define_local_op_adaptive_archetype_result will create Res_canon_repr using create_intensity_representation.
    # Then Res_canon_repr['definition'] = raw_sub_logic_builder(...).
    # Then it maps Res_canon_repr back to local. When Res_canon_repr.is_areo is true,
    # map_adaptive_archetype_result_to_local will use P_B_val_sym.
    # The actual val of Res_canon_repr if it's AS_C should implicitly be Omega_eff_C_sym.
    # This is handled by Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym)) in map_local_to_adaptive...
    # And it should also apply to results of canonical operations if they are AS_C.
    # The define_xxx_canonical_result functions must ensure this for their results.
    # For now, the logic builder only determines the kind flags.
    res_repr["definition"] = raw_sub_from_Unio_Areo_aspect_logic_builder(
        i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt
    )
    # Add assertion: if this operation makes 'res' an AreoState, its value must be the current omega.
    # This is essential because create_intensity_representation doesn't know omega.
    # This might be tricky as it's about the *result* of the logic builder.
    # Better to ensure that any AS_C state has its value tied to its omega.
    # The most robust place is in define_local_op_adaptive_archetype_result
    # where Res_canon_repr is created, we add Implies(Res_canon_repr["is_areo"], Equals(Res_canon_repr["val"], Omega_eff_C_sym))
    # This is already done for inputs in map_local_to_adaptive_archetype_input_repr.
    # For results of canonical operations, it's implicit if their logic (like sum >= omega) sets is_areo.
    # The val for AS_C is actually only used if it were Finite; for ZS/AS, the kind is enough for mapping back.
    # So, the current setup where logic_builder sets kind flags is okay.
    return res_repr

# --- Phase 3: Local Frame, Adaptive Omega, and Mappings ---
# (Copied and verified from AVC_Adaptive_Refined_Test.py / AVC_Adaptive_Division_Properties_Test.py)
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

def determine_effective_canonical_omega(S_val_sym: FNode) -> FNode:
    return Ite(Equals(S_val_sym, Int(1)), Int(1),
           Ite(Equals(S_val_sym, Int(2)), Int(2),
                                           Int(3))) 

def map_local_to_adaptive_archetype_input_repr(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode, 
    arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    arch_repr = create_intensity_representation(arch_name_prefix)
    is_L_ZS_cond = is_local_ZS_val(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS_val(Local_val_sym, PB_sym)
    is_L_DFI_cond = is_local_DFI_val(Local_val_sym, PA_sym, PB_sym) 
    kind_assertions = [
        arch_repr["constraints"], 
        Implies(is_L_ZS_cond, And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))),
        Implies(is_L_AS_cond, And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))),
        Implies(is_L_DFI_cond, And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"]))
    ]
    val_assertions = [Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym))]
    val_if_omega_eff_is_2 = Int(1) 
    val_if_omega_eff_is_3 = Ite(Equals(Local_val_sym, PA_sym + Int(1)), Int(1), Int(2))                                 
    val_assertions.append(
        Implies(arch_repr["is_finite"], 
            Ite(Equals(Omega_eff_C_sym, Int(1)), FALSE(), 
            Ite(Equals(Omega_eff_C_sym, Int(2)), Equals(arch_repr["val"], val_if_omega_eff_is_2),
                 Equals(arch_repr["val"], val_if_omega_eff_is_3)))))
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))
    return arch_repr, kind_assertions + val_assertions

def map_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], PA_sym: FNode, PB_sym: FNode, S_sym: FNode, Omega_eff_C_sym: FNode 
) -> FNode:
    val_from_fp_if_omega_eff_is_1 = PB_sym 
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))
    val_from_fp_if_omega_eff_is_3 = \
        Ite(Equals(S_sym, Int(1)), PB_sym, 
        Ite(Equals(S_sym, Int(2)), 
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym), 
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym - Int(1))))
    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                    Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         val_from_fp_if_omega_eff_is_3))
    return Ite(Arch_Res_Repr["is_zero"], PA_sym, Ite(Arch_Res_Repr["is_areo"], PB_sym, fp_result_val))

def define_local_op_adaptive_archetype_result(
    op_canonical_result_definer: Callable, X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    S_val_sym = P_B_val_sym - P_A_val_sym
    Omega_eff_C_sym = determine_effective_canonical_omega(S_val_sym)
    X_canon_repr, x_canon_assertions = map_local_to_adaptive_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_xc")
    defining_assertions_for_local_op.extend(x_canon_assertions)
    Y_canon_repr, y_canon_assertions = map_local_to_adaptive_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_yc")
    defining_assertions_for_local_op.extend(y_canon_assertions)
    
    # Explicitly assert val for AS_C inputs if they are AS_C
    # This is normally handled by map_local_to_adaptive_archetype_input_repr's val_assertions
    # defining_assertions_for_local_op.append(Implies(X_canon_repr["is_areo"], Equals(X_canon_repr["val"], Omega_eff_C_sym)))
    # defining_assertions_for_local_op.append(Implies(Y_canon_repr["is_areo"], Equals(Y_canon_repr["val"], Omega_eff_C_sym)))
    
    Res_canon_repr = op_canonical_result_definer(X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", Omega_eff_C_sym)
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])
    # Crucially, if Res_canon_repr is determined to be AS_C by the op_logic_builder, its val must be Omega_eff_C_sym
    # This ensures that AS_C results from ops have the correct conceptual value for that archetype.
    defining_assertions_for_local_op.append(Implies(Res_canon_repr["is_areo"], Equals(Res_canon_repr["val"], Omega_eff_C_sym)))


    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym)
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
    # (Same as in AVC_Adaptive_Division_Properties_Test.py)
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
                    name_to_print = ""
                    if var_item.is_symbol():
                        name_to_print = var_item.symbol_name()
                    else:
                        # For complex FNodes (like Ite, And, etc.), use their string representation
                        # or a custom description if you prefer.
                        name_to_print = f"Expression({str(var_item)})"
                    
                    value_str = "?"
                    try:
                        value_str = str(solver.get_value(var_item))
                    except Exception as e:
                        value_str = f"(Error getting value: {e})"
                    print(f"  {name_to_print}: {value_str}")
            
            if op_result_dicts_for_debug:
                print("  DEBUG Canonical Mappings/Results in Counterexample:")
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
                                    if local_val_sym_dbg and local_val_sym_dbg in solver.get_model(): print(f"        Local Input {local_val_key.split('_')[0]}: {local_val_sym_dbg.symbol_name()} = {solver.get_value(local_val_sym_dbg)}")
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
    print("====== AVC Adaptive Subtraction Interactions Test ======\n")

    P_A_val_sym = Symbol("PA_val_asubit", solver_INT_TYPE) # asubit for Adaptive Subtraction Interactions Test
    P_B_val_sym = Symbol("PB_val_asubit", solver_INT_TYPE)
    
    La_val_sym = Symbol("La_val_asubit", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val_asubit", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val_asubit", solver_INT_TYPE)

    Li1_val_sym = Symbol("Li1_val_asubit", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val_asubit", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val_asubit", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val_asubit", solver_INT_TYPE)

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S_py} (Adaptive Omega for Subtraction Interactions) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) 

        # --- L0-SubId: Foundational Re-verification ---
        print(f"--- Test L0-SubId (S={current_local_span_S_py}) ---")
        s.push() 
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))
        premise_L0SubId = And(avc_equiv_local_val(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym),
                             avc_equiv_local_val(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        op_L0SubId_r1 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L0SubId_r1")
        op_L0SubId_r2 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L0SubId_r2")
        conc_L0SubId = avc_equiv_local_val(op_L0SubId_r1["val_L_sym"], op_L0SubId_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.1-SubId raw_sub_local_adaptive respects avc_equiv (S={current_local_span_S_py})",
                                     [premise_L0SubId] + op_L0SubId_r1["defining_assertions"] + op_L0SubId_r2["defining_assertions"], conc_L0SubId,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L0SubId_r1["val_L_sym"],op_L0SubId_r2["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L0SubId_r1, op_L0SubId_r2])
        s.pop() 

        s.push() 
        s.add_assertion(is_local_DFI_val(Lc_val_sym, P_A_val_sym, P_B_val_sym)) 
        op_L02SubId = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, P_A_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L02SubId")
        conc_L02SubId = is_local_AS_val(op_L02SubId["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.2-SubId (ZS_L - DFI_L) ~ AS_L (S={current_local_span_S_py})",
                                     op_L02SubId["defining_assertions"], conc_L02SubId,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Lc_val_sym, op_L02SubId["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L02SubId])
        s.pop() 

        s.push() 
        s.add_assertion(is_local_DFI_val(Lc_val_sym, P_A_val_sym, P_B_val_sym)) 
        op_L03SubId = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, P_B_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L03SubId")
        conc_L03SubId = is_local_AS_val(op_L03SubId["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.3-SubId (AS_L - DFI_L) ~ AS_L (S={current_local_span_S_py})",
                                     op_L03SubId["defining_assertions"], conc_L03SubId,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Lc_val_sym, op_L03SubId["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L03SubId])
        s.pop() 
        # --- End L0-SubId ---

        dfi_L_abc_setup = [
            is_local_DFI_val(La_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI_val(Lc_val_sym, P_A_val_sym, P_B_val_sym)
        ]
        general_L_abc_setup = [
            And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym),
            And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym),
            And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym)
        ]

        # --- L1-SubId: Additive Inverse via Subtraction from Unio ---
        print(f"\n--- Test L1-SubId: DFI + (ZS_L - DFI) (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(dfi_L_abc_setup) # La, Lb, Lc are DFI. Using La for DFI.
        sub_res_L1 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, P_A_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L1SubId_sub")
        add_res_L1 = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, La_val_sym, sub_res_L1["val_L_sym"], P_A_val_sym, P_B_val_sym, "L1SubId_add")
        conc_L1SubId = avc_equiv_local_val(add_res_L1["val_L_sym"], P_A_val_sym, P_A_val_sym, P_B_val_sym) # ~ ZS_L
        prove_or_find_counterexample(s, f"L1-SubId DFI + (ZS_L-DFI) ~ ZS_L (S={current_local_span_S_py})",
                                     sub_res_L1["defining_assertions"] + add_res_L1["defining_assertions"], conc_L1SubId,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym, sub_res_L1["val_L_sym"], add_res_L1["val_L_sym"]],
                                     op_result_dicts_for_debug=[sub_res_L1, add_res_L1])
        s.pop()

        # --- L2-SubId: Zeroing via Subtraction from Self (Misuse of Op) ---
        print(f"\n--- Test L2-SubId: DFI - DFI (via UnioSub) (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(dfi_L_abc_setup) # La is DFI
        sub_res_L2 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, La_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L2SubId_sub")
        conc_L2SubId = avc_equiv_local_val(sub_res_L2["val_L_sym"], P_A_val_sym, P_A_val_sym, P_B_val_sym) # ~ ZS_L
        prove_or_find_counterexample(s, f"L2-SubId DFI - DFI (via UnioSub) ~ ZS_L (S={current_local_span_S_py})",
                                     sub_res_L2["defining_assertions"], conc_L2SubId,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym, sub_res_L2["val_L_sym"]],
                                     op_result_dicts_for_debug=[sub_res_L2])
        s.pop()

        # --- L3-SubId: Chained Op: (AS_L - DFI1)_AS + DFI2 ---
        print(f"\n--- Test L3-SubId: (AS_L-DFI1)+DFI2 (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(dfi_L_abc_setup) # La is DFI1, Lb is DFI2
        sub_res_L3 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, P_B_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L3SubId_sub")
        # s.add_assertion(is_local_AS_val(sub_res_L3["val_L_sym"], P_B_val_sym)) # This should be true from op def
        
        add_res_L3 = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, sub_res_L3["val_L_sym"], Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3SubId_add")
        
        # Expected result depends on span S for the add part
        expected_L3_res_val = Ite(Equals(current_local_span_S_smt, Int(1)), P_B_val_sym, Lb_val_sym) # AS+ZS/AS -> AS; AS+DFI -> DFI for S>=2

        conc_L3SubId = avc_equiv_local_val(add_res_L3["val_L_sym"], expected_L3_res_val, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L3-SubId (AS_L-DFI1)+DFI2 ~ Expected (S={current_local_span_S_py})",
                                     sub_res_L3["defining_assertions"] + add_res_L3["defining_assertions"], conc_L3SubId,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym, Lb_val_sym, sub_res_L3["val_L_sym"], add_res_L3["val_L_sym"], expected_L3_res_val],
                                     op_result_dicts_for_debug=[sub_res_L3, add_res_L3])
        s.pop()

        # --- L4-SubId: Chained Op: (AS_L - DFI1)_AS * DFI2 ---
        print(f"\n--- Test L4-SubId: (AS_L-DFI1)*DFI2 (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(dfi_L_abc_setup) # La is DFI1, Lb is DFI2
        sub_res_L4 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, P_B_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L4SubId_sub")
        mul_res_L4 = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, sub_res_L4["val_L_sym"], Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4SubId_mul")
        conc_L4SubId = is_local_AS_val(mul_res_L4["val_L_sym"], P_B_val_sym) # Expect AS_L * DFI_L -> AS_L
        prove_or_find_counterexample(s, f"L4-SubId (AS_L-DFI1)*DFI2 ~ AS_L (S={current_local_span_S_py})",
                                     sub_res_L4["defining_assertions"] + mul_res_L4["defining_assertions"], conc_L4SubId,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym, Lb_val_sym, sub_res_L4["val_L_sym"], mul_res_L4["val_L_sym"]],
                                     op_result_dicts_for_debug=[sub_res_L4, mul_res_L4])
        s.pop()

        # --- L5-SubId: Chained Op: (AS_L - DFI1)_AS / DFI2 ---
        print(f"\n--- Test L5-SubId: (AS_L-DFI1)/DFI2 (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(dfi_L_abc_setup) # La is DFI1, Lb is DFI2
        sub_res_L5 = define_local_op_adaptive_archetype_result(define_raw_sub_from_Unio_Areo_aspect_canonical_result, P_B_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L5SubId_sub")
        div_res_L5 = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, sub_res_L5["val_L_sym"], Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5SubId_div")
        conc_L5SubId = is_local_AS_val(div_res_L5["val_L_sym"], P_B_val_sym) # Expect AS_L / DFI_L -> AS_L
        prove_or_find_counterexample(s, f"L5-SubId (AS_L-DFI1)/DFI2 ~ AS_L (S={current_local_span_S_py})",
                                     sub_res_L5["defining_assertions"] + div_res_L5["defining_assertions"], conc_L5SubId,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym, Lb_val_sym, sub_res_L5["val_L_sym"], div_res_L5["val_L_sym"]],
                                     op_result_dicts_for_debug=[sub_res_L5, div_res_L5])
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC Adaptive Subtraction Interactions Test Complete ======")