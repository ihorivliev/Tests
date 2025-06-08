from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7] 
DEFAULT_P_A_OFFSET = 0 

# --- Phase 1: Foundational Definitions (Canonical AVC - used by adaptive model) ---
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

# --- Phase 2: Canonical Raw Operations (Parameterized by an effective Omega_C) ---
# smart_raw_add and raw_mul are included for completeness if complex cancellation laws are built later
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
                    Ite(q_sym >= current_omega_eff_c_smt, # Apply Omega threshold to quotient
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
                                     result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_div_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

# --- Phase 3: Local Frame, Adaptive Omega, and Mappings (Copied and verified from AVC_Adaptive_Refined_Test.py) ---
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
    is_L_DFI_cond = is_local_DFI_val(Local_val_sym, PA_sym, PB_sym) # True only if S_sym >= 2

    kind_assertions = [
        arch_repr["constraints"], # Basic validity of the canonical structure
        Implies(is_L_ZS_cond, 
                And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))),
        Implies(is_L_AS_cond,
                And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))),
        # If local is DFI (so S_sym must be >= 2), map to canonical Fp.
        # Omega_eff_C_sym will be >= 2 if S_sym >= 2, so canonical DFI exists.
        Implies(is_L_DFI_cond, 
                And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"]))
    ]
    
    val_assertions = [
        Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym)) # Canon AS val is Omega_eff_C_sym
    ]

    # Canonical Fp value mapping:
    # This part assumes arch_repr["is_finite"] is True (i.e., local input was DFI and S_sym >= 2)
    val_if_omega_eff_is_2 = Int(1) # If Omega_eff_C is 2, Canon Fp val is 1.
    val_if_omega_eff_is_3 = Ite(Equals(Local_val_sym, PA_sym + Int(1)), # If Omega_eff_C is 3:
                                 Int(1),                                  # Local P_A+1 -> Canon Fp(1)
                                 Int(2))                                  # Other Local DFIs (e.g. P_A+2 if S=3) -> Canon Fp(2)
                                 
    val_assertions.append(
        Implies(arch_repr["is_finite"], 
            # Omega_eff_C cannot be 1 if arch_repr is finite because is_L_DFI_cond implies S_sym >= 2,
            # and if S_sym >= 2, Omega_eff_C_sym is >= 2.
            Ite(Equals(Omega_eff_C_sym, Int(2)),
                Equals(arch_repr["val"], val_if_omega_eff_is_2),
                # Else Omega_eff_C_sym must be 3 (because arch_repr is_finite means S_sym >=2, so Omega_eff_C is 2 or 3)
                Equals(arch_repr["val"], val_if_omega_eff_is_3) 
            )
        )
    )
    # Ensure canonical Fp value is valid for its archetype (val > 0 and val < Omega_eff_C_sym)
    # This is partly covered by create_intensity_representation (val > 0), 
    # and the specific values (1, 2) assigned are valid for Omega_eff_C=2 or 3.
    val_assertions.append(Implies(arch_repr["is_finite"], 
                            And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))

    return arch_repr, kind_assertions + val_assertions

def map_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode 
) -> FNode:
    # Default mapping for Fp_C if Omega_eff_C_sym is 1 (Arch_Res_Repr should not be Fp_C then)
    val_from_fp_if_omega_eff_is_1 = PB_sym # Fallback to local AS (P_B)
    
    # Mapping for Fp_C if Omega_eff_C_sym is 2 (Arch_Res_Repr.val must be 1)
    # If local span S=1, Fp_C(1) from Omega_eff_C=2 means "one step in a 2-step system".
    # For S=1 (local ZS, local AS only), this "one step" means hitting local AS.
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))

    # Mapping for Fp_C if Omega_eff_C_sym is 3 (Arch_Res_Repr.val is 1 or 2)
    val_from_fp_if_omega_eff_is_3 = \
        Ite(Equals(S_sym, Int(1)), PB_sym, # No local DFI, map any Fp_C to local AS (P_B)
        Ite(Equals(S_sym, Int(2)), # Local DFI is {PA+1}
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), # Canon Fp(1) -> PA+1
                                                     PB_sym),          # Canon Fp(2) from Omega_eff_C=3 maps to Local AS (P_B) if S=2
            # Else S_sym >= 3 (Local DFI has at least PA+1, and PB-1 if S_sym >=2)
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), # Canon Fp(1) -> PA+1
                                                    PB_sym - Int(1))  # Canon Fp(2) -> PB-1 (last DFI step if S>=3)
           ))
                              
    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                    Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         val_from_fp_if_omega_eff_is_3))

    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
               fp_result_val 
           ))

def define_local_op_adaptive_archetype_result(
    op_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    
    S_val_sym = P_B_val_sym - P_A_val_sym
    Omega_eff_C_sym = determine_effective_canonical_omega(S_val_sym)

    X_canon_repr, x_canon_assertions = map_local_to_adaptive_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_xc"
    )
    defining_assertions_for_local_op.extend(x_canon_assertions)

    Y_canon_repr, y_canon_assertions = map_local_to_adaptive_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_yc"
    )
    defining_assertions_for_local_op.extend(y_canon_assertions)

    Res_canon_repr = op_canonical_result_definer( 
        X_canon_repr, Y_canon_repr, 
        f"{result_name_prefix_local}_resc", 
        Omega_eff_C_sym 
    )
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])

    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym
    )
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))

    debug_info = { 
        "X_L_val_dbg": X_L_val_sym, "X_canon_repr_dbg": X_canon_repr, 
        "Y_L_val_dbg": Y_L_val_sym, "Y_canon_repr_dbg": Y_canon_repr,
        "Res_canon_repr_dbg": Res_canon_repr, "Omega_eff_C_sym_dbg": Omega_eff_C_sym,
        "S_val_sym_dbg": S_val_sym, "parent_dict_name_for_debug": result_name_prefix_local 
    }
    return {
        "val_L_sym": Res_L_val_sym, 
        "defining_assertions": defining_assertions_for_local_op,
        "debug_info": debug_info
    }

# --- Phase 4: Generic Property Prover (Copied and enhanced for debug_info) ---
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
                            
                            for repr_key_tuple in [
                                ("X_L_val_dbg", "X_canon_repr_dbg"), 
                                ("Y_L_val_dbg", "Y_canon_repr_dbg"), 
                                (None, "Res_canon_repr_dbg") # For result, only canonical
                            ]:
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
    print("====== AVC Adaptive Division Properties Test ======\n")

    P_A_val_sym = Symbol("PA_val_adiv", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_adiv", solver_INT_TYPE)
    
    La_val_sym = Symbol("La_val_adiv", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val_adiv", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val_adiv", solver_INT_TYPE)

    Li1_val_sym = Symbol("Li1_val_adiv", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val_adiv", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val_adiv", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val_adiv", solver_INT_TYPE)

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S_py} (Adaptive Omega for Division) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) 

        # --- L1-Div: Well-Definedness of raw_div_local_adaptive ---
        print(f"--- Test L1-Div (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))
        premise_L1Div = And(avc_equiv_local_val(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym),
                           avc_equiv_local_val(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        
        op_L1Div_r1 = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1Div_r1")
        op_L1Div_r2 = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1Div_r2")
        conc_L1Div = avc_equiv_local_val(op_L1Div_r1["val_L_sym"], op_L1Div_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1-Div raw_div_local_adaptive respects avc_equiv_local (S={current_local_span_S_py})",
                                     [premise_L1Div] + op_L1Div_r1["defining_assertions"] + op_L1Div_r2["defining_assertions"], conc_L1Div,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L1Div_r1["val_L_sym"],op_L1Div_r2["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L1Div_r1, op_L1Div_r2])
        s.pop()

        # General setup for algebraic laws: La, Lb, Lc are symbolic local values valid in the frame
        general_L_abc_setup = [
            And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym),
            And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym),
            And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym)
        ]

        # --- L2-Div: Commutativity of raw_div_local_adaptive ---
        print(f"\n--- Test L2-Div Commutativity (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(general_L_abc_setup)
        op_ab_L2Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2Div_ab")
        op_ba_L2Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, Lb_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L2Div_ba")
        conc_L2Div = avc_equiv_local_val(op_ab_L2Div["val_L_sym"], op_ba_L2Div["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L2-Div Commutativity (S={current_local_span_S_py})", 
                                     op_ab_L2Div["defining_assertions"] + op_ba_L2Div["defining_assertions"], conc_L2Div,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,op_ab_L2Div["val_L_sym"],op_ba_L2Div["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_ab_L2Div, op_ba_L2Div])
        s.pop()

        # --- L3-Div: Associativity of raw_div_local_adaptive ---
        print(f"\n--- Test L3-Div Associativity (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(general_L_abc_setup)
        div_ab_L3Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3Div_ab")
        lhs_L3Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, div_ab_L3Div["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3Div_lhs")
        div_bc_L3Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3Div_bc")
        rhs_L3Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, div_bc_L3Div["val_L_sym"], P_A_val_sym, P_B_val_sym, "L3Div_rhs")
        all_L3Div_asserts = div_ab_L3Div["defining_assertions"] + lhs_L3Div["defining_assertions"] + div_bc_L3Div["defining_assertions"] + rhs_L3Div["defining_assertions"]
        conc_L3Div = avc_equiv_local_val(lhs_L3Div["val_L_sym"], rhs_L3Div["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L3-Div Associativity (S={current_local_span_S_py})", all_L3Div_asserts, conc_L3Div,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,lhs_L3Div["val_L_sym"],rhs_L3Div["val_L_sym"]],
                                     op_result_dicts_for_debug=[div_ab_L3Div, lhs_L3Div, div_bc_L3Div, rhs_L3Div])
        s.pop()
        
        # --- L4-Div: Cancellation Law 1: (La *_L Lb_DFI) /_L Lb_DFI ~_L La ---
        print(f"\n--- Test L4-Div Cancellation 1 (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)) # La can be anything
        s.add_assertion(is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym))    # Lb must be DFI
        
        prod_ab_L4Div = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4Div_prod_ab")
        res_div_L4Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, prod_ab_L4Div["val_L_sym"], Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4Div_res_div")
        conc_L4Div = avc_equiv_local_val(res_div_L4Div["val_L_sym"], La_val_sym, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L4-Div (La*_L Lb_DFI)/_L Lb_DFI ~_L La (S={current_local_span_S_py})",
                                     prod_ab_L4Div["defining_assertions"] + res_div_L4Div["defining_assertions"], conc_L4Div,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,prod_ab_L4Div["val_L_sym"],res_div_L4Div["val_L_sym"]],
                                     op_result_dicts_for_debug=[prod_ab_L4Div, res_div_L4Div])
        s.pop()

        # --- L5-Div: Cancellation Law 2: (La /_L Lb_DFI) *_L Lb_DFI ~_L La (if La/_L Lb_DFI is DFI_L) ---
        print(f"\n--- Test L5-Div Cancellation 2 (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)) # La can be anything
        s.add_assertion(is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym))    # Lb must be DFI
        
        div_ab_L5Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5Div_div_ab")
        # Add constraint that the intermediate division result is DFI_L
        s.add_assertion(is_local_DFI_val(div_ab_L5Div["val_L_sym"], P_A_val_sym, P_B_val_sym))
        
        res_mul_L5Div = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, div_ab_L5Div["val_L_sym"], Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5Div_res_mul")
        conc_L5Div = avc_equiv_local_val(res_mul_L5Div["val_L_sym"], La_val_sym, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L5-Div (La/_L Lb_DFI)*_L Lb_DFI ~_L La (if Res DFI_L) (S={current_local_span_S_py})",
                                     div_ab_L5Div["defining_assertions"] + res_mul_L5Div["defining_assertions"], conc_L5Div,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,div_ab_L5Div["val_L_sym"],res_mul_L5Div["val_L_sym"]],
                                     op_result_dicts_for_debug=[div_ab_L5Div, res_mul_L5Div])
        s.pop()

        # --- L6-Div: Division by Local Poles ---
        print(f"\n--- Test L6-Div Division by Poles (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)) # La can be anything

        # L6.1: La /_L Local_ZS ~_L Local_AS
        res_div_zs_L6Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, P_A_val_sym, P_A_val_sym, P_B_val_sym, "L6Div_zs")
        conc_L61Div = is_local_AS_val(res_div_zs_L6Div["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L6.1-Div La/_L ZS_L ~_L AS_L (S={current_local_span_S_py})",
                                     res_div_zs_L6Div["defining_assertions"], conc_L61Div,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,res_div_zs_L6Div["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_div_zs_L6Div])
        s.pop()

        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        # L6.2: La /_L Local_AS ~_L Local_AS
        res_div_as_L6Div = define_local_op_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, P_B_val_sym, P_A_val_sym, P_B_val_sym, "L6Div_as")
        conc_L62Div = is_local_AS_val(res_div_as_L6Div["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L6.2-Div La/_L AS_L ~_L AS_L (S={current_local_span_S_py})",
                                     res_div_as_L6Div["defining_assertions"], conc_L62Div,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,res_div_as_L6Div["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_div_as_L6Div])
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC Adaptive Division Properties Test Complete ======")