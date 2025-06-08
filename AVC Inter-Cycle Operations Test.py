from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Spans for the local frames we will define
LOCAL_SPAN_S1_PY = 2 # Expects associative local smart_add via adaptive model
LOCAL_SPAN_S2_PY = 3 # Expects non-associative local smart_add via adaptive model
LOCAL_SPAN_S3_PY = 5 # Expects non-associative local smart_add via adaptive model

# Define PA for local frames (can be different for more complex tests)
P_A1_OFFSET = 0
P_A2_OFFSET = 100 # Offset to ensure distinct local value ranges
P_A3_OFFSET = 200

GLOBAL_CANONICAL_OMEGA_PY = 7 # The Omega for the global operational archetype
GLOBAL_CANONICAL_OMEGA_SMT = Int(GLOBAL_CANONICAL_OMEGA_PY)

# --- Phase 1: Foundational Definitions (Canonical AVC - for the Global Archetype) ---
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
    # Equivalence in the Global Canonical Frame [0, GLOBAL_CANONICAL_OMEGA_SMT]
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"]) 
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"]) 
    finite_finite_equal_val = And(i1_repr["is_finite"], 
                                  i2_repr["is_finite"], 
                                  Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Phase 2: Canonical Raw Operations (for Global Archetype) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    # Standard smart_raw_add logic
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

def define_smart_raw_add_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any], 
                                       result_name_prefix: str) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    # Operations in global archetype always use GLOBAL_CANONICAL_OMEGA_SMT
    res_repr["definition"] = smart_raw_add_logic_builder(i1_global_repr, i2_global_repr, res_repr, GLOBAL_CANONICAL_OMEGA_SMT)
    return res_repr

# (raw_mul_logic_builder and its definer would be similar, using GLOBAL_CANONICAL_OMEGA_SMT)

# --- Phase 3: Local Frame Definitions and Mapping to Global Archetype ---

def is_local_ZS(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

def map_local_to_global_archetype_repr(
    Local_val_sym: FNode, 
    PA_local_sym: FNode, PB_local_sym: FNode, S_local_sym: FNode, # Local frame params
    Omega_global_sym: FNode, # Omega of the target Global Archetype (e.g., 7)
    global_arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    """
    Maps a local value to a state of the GLOBAL canonical archetype [0, Omega_global_sym].
    """
    global_repr = create_intensity_representation(global_arch_name_prefix)
    assertions = [global_repr["constraints"]]

    is_L_ZS = is_local_ZS(Local_val_sym, PA_local_sym)
    is_L_AS = is_local_AS(Local_val_sym, PB_local_sym)
    # is_L_DFI = is_local_DFI(Local_val_sym, PA_local_sym, PB_local_sym) # Implicit if not ZS or AS

    # --- Define Global Kind ---
    assertions.append(
        Ite(is_L_ZS, And(global_repr["is_zero"], Not(global_repr["is_areo"]), Not(global_repr["is_finite"])),
        Ite(is_L_AS, And(Not(global_repr["is_zero"]), global_repr["is_areo"], Not(global_repr["is_finite"])),
                     And(Not(global_repr["is_zero"]), Not(global_repr["is_areo"]), global_repr["is_finite"])))) # Local DFI -> Global Fp
    
    # --- Define Global Value ---
    assertions.append(Implies(global_repr["is_areo"], Equals(global_repr["val"], Omega_global_sym)))

    # Mapping Local DFI to Global DFI [1, Omega_global_sym-1]
    # Strategy: P_A_local+1 maps to Fp_G(1). P_B_local-1 maps to Fp_G(Omega_global-1). Others to Fp_G(2).
    
    is_first_local_dfi = And(S_local_sym > Int(1), Equals(Local_val_sym, PA_local_sym + Int(1)))
    is_last_local_dfi = And(S_local_sym > Int(2), Equals(Local_val_sym, PB_local_sym - Int(1)), Not(is_first_local_dfi))
    
    # Default for other DFIs, ensuring it's at least 2 if Omega_global_sym allows, otherwise 1.
    # This also handles S_local_sym = 2 where first_local_dfi is true, but last_local_dfi is false.
    # If Omega_global_sym is small (e.g. < 3), Fp_G(Omega_global_sym - Int(1)) might be <= Fp_G(1).
    # We need to ensure distinct mapping if possible and valid global DFI values.
    # For Omega_global_sym = 7: Fp_G(1), Fp_G(6), Fp_G(2) are all valid and distinct.
    default_other_dfi_val = Int(2)
    if GLOBAL_CANONICAL_OMEGA_PY < 3: # If global DFI is just {1} or empty
        default_other_dfi_val = Int(1)


    global_dfi_val = Ite(is_first_local_dfi, Int(1),
                       Ite(is_last_local_dfi, Omega_global_sym - Int(1),
                                                default_other_dfi_val)) 

    assertions.append(Implies(global_repr["is_finite"], Equals(global_repr["val"], global_dfi_val)))
    
    # Ensure global Fp value is valid for its archetype [0, Omega_global_sym]
    assertions.append(Implies(global_repr["is_finite"], 
                              And(global_repr["val"] > Int(0), global_repr["val"] < Omega_global_sym)))
    
    return global_repr, assertions

def define_inter_cycle_op_result(
    op_global_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, PA_X_sym: FNode, PB_X_sym: FNode, S_X_sym: FNode, 
    Y_L_val_sym: FNode, PA_Y_sym: FNode, PB_Y_sym: FNode, S_Y_sym: FNode, 
    Omega_global_sym: FNode, 
    result_name_prefix: str
) -> Dict[str, Any]: 
    
    all_inter_cycle_assertions = []

    X_global_repr, x_global_assertions = map_local_to_global_archetype_repr(
        X_L_val_sym, PA_X_sym, PB_X_sym, S_X_sym, Omega_global_sym, f"{result_name_prefix}_xg"
    )
    all_inter_cycle_assertions.extend(x_global_assertions)

    Y_global_repr, y_global_assertions = map_local_to_global_archetype_repr(
        Y_L_val_sym, PA_Y_sym, PB_Y_sym, S_Y_sym, Omega_global_sym, f"{result_name_prefix}_yg"
    )
    all_inter_cycle_assertions.extend(y_global_assertions)

    Res_global_repr = op_global_canonical_result_definer( 
        X_global_repr, Y_global_repr, 
        f"{result_name_prefix}_resg" 
    )
    all_inter_cycle_assertions.append(Res_global_repr["definition"])
    all_inter_cycle_assertions.append(Res_global_repr["constraints"])
    
    debug_info = {
        "X_local_val_dbg": X_L_val_sym, "PA_X_dbg": PA_X_sym, "PB_X_dbg": PB_X_sym, "S_X_dbg": S_X_sym,
        "Y_local_val_dbg": Y_L_val_sym, "PA_Y_dbg": PA_Y_sym, "PB_Y_dbg": PB_Y_sym, "S_Y_dbg": S_Y_sym,
        "X_global_repr_dbg": X_global_repr, "Y_global_repr_dbg": Y_global_repr,
        "Res_global_repr_dbg": Res_global_repr, "Omega_global_sym_dbg": Omega_global_sym,
        "parent_dict_name_for_debug": result_name_prefix
    }

    return {
        "global_repr": Res_global_repr, 
        "defining_assertions": all_inter_cycle_assertions,
        "debug_info": debug_info
    }

# --- Generic Property Prover ---
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
                            op_name_for_print = debug_info.get("parent_dict_name_for_debug", "InterCycleOp")
                            print(f"    Context for Inter-Cycle Op Result '{op_name_for_print}':")
                            
                            for frame_prefix in ["X", "Y"]:
                                pa_sym = debug_info.get(f"PA_{frame_prefix}_dbg")
                                pb_sym = debug_info.get(f"PB_{frame_prefix}_dbg")
                                s_sym = debug_info.get(f"S_{frame_prefix}_dbg")
                                lv_sym = debug_info.get(f"{frame_prefix}_local_val_dbg")
                                g_repr = debug_info.get(f"{frame_prefix}_global_repr_dbg")

                                if lv_sym and pa_sym and pb_sym and s_sym : # Ensure all frame vars are present
                                    print(f"      Local Input {frame_prefix}:")
                                    print(f"        {lv_sym.symbol_name() if isinstance(lv_sym, FNode) else 'LocalVal'}: {solver.get_value(lv_sym) if lv_sym in solver.get_model() else '?'}")
                                    print(f"        {pa_sym.symbol_name() if isinstance(pa_sym, FNode) else 'PA'}: {solver.get_value(pa_sym) if pa_sym in solver.get_model() else '?'}")
                                    print(f"        {pb_sym.symbol_name() if isinstance(pb_sym, FNode) else 'PB'}: {solver.get_value(pb_sym) if pb_sym in solver.get_model() else '?'}")
                                    print(f"        {s_sym.symbol_name() if isinstance(s_sym, FNode) else 'S'}: {solver.get_value(s_sym) if s_sym in solver.get_model() else '?'}")
                                if g_repr and isinstance(g_repr, dict) and "name" in g_repr:
                                    val_str = f"V={solver.get_value(g_repr['val'])}" if g_repr['val'] in solver.get_model() else "V=?"
                                    is_z_str = f"Z={solver.get_value(g_repr['is_zero'])}" if g_repr['is_zero'] in solver.get_model() else "Z=?"
                                    is_a_str = f"A={solver.get_value(g_repr['is_areo'])}" if g_repr['is_areo'] in solver.get_model() else "A=?"
                                    is_f_str = f"F={solver.get_value(g_repr['is_finite'])}" if g_repr['is_finite'] in solver.get_model() else "F=?"
                                    print(f"        Mapped Global {g_repr['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")

                            res_g_repr = debug_info.get("Res_global_repr_dbg")
                            if res_g_repr and isinstance(res_g_repr, dict) and "name" in res_g_repr:
                                val_str = f"V={solver.get_value(res_g_repr['val'])}" if res_g_repr['val'] in solver.get_model() else "V=?"
                                is_z_str = f"Z={solver.get_value(res_g_repr['is_zero'])}" if res_g_repr['is_zero'] in solver.get_model() else "Z=?"
                                is_a_str = f"A={solver.get_value(res_g_repr['is_areo'])}" if res_g_repr['is_areo'] in solver.get_model() else "A=?"
                                is_f_str = f"F={solver.get_value(res_g_repr['is_finite'])}" if res_g_repr['is_finite'] in solver.get_model() else "F=?"
                                print(f"        Global Result {res_g_repr['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print(f"====== AVC Inter-Cycle Operations Test (Global Omega={GLOBAL_CANONICAL_OMEGA_PY}) ======\n")
    s = Solver(name="z3")

    # --- Define Local Frames ---
    PA1_sym = Symbol("PA1", solver_INT_TYPE); PB1_sym = Symbol("PB1", solver_INT_TYPE)
    S1_sym = Symbol("S1", solver_INT_TYPE)
    s.add_assertion(Equals(PA1_sym, Int(P_A1_OFFSET)))
    s.add_assertion(Equals(S1_sym, Int(LOCAL_SPAN_S1_PY)))
    s.add_assertion(S1_sym > Int(0))
    s.add_assertion(Equals(PB1_sym, PA1_sym + S1_sym))

    PA2_sym = Symbol("PA2", solver_INT_TYPE); PB2_sym = Symbol("PB2", solver_INT_TYPE)
    S2_sym = Symbol("S2", solver_INT_TYPE)
    s.add_assertion(Equals(PA2_sym, Int(P_A2_OFFSET)))
    s.add_assertion(Equals(S2_sym, Int(LOCAL_SPAN_S2_PY)))
    s.add_assertion(S2_sym > Int(0))
    s.add_assertion(Equals(PB2_sym, PA2_sym + S2_sym))
    
    PA3_sym = Symbol("PA3", solver_INT_TYPE); PB3_sym = Symbol("PB3", solver_INT_TYPE)
    S3_sym = Symbol("S3", solver_INT_TYPE)
    s.add_assertion(Equals(PA3_sym, Int(P_A3_OFFSET)))
    s.add_assertion(Equals(S3_sym, Int(LOCAL_SPAN_S3_PY)))
    s.add_assertion(S3_sym > Int(0))
    s.add_assertion(Equals(PB3_sym, PA3_sym + S3_sym))

    La_L1_val = Symbol("La_L1", solver_INT_TYPE) 
    Lb_L2_val = Symbol("Lb_L2", solver_INT_TYPE) 
    Lc_L3_val = Symbol("Lc_L3", solver_INT_TYPE) 

    s.add_assertion(And(La_L1_val >= PA1_sym, La_L1_val <= PB1_sym))
    s.add_assertion(And(Lb_L2_val >= PA2_sym, Lb_L2_val <= PB2_sym))
    s.add_assertion(And(Lc_L3_val >= PA3_sym, Lc_L3_val <= PB3_sym))

    print(f"--- Test T0: Sanity of Local-to-Global Mapping ---")
    s.push()
    # Test with La_L1_val being the first DFI of Frame 1, if Frame 1 has a DFI (S1 > 1)
    # If S1 = 1, La_L1_val will be PA1_sym (Local ZS)
    s.add_assertion(Ite(S1_sym > Int(1), 
                        Equals(La_L1_val, PA1_sym + Int(1)), 
                        Equals(La_L1_val, PA1_sym)))

    La_G_repr, la_g_assertions = map_local_to_global_archetype_repr(
        La_L1_val, PA1_sym, PB1_sym, S1_sym, GLOBAL_CANONICAL_OMEGA_SMT, "T0_La_G"
    )
    s.add_assertions(la_g_assertions)
    
    expected_global_val_if_finite = Int(1) 
    
    property_T0 = Ite(S1_sym > Int(1), 
                      And(La_G_repr["is_finite"], Equals(La_G_repr["val"], expected_global_val_if_finite)),
                      La_G_repr["is_zero"]) # If S1=1, La_L1_val=PA1, maps to Global ZS

    prove_or_find_counterexample(s, f"T0 Mapping (La_L1 from S1={LOCAL_SPAN_S1_PY} to Global Omega={GLOBAL_CANONICAL_OMEGA_PY})",
                                 [], property_T0, 
                                 model_vars_to_print=[La_L1_val, PA1_sym, PB1_sym, S1_sym, La_G_repr])
    s.pop()

    print(f"\n--- Test T1: Commutativity of Inter-Cycle Add ---")
    s.push()
    op_XY_dict = define_inter_cycle_op_result(define_smart_raw_add_global_result, 
                                            La_L1_val, PA1_sym, PB1_sym, S1_sym,
                                            Lb_L2_val, PA2_sym, PB2_sym, S2_sym,
                                            GLOBAL_CANONICAL_OMEGA_SMT, "T1_XY")
    op_YX_dict = define_inter_cycle_op_result(define_smart_raw_add_global_result,
                                            Lb_L2_val, PA2_sym, PB2_sym, S2_sym, 
                                            La_L1_val, PA1_sym, PB1_sym, S1_sym,
                                            GLOBAL_CANONICAL_OMEGA_SMT, "T1_YX")
    
    all_T1_assertions = op_XY_dict["defining_assertions"] + op_YX_dict["defining_assertions"]
    prop_T1 = avc_equiv_canonical(op_XY_dict["global_repr"], op_YX_dict["global_repr"])
    
    prove_or_find_counterexample(s, f"T1 Commutativity Inter-Cycle Add (S1={LOCAL_SPAN_S1_PY}, S2={LOCAL_SPAN_S2_PY})",
                                 all_T1_assertions, prop_T1,
                                 model_vars_to_print=[La_L1_val, Lb_L2_val, op_XY_dict["global_repr"], op_YX_dict["global_repr"]],
                                 op_result_dicts_for_debug=[op_XY_dict, op_YX_dict])
    s.pop()

    print(f"\n--- Test T2: Associativity of Inter-Cycle Add ---")
    s.push()
    La_G, la_g_asserts = map_local_to_global_archetype_repr(La_L1_val, PA1_sym, PB1_sym, S1_sym, GLOBAL_CANONICAL_OMEGA_SMT, "T2_LaG")
    Lb_G, lb_g_asserts = map_local_to_global_archetype_repr(Lb_L2_val, PA2_sym, PB2_sym, S2_sym, GLOBAL_CANONICAL_OMEGA_SMT, "T2_LbG")
    Lc_G, lc_g_asserts = map_local_to_global_archetype_repr(Lc_L3_val, PA3_sym, PB3_sym, S3_sym, GLOBAL_CANONICAL_OMEGA_SMT, "T2_LcG")
    all_mapping_asserts_T2 = la_g_asserts + lb_g_asserts + lc_g_asserts
    # Add the constraints from create_intensity_representation for La_G, Lb_G, Lc_G as they are now direct inputs to global ops
    all_mapping_asserts_T2.extend([La_G["constraints"], Lb_G["constraints"], Lc_G["constraints"]])


    sum_ab_G = define_smart_raw_add_global_result(La_G, Lb_G, "T2_sum_abG")
    lhs_G = define_smart_raw_add_global_result(sum_ab_G, Lc_G, "T2_lhsG")
    sum_bc_G = define_smart_raw_add_global_result(Lb_G, Lc_G, "T2_sum_bcG")
    rhs_G = define_smart_raw_add_global_result(La_G, sum_bc_G, "T2_rhsG")
    
    all_T2_op_asserts = [
        sum_ab_G["definition"], sum_ab_G["constraints"],
        lhs_G["definition"], lhs_G["constraints"],
        sum_bc_G["definition"], sum_bc_G["constraints"],
        rhs_G["definition"], rhs_G["constraints"]
    ]
    prop_T2_simplified = avc_equiv_canonical(lhs_G, rhs_G)
    
    prove_or_find_counterexample(s, f"T2 Assoc. Inter-Cycle Add (S1={LOCAL_SPAN_S1_PY},S2={LOCAL_SPAN_S2_PY},S3={LOCAL_SPAN_S3_PY} -> Global Omega={GLOBAL_CANONICAL_OMEGA_PY})",
                                 all_mapping_asserts_T2 + all_T2_op_asserts, prop_T2_simplified,
                                 model_vars_to_print=[La_L1_val,Lb_L2_val,Lc_L3_val, La_G, Lb_G, Lc_G, sum_ab_G, lhs_G, sum_bc_G, rhs_G],
                                 print_model_on_fail=True)
    s.pop()

    print(f"\n--- Test T3: Interaction of Local Unios in Global Context ---")
    s.push()
    # Case 1: La_L1 is PA1 (Local ZS1 from Frame 1)
    s.add_assertion(Equals(La_L1_val, PA1_sym)) 
    
    op_PA1_Lb_dict = define_inter_cycle_op_result(define_smart_raw_add_global_result,
                                                La_L1_val, PA1_sym, PB1_sym, S1_sym,
                                                Lb_L2_val, PA2_sym, PB2_sym, S2_sym,
                                                GLOBAL_CANONICAL_OMEGA_SMT, "T3_PA1_Lb")
    # Get the global representation of Lb_L2_val for comparison
    Lb_L2_mapped_to_G, lb_l2_g_asserts = map_local_to_global_archetype_repr(
        Lb_L2_val, PA2_sym, PB2_sym, S2_sym, GLOBAL_CANONICAL_OMEGA_SMT, "T3_Lb_L2_G"
    )
    all_T3_1_asserts = op_PA1_Lb_dict["defining_assertions"] + lb_l2_g_asserts + [Lb_L2_mapped_to_G["constraints"]]
    prop_T3_1 = avc_equiv_canonical(op_PA1_Lb_dict["global_repr"], Lb_L2_mapped_to_G) # Expect ZS_G + X_G ~ X_G
    
    prove_or_find_counterexample(s, f"T3.1 add_inter(Local_ZS1, Local_Y) ~ Global_Y (S1={LOCAL_SPAN_S1_PY}, S2={LOCAL_SPAN_S2_PY})",
                                 all_T3_1_asserts, prop_T3_1,
                                 model_vars_to_print=[La_L1_val, Lb_L2_val, op_PA1_Lb_dict["global_repr"], Lb_L2_mapped_to_G],
                                 op_result_dicts_for_debug=[op_PA1_Lb_dict])
    s.pop()
    
    s.push()
    # Case 2: La_L1 is PB1 (Local AS1 from Frame 1)
    s.add_assertion(Equals(La_L1_val, PB1_sym))

    op_PB1_Lb_dict = define_inter_cycle_op_result(define_smart_raw_add_global_result,
                                                La_L1_val, PA1_sym, PB1_sym, S1_sym,
                                                Lb_L2_val, PA2_sym, PB2_sym, S2_sym,
                                                GLOBAL_CANONICAL_OMEGA_SMT, "T3_PB1_Lb")
    Lb_L2_mapped_to_G_case2, lb_l2_g_asserts_case2 = map_local_to_global_archetype_repr( 
        Lb_L2_val, PA2_sym, PB2_sym, S2_sym, GLOBAL_CANONICAL_OMEGA_SMT, "T3_Lb_L2_G_c2"
    )
    all_T3_2_asserts = op_PB1_Lb_dict["defining_assertions"] + lb_l2_g_asserts_case2 + [Lb_L2_mapped_to_G_case2["constraints"]]
    prop_T3_2 = avc_equiv_canonical(op_PB1_Lb_dict["global_repr"], Lb_L2_mapped_to_G_case2) # Expect AS_G + X_G ~ X_G (due to smart_raw_add)
    
    prove_or_find_counterexample(s, f"T3.2 add_inter(Local_AS1, Local_Y) ~ Global_Y (S1={LOCAL_SPAN_S1_PY}, S2={LOCAL_SPAN_S2_PY})",
                                 all_T3_2_asserts, prop_T3_2,
                                 model_vars_to_print=[La_L1_val, Lb_L2_val, op_PB1_Lb_dict["global_repr"], Lb_L2_mapped_to_G_case2],
                                 op_result_dicts_for_debug=[op_PB1_Lb_dict])
    s.pop()
        
    del s 
    print("-" * 80)

    print(f"\n====== AVC Inter-Cycle Operations Test (Global Omega={GLOBAL_CANONICAL_OMEGA_PY}) Complete ======")

