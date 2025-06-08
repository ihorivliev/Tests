from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Omega values for the Global Canonical Archetype (GCA) to be tested
GLOBAL_CANONICAL_OMEGA_PY_VARIANTS = [2, 3, 7]

# Define fixed local frames for testing inter-cycle operations
# Frame A: P_A_A to P_B_A with Span S_A
P_A1_OFFSET_PY = 0
LOCAL_SPAN_S1_PY = 2 # Local add would be associative if S1 was Omega_C

# Frame B: P_A_B to P_B_B with Span S_B
P_A2_OFFSET_PY = 100 # Offset to ensure distinct local value ranges
LOCAL_SPAN_S2_PY = 3 # Local add would be non-associative if S2 was Omega_C

# Frame C: P_A_C to P_B_C with Span S_C
P_A3_OFFSET_PY = 200
LOCAL_SPAN_S3_PY = 5 # Local add would be non-associative if S3 was Omega_C


# --- Phase 1: Foundational Definitions (Canonical AVC - for the Global Archetype) ---
def create_intensity_representation(name_prefix: str) -> Dict[str, Any]:
    """
    Creates PySMT symbols for a Canonical Intensity and its critical validity constraints.
    An Intensity is abstractly one of: ZeroState, AreoState, or Finite(PosNat).
    """
    is_zero = Symbol(f"{name_prefix}_is_zero", solver_BOOL_TYPE)
    is_areo = Symbol(f"{name_prefix}_is_areo", solver_BOOL_TYPE)
    is_finite = Symbol(f"{name_prefix}_is_finite", solver_BOOL_TYPE)
    val = Symbol(f"{name_prefix}_val", solver_INT_TYPE) # Value if finite

    constraint_exactly_one_state = ExactlyOne(is_zero, is_areo, is_finite)
    # Constraint: If Finite, its value must be a Positive Natural (val > 0)
    # The upper bound (val < Omega_canonical) is context-dependent and applied by mapping or ops.
    constraint_pos_nat_if_finite = Implies(is_finite, val > Int(0))
    
    all_constraints = And(constraint_exactly_one_state, constraint_pos_nat_if_finite)
    
    return {
        "is_zero": is_zero, "is_areo": is_areo, "is_finite": is_finite,
        "val": val, "constraints": all_constraints, "name": name_prefix
    }

def avc_equiv_canonical(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any]) -> FNode:
    """
    Defines the avc_equiv relation between two canonical intensity representations.
    ZS_C ~ AS_C (Unio identification in the canonical frame).
    """
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"]) # Unio identification
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"]) # Unio identification
    finite_finite_equal_val = And(i1_repr["is_finite"], 
                                  i2_repr["is_finite"], 
                                  Equals(i1_repr["val"], i2_repr["val"]))
    
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Phase 2: Canonical Raw Operations (for Global Archetype, Parameterized by Global Omega) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    # Standard smart_raw_add logic (AS_C + Fp_C -> Fp_C)
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), # ZS_C + ZS_C -> ZS_C
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # ZS_C + AS_C -> AS_C
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) # ZS_C + Fp_C -> Fp_C
    )))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  # AS_C + ZS_C -> AS_C
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  # AS_C + AS_C -> AS_C
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) # AS_C + Fp_C -> Fp_C
    )))
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) # Fp_C + ZS_C -> Fp_C
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) # Fp_C + AS_C -> Fp_C
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
                            Ite(val_sum >= current_omega_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # result is AS_C
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) # result is Fp_C(sum)
                            )))
    return And(formulas)

def define_smart_raw_add_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any], 
                                       result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    # Standard raw_mul logic
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

def define_raw_mul_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any], 
                                 result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
    return res_repr

# --- Phase 3: Local Frame Definitions and Mapping to Global Archetype ---
def is_local_ZS(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    # True if P_A < val_L < P_B. This implies span P_B - P_A > 1.
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

def map_local_to_global_archetype_repr(
    Local_val_sym: FNode, 
    PA_local_sym: FNode, PB_local_sym: FNode, S_local_sym: FNode, # Local frame params
    Omega_global_sym: FNode, # Omega of the target Global Archetype
    global_arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    """
    Maps a local value to a state of the GLOBAL canonical archetype [0, Omega_global_sym].
    """
    global_repr = create_intensity_representation(global_arch_name_prefix)
    assertions = [global_repr["constraints"]]

    is_L_ZS = is_local_ZS(Local_val_sym, PA_local_sym)
    is_L_AS = is_local_AS(Local_val_sym, PB_local_sym)
    # is_L_DFI is implicitly Not(is_L_ZS) and Not(is_L_AS) for a valid local value

    # --- Define Global Kind ---
    assertions.append(
        Ite(is_L_ZS, And(global_repr["is_zero"], Not(global_repr["is_areo"]), Not(global_repr["is_finite"])),
        Ite(is_L_AS, And(Not(global_repr["is_zero"]), global_repr["is_areo"], Not(global_repr["is_finite"])),
                     And(Not(global_repr["is_zero"]), Not(global_repr["is_areo"]), global_repr["is_finite"])))) # Local DFI -> Global Fp
    
    # --- Define Global Value ---
    # For Global AS, its canonical value is Omega_global_sym
    assertions.append(Implies(global_repr["is_areo"], Equals(global_repr["val"], Omega_global_sym)))

    # Mapping Local DFI to Global DFI [1, Omega_global_sym-1]
    # Strategy:
    # - Local P_A+1 (if it exists, i.e., S_local_sym > 1) maps to Global Fp_G(1).
    # - Local P_B-1 (if it exists and is distinct from P_A+1, i.e., S_local_sym > 2) maps to Global Fp_G(Omega_global_sym-1).
    # - All other Local DFIs map to a default Global Fp_G value (e.g., Fp_G(2), if Omega_global_sym allows).
    
    # Check if Omega_global_sym can support Fp_G(1), Fp_G(2), Fp_G(Omega_global_sym-1) as distinct
    # Need Omega_global_sym >= 3 for Fp_G(1) and Fp_G(2) to be distinct and valid DFIs.
    # Need Omega_global_sym >= 2 for Fp_G(1) to exist.
    # Need Omega_global_sym >= 2 for Fp_G(Omega_global_sym-1) to exist (as Fp_G(1) if Omega_global_sym=2).

    # Default mapped value for "other" DFIs
    # If Omega_global_sym = 2, other DFIs (if any beyond P_A+1) can't really map uniquely. This mapping simplifies.
    # If Omega_global_sym >=3, map to Fp_G(2).
    default_other_dfi_val_G = Ite(Omega_global_sym < Int(3), Int(1), Int(2))

    # Conditions for local DFI structure
    is_first_local_dfi = And(S_local_sym > Int(1), Equals(Local_val_sym, PA_local_sym + Int(1)))
    is_last_local_dfi  = And(S_local_sym > Int(2), Equals(Local_val_sym, PB_local_sym - Int(1))) # S_local > 2 implies distinct from P_A+1

    # Guard against mapping to Fp_G(Omega_global_sym-1) if Omega_global_sym-1 <= 1 (i.e. Omega_global_sym <=2)
    # If Omega_global_sym is 2, Omega_global_sym-1 is 1.
    # If Omega_global_sym is <2 (i.e. 1), Omega_global_sym-1 is 0 (invalid DFI).
    # The DFI mapping for last_local_dfi should only apply if Omega_global_sym-1 > 1 (i.e. Omega_global_sym > 2)
    # and it's distinct from first_local_dfi mapping.
    
    global_dfi_val = Ite(is_first_local_dfi, 
                         Int(1), # First local DFI maps to Global Fp_G(1)
                         Ite(And(is_last_local_dfi, Omega_global_sym > Int(2)), # Only map to last global DFI if distinct from global Fp_G(1)
                             Omega_global_sym - Int(1), # Last local DFI maps to Global Fp_G(Omega_global-1)
                             default_other_dfi_val_G # All other local DFIs map to default
                            )
                        )
    
    assertions.append(Implies(global_repr["is_finite"], Equals(global_repr["val"], global_dfi_val)))
    
    # Ensure global Fp value is valid for its archetype [0, Omega_global_sym]
    # (val > 0 is from create_intensity_representation, val < Omega_global_sym needs to be asserted for mapped Fp)
    assertions.append(Implies(global_repr["is_finite"], 
                              And(global_repr["val"] > Int(0), global_repr["val"] < Omega_global_sym)))
    
    return global_repr, assertions

# --- Phase 4: Inter-Cycle Operation Definition ---
def define_inter_cycle_op_result(
    op_global_canonical_result_definer: Callable, # e.g., define_smart_raw_add_global_result
    # Frame X parameters
    X_L_val_sym: FNode, PA_X_sym: FNode, PB_X_sym: FNode, S_X_sym: FNode, 
    # Frame Y parameters
    Y_L_val_sym: FNode, PA_Y_sym: FNode, PB_Y_sym: FNode, S_Y_sym: FNode, 
    Omega_global_sym: FNode, # Omega of the Global Archetype
    result_name_prefix: str
) -> Dict[str, Any]: 
    """
    Defines an operation between entities from two different local frames (X from Frame A, Y from Frame B).
    The operation is performed in the Global Canonical Archetype.
    Returns a dictionary containing the Global Canonical Intensity representation of the result 
    and all SMT assertions defining this process.
    """
    all_inter_cycle_assertions = []

    # 1. Map X_L_val_sym (from its local frame [PA_X, PB_X]) to Global Representation X_G
    X_global_repr, x_global_assertions = map_local_to_global_archetype_repr(
        X_L_val_sym, PA_X_sym, PB_X_sym, S_X_sym, Omega_global_sym, f"{result_name_prefix}_xg"
    )
    all_inter_cycle_assertions.extend(x_global_assertions)

    # 2. Map Y_L_val_sym (from its local frame [PA_Y, PB_Y]) to Global Representation Y_G
    Y_global_repr, y_global_assertions = map_local_to_global_archetype_repr(
        Y_L_val_sym, PA_Y_sym, PB_Y_sym, S_Y_sym, Omega_global_sym, f"{result_name_prefix}_yg"
    )
    all_inter_cycle_assertions.extend(y_global_assertions)

    # 3. Perform operation in the Global Canonical Archetype
    #    The op_global_canonical_result_definer (e.g. define_smart_raw_add_global_result)
    #    will use Omega_global_sym internally.
    Res_global_repr = op_global_canonical_result_definer( 
        X_global_repr, Y_global_repr, 
        f"{result_name_prefix}_resg",
        Omega_global_sym # Ensure this is passed if definer needs it, or definer uses a global
    )
    all_inter_cycle_assertions.append(Res_global_repr["definition"])
    all_inter_cycle_assertions.append(Res_global_repr["constraints"]) # Constraints of the result representation
    
    # Debug information to help trace mappings if a test fails
    debug_info = {
        "X_local_val_dbg": X_L_val_sym, "PA_X_dbg": PA_X_sym, "PB_X_dbg": PB_X_sym, "S_X_dbg": S_X_sym,
        "Y_local_val_dbg": Y_L_val_sym, "PA_Y_dbg": PA_Y_sym, "PB_Y_dbg": PB_Y_sym, "S_Y_dbg": S_Y_sym,
        "X_global_repr_dbg": X_global_repr, 
        "Y_global_repr_dbg": Y_global_repr,
        "Res_global_repr_dbg": Res_global_repr, 
        "Omega_global_sym_dbg": Omega_global_sym,
        "parent_dict_name_for_debug": result_name_prefix
    }

    return {
        "global_repr": Res_global_repr, # The result is a Global Canonical Intensity
        "defining_assertions": all_inter_cycle_assertions,
        "debug_info": debug_info
    }

# --- Phase 5: Generic Property Prover (Enhanced for Debugging Mappings) ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True, 
                                 op_result_dicts_for_debug: List[Dict[str,Any]] = []): # List of op_result_dicts
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions: solver.add_assertion(assertion)
    
    # Assert the negation of the property we want to prove true
    solver.add_assertion(Not(property_to_prove_true))
        
    proved_universally = False
    if not solver.solve(): # If "NOT property_to_prove_true" is UNSAT
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved_universally = True
    else: # If "NOT property_to_prove_true" is SAT, then "property_to_prove_true" does NOT hold universally
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_fail:
            printed_debug_info_ids = set() # To avoid printing the same debug_info multiple times if shared
            for var_item in model_vars_to_print:
                if isinstance(var_item, dict) and "name" in var_item : # It's an Intensity representation
                    val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                    is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                    is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode): # It's a raw SMT symbol (like P_A_val_sym or a local result value)
                     print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
                # else:
                #     print(f"  Unknown model var type: {var_item}")
            
            if op_result_dicts_for_debug:
                print("  DEBUG Global Representations & Results in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "debug_info" in op_res_dict:
                        debug_info = op_res_dict["debug_info"]
                        if isinstance(debug_info, dict) and id(debug_info) not in printed_debug_info_ids:
                            printed_debug_info_ids.add(id(debug_info)) 
                            op_name_for_print = debug_info.get("parent_dict_name_for_debug", "InterCycleOp")
                            print(f"    Context for Operation Result '{op_name_for_print}':")
                            
                            omega_g_sym = debug_info.get('Omega_global_sym_dbg')
                            omega_g_str = f"{solver.get_value(omega_g_sym)}" if omega_g_sym and omega_g_sym in solver.get_model() else "?"
                            print(f"      Global Archetype Omega_G = {omega_g_str}")

                            for frame_prefix_dbg in ["X", "Y"]: # For X_from_A, Y_from_B style inputs
                                pa_sym_dbg = debug_info.get(f"PA_{frame_prefix_dbg}_dbg")
                                pb_sym_dbg = debug_info.get(f"PB_{frame_prefix_dbg}_dbg")
                                s_sym_dbg = debug_info.get(f"S_{frame_prefix_dbg}_dbg")
                                lv_sym_dbg = debug_info.get(f"{frame_prefix_dbg}_local_val_dbg")
                                g_repr_dbg = debug_info.get(f"{frame_prefix_dbg}_global_repr_dbg")

                                if lv_sym_dbg and pa_sym_dbg and pb_sym_dbg and s_sym_dbg and g_repr_dbg :
                                    print(f"      Input {frame_prefix_dbg}:")
                                    lv_name = lv_sym_dbg.symbol_name() if isinstance(lv_sym_dbg, FNode) else 'LocalVal'
                                    pa_name = pa_sym_dbg.symbol_name() if isinstance(pa_sym_dbg, FNode) else 'PA'
                                    pb_name = pb_sym_dbg.symbol_name() if isinstance(pb_sym_dbg, FNode) else 'PB'
                                    s_name = s_sym_dbg.symbol_name() if isinstance(s_sym_dbg, FNode) else 'S'
                                    
                                    print(f"        Local {lv_name}: {solver.get_value(lv_sym_dbg) if lv_sym_dbg in solver.get_model() else '?'}")
                                    print(f"        Frame {pa_name}: {solver.get_value(pa_sym_dbg) if pa_sym_dbg in solver.get_model() else '?'} to {pb_name}: {solver.get_value(pb_sym_dbg) if pb_sym_dbg in solver.get_model() else '?'} (Span {s_name}: {solver.get_value(s_sym_dbg) if s_sym_dbg in solver.get_model() else '?'})")
                                    
                                    val_str_g = f"V={solver.get_value(g_repr_dbg['val'])}" if g_repr_dbg['val'] in solver.get_model() else "V=?"
                                    is_z_str_g = f"Z={solver.get_value(g_repr_dbg['is_zero'])}" if g_repr_dbg['is_zero'] in solver.get_model() else "Z=?"
                                    is_a_str_g = f"A={solver.get_value(g_repr_dbg['is_areo'])}" if g_repr_dbg['is_areo'] in solver.get_model() else "A=?"
                                    is_f_str_g = f"F={solver.get_value(g_repr_dbg['is_finite'])}" if g_repr_dbg['is_finite'] in solver.get_model() else "F=?"
                                    print(f"        Mapped Global {g_repr_dbg['name']}: {is_z_str_g}, {is_a_str_g}, {is_f_str_g}, {val_str_g}")

                            res_g_repr_dbg = debug_info.get("Res_global_repr_dbg")
                            if res_g_repr_dbg and isinstance(res_g_repr_dbg, dict) and "name" in res_g_repr_dbg:
                                val_str_resg = f"V={solver.get_value(res_g_repr_dbg['val'])}" if res_g_repr_dbg['val'] in solver.get_model() else "V=?"
                                is_z_str_resg = f"Z={solver.get_value(res_g_repr_dbg['is_zero'])}" if res_g_repr_dbg['is_zero'] in solver.get_model() else "Z=?"
                                is_a_str_resg = f"A={solver.get_value(res_g_repr_dbg['is_areo'])}" if res_g_repr_dbg['is_areo'] in solver.get_model() else "A=?"
                                is_f_str_resg = f"F={solver.get_value(res_g_repr_dbg['is_finite'])}" if res_g_repr_dbg['is_finite'] in solver.get_model() else "F=?"
                                print(f"      Global Result {res_g_repr_dbg['name']}: {is_z_str_resg}, {is_a_str_resg}, {is_f_str_resg}, {val_str_resg}")
            
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 6: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Inter-Cycle Global Archetype Impact Test ======\n")
    
    # Define Local Frame Parameters (as Python values for loop, will be Int() in solver)
    frame_A_params = {"pa_offset": P_A1_OFFSET_PY, "span": LOCAL_SPAN_S1_PY, "name": "FrameA"} # S=2
    frame_B_params = {"pa_offset": P_A2_OFFSET_PY, "span": LOCAL_SPAN_S2_PY, "name": "FrameB"} # S=3
    frame_C_params = {"pa_offset": P_A3_OFFSET_PY, "span": LOCAL_SPAN_S3_PY, "name": "FrameC"} # S=5

    for global_omega_py in GLOBAL_CANONICAL_OMEGA_PY_VARIANTS:
        s = Solver(name="z3")
        current_global_omega_smt = Int(global_omega_py)
        print(f"\n\n===== TESTING INTER-CYCLE OPS WITH GLOBAL OMEGA = {global_omega_py} =====\n")

        # --- Symbolic representations for local values and their frame parameters ---
        # For X_A from Frame A
        XA_L_val = Symbol("XA_L", solver_INT_TYPE)
        PA_X_sym = Symbol("PA_X", solver_INT_TYPE); PB_X_sym = Symbol("PB_X", solver_INT_TYPE); S_X_sym = Symbol("S_X", solver_INT_TYPE)
        s.add_assertion(Equals(PA_X_sym, Int(frame_A_params["pa_offset"])))
        s.add_assertion(Equals(S_X_sym, Int(frame_A_params["span"])))
        s.add_assertion(S_X_sym > Int(0))
        s.add_assertion(Equals(PB_X_sym, PA_X_sym + S_X_sym))
        s.add_assertion(And(XA_L_val >= PA_X_sym, XA_L_val <= PB_X_sym)) # Ensure XA_L is a valid value in its frame

        # For Y_B from Frame B
        YB_L_val = Symbol("YB_L", solver_INT_TYPE)
        PA_Y_sym = Symbol("PA_Y", solver_INT_TYPE); PB_Y_sym = Symbol("PB_Y", solver_INT_TYPE); S_Y_sym = Symbol("S_Y", solver_INT_TYPE)
        s.add_assertion(Equals(PA_Y_sym, Int(frame_B_params["pa_offset"])))
        s.add_assertion(Equals(S_Y_sym, Int(frame_B_params["span"])))
        s.add_assertion(S_Y_sym > Int(0))
        s.add_assertion(Equals(PB_Y_sym, PA_Y_sym + S_Y_sym))
        s.add_assertion(And(YB_L_val >= PA_Y_sym, YB_L_val <= PB_Y_sym))

        # For Z_C from Frame C
        ZC_L_val = Symbol("ZC_L", solver_INT_TYPE)
        PA_Z_sym = Symbol("PA_Z", solver_INT_TYPE); PB_Z_sym = Symbol("PB_Z", solver_INT_TYPE); S_Z_sym = Symbol("S_Z", solver_INT_TYPE)
        s.add_assertion(Equals(PA_Z_sym, Int(frame_C_params["pa_offset"])))
        s.add_assertion(Equals(S_Z_sym, Int(frame_C_params["span"])))
        s.add_assertion(S_Z_sym > Int(0))
        s.add_assertion(Equals(PB_Z_sym, PA_Z_sym + S_Z_sym))
        s.add_assertion(And(ZC_L_val >= PA_Z_sym, ZC_L_val <= PB_Z_sym))

        # --- Test IC-1: Associativity of Inter-Cycle Addition ---
        # ( (X_A +_inter Y_B) +_inter Z_C )  vs  ( X_A +_inter (Y_B +_inter Z_C) )
        # All additions are inter-cycle, results are Global Canonical an
        print(f"--- Test IC-1: Associativity of Inter-Cycle Add (Global Omega={global_omega_py}) ---")
        
        # LHS: (X_A +_inter Y_B)
        op_XA_YB_dict = define_inter_cycle_op_result(
            define_smart_raw_add_global_result,
            XA_L_val, PA_X_sym, PB_X_sym, S_X_sym,
            YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
            current_global_omega_smt, f"IC1_sum_XA_YB_G{global_omega_py}"
        )
        # LHS_final: (result of XA+YB) +_inter Z_C
        # For this, the first operand is already a Global Canonical Intensity.
        # We need a way to use a Global Canonical Intensity as a direct input to an inter-cycle op,
        # or adapt define_inter_cycle_op_result, or define a simpler global op.
        # Let's define a global op directly for this step.
        
        # Map Z_C to Global
        ZC_global_repr, zc_global_assertions = map_local_to_global_archetype_repr(
            ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym, current_global_omega_smt, f"IC1_ZC_G{global_omega_py}"
        )
        
        LHS_final_global_repr = define_smart_raw_add_global_result(
            op_XA_YB_dict["global_repr"], ZC_global_repr, 
            f"IC1_LHS_final_G{global_omega_py}", current_global_omega_smt
        )

        # RHS: (Y_B +_inter Z_C)
        op_YB_ZC_dict = define_inter_cycle_op_result(
            define_smart_raw_add_global_result,
            YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
            ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym,
            current_global_omega_smt, f"IC1_sum_YB_ZC_G{global_omega_py}"
        )
        # RHS_final: X_A +_inter (result of YB+ZC)
        # Map X_A to Global
        XA_global_repr, xa_global_assertions = map_local_to_global_archetype_repr(
            XA_L_val, PA_X_sym, PB_X_sym, S_X_sym, current_global_omega_smt, f"IC1_XA_G{global_omega_py}"
        )

        RHS_final_global_repr = define_smart_raw_add_global_result(
            XA_global_repr, op_YB_ZC_dict["global_repr"],
            f"IC1_RHS_final_G{global_omega_py}", current_global_omega_smt
        )

        all_IC1_assertions = op_XA_YB_dict["defining_assertions"] + \
                             zc_global_assertions + [ZC_global_repr["constraints"]] + \
                             [LHS_final_global_repr["definition"], LHS_final_global_repr["constraints"]] + \
                             op_YB_ZC_dict["defining_assertions"] + \
                             xa_global_assertions + [XA_global_repr["constraints"]] + \
                             [RHS_final_global_repr["definition"], RHS_final_global_repr["constraints"]]
        
        property_IC1 = avc_equiv_canonical(LHS_final_global_repr, RHS_final_global_repr)
        
        # Variables to print for counterexample
        model_vars_IC1 = [
            XA_L_val, PA_X_sym, PB_X_sym, S_X_sym, 
            YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
            ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym,
            # Global representations of inputs
            op_XA_YB_dict["debug_info"]["X_global_repr_dbg"], op_XA_YB_dict["debug_info"]["Y_global_repr_dbg"], # XA_G, YB_G for sum1
            ZC_global_repr, # ZC_G
            XA_global_repr, # XA_G for sum2
            op_YB_ZC_dict["debug_info"]["X_global_repr_dbg"], op_YB_ZC_dict["debug_info"]["Y_global_repr_dbg"], # YB_G, ZC_G for sum3
            # Intermediate and final results (which are global intensities)
            op_XA_YB_dict["global_repr"], LHS_final_global_repr,
            op_YB_ZC_dict["global_repr"], RHS_final_global_repr
        ]
        debug_ops_IC1 = [op_XA_YB_dict, op_YB_ZC_dict] # Pass the dicts containing debug_info

        prove_or_find_counterexample(s, f"IC-1 Assoc. Inter-Cycle Add (Global Omega={global_omega_py})",
                                     all_IC1_assertions, property_IC1,
                                     model_vars_to_print=model_vars_IC1,
                                     op_result_dicts_for_debug=debug_ops_IC1)

        # --- Test IC-2: Distributivity of Inter-Cycle Operations ---
        # X_A *_inter (Y_B +_inter Z_C)   vs   (X_A *_inter Y_B) +_inter (X_A *_inter Z_C)
        print(f"--- Test IC-2: Distributivity of Inter-Cycle Ops (Global Omega={global_omega_py}) ---")
        
        # LHS: Y_B +_inter Z_C
        sum_YB_ZC_inter_dict = define_inter_cycle_op_result(
            define_smart_raw_add_global_result,
            YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
            ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym,
            current_global_omega_smt, f"IC2_sum_YBZC_G{global_omega_py}"
        )
        # LHS_final: X_A *_inter (result of YB+ZC)
        # Map X_A to Global (already done as XA_global_repr for IC-1, reuse if same scope or redefine)
        # Re-defining for clarity within this test block although XA_global_repr is available from IC-1
        XA_global_repr_ic2, xa_global_assertions_ic2 = map_local_to_global_archetype_repr(
            XA_L_val, PA_X_sym, PB_X_sym, S_X_sym, current_global_omega_smt, f"IC2_XA_G{global_omega_py}"
        )
        
        LHS_dist_final_global_repr = define_raw_mul_global_result(
            XA_global_repr_ic2, sum_YB_ZC_inter_dict["global_repr"],
            f"IC2_LHS_final_G{global_omega_py}", current_global_omega_smt
        )

        # RHS: (X_A *_inter Y_B)
        prod_XA_YB_inter_dict = define_inter_cycle_op_result(
            define_raw_mul_global_result, # Using raw_mul for the product part
            XA_L_val, PA_X_sym, PB_X_sym, S_X_sym,
            YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
            current_global_omega_smt, f"IC2_prod_XAYB_G{global_omega_py}"
        )
        # RHS: (X_A *_inter Z_C)
        prod_XA_ZC_inter_dict = define_inter_cycle_op_result(
            define_raw_mul_global_result, # Using raw_mul for the product part
            XA_L_val, PA_X_sym, PB_X_sym, S_X_sym,
            ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym,
            current_global_omega_smt, f"IC2_prod_XAZC_G{global_omega_py}"
        )
        # RHS_final: (result of XA*YB) +_inter (result of XA*ZC)
        RHS_dist_final_global_repr = define_smart_raw_add_global_result(
            prod_XA_YB_inter_dict["global_repr"], prod_XA_ZC_inter_dict["global_repr"],
            f"IC2_RHS_final_G{global_omega_py}", current_global_omega_smt
        )

        all_IC2_assertions = sum_YB_ZC_inter_dict["defining_assertions"] + \
                             xa_global_assertions_ic2 + [XA_global_repr_ic2["constraints"]] + \
                             [LHS_dist_final_global_repr["definition"], LHS_dist_final_global_repr["constraints"]] + \
                             prod_XA_YB_inter_dict["defining_assertions"] + \
                             prod_XA_ZC_inter_dict["defining_assertions"] + \
                             [RHS_dist_final_global_repr["definition"], RHS_dist_final_global_repr["constraints"]]

        property_IC2 = avc_equiv_canonical(LHS_dist_final_global_repr, RHS_dist_final_global_repr)

        model_vars_IC2 = [
            XA_L_val, PA_X_sym, PB_X_sym, S_X_sym, 
            YB_L_val, PA_Y_sym, PB_Y_sym, S_Y_sym,
            ZC_L_val, PA_Z_sym, PB_Z_sym, S_Z_sym,
            # Global representations and results
            XA_global_repr_ic2, 
            sum_YB_ZC_inter_dict["debug_info"]["X_global_repr_dbg"], # YB_G for sum
            sum_YB_ZC_inter_dict["debug_info"]["Y_global_repr_dbg"], # ZC_G for sum
            sum_YB_ZC_inter_dict["global_repr"], 
            LHS_dist_final_global_repr,
            prod_XA_YB_inter_dict["global_repr"], 
            prod_XA_ZC_inter_dict["global_repr"],
            RHS_dist_final_global_repr
        ]
        debug_ops_IC2 = [sum_YB_ZC_inter_dict, prod_XA_YB_inter_dict, prod_XA_ZC_inter_dict]


        prove_or_find_counterexample(s, f"IC-2 Distrib. Inter-Cycle (Global Omega={global_omega_py})",
                                     all_IC2_assertions, property_IC2,
                                     model_vars_to_print=model_vars_IC2,
                                     op_result_dicts_for_debug=debug_ops_IC2)
        del s
        print("-" * 80)

    print("\n====== AVC Inter-Cycle Global Archetype Impact Test Complete ======")