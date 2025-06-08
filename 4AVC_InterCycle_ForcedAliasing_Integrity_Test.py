from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Test with a coarse GCA (Omega_G=3) and richer local frames
GLOBAL_CANONICAL_OMEGA_PY = 3
LOCAL_SPAN_S_X_PY = 7
LOCAL_SPAN_S_Y_PY = 5 
DEFAULT_P_A_OFFSET_X = 0
DEFAULT_P_A_OFFSET_Y = 10 # Ensure distinct local value ranges

# --- Phase 1: Foundational Definitions (Canonical GCA) ---
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

def avc_equiv_global(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any]) -> FNode: # Renamed for clarity
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"]) 
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"]) 
    finite_finite_equal_val = And(i1_repr["is_finite"], 
                                  i2_repr["is_finite"], 
                                  Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Phase 2: Global Canonical Raw Operations ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    # Copied from previous scripts
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
                                       result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
    # Ensure val for AS_G is global_omega_smt (handled by mapping and initial state constraints)
    return res_repr
    
# --- Phase 3: Local Frame Definitions and "Broader" Mapping to GCA ---
def is_local_ZS_val(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS_val(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI_val(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

def map_local_to_global_archetype_repr_broader(
    Local_val_sym: FNode, 
    PA_local_sym: FNode, PB_local_sym: FNode, # Span_local_sym not directly needed if using k_L
    Omega_global_smt: FNode, 
    global_repr_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    
    glob_repr = create_intensity_representation(global_repr_name_prefix)
    assertions = [glob_repr["constraints"]]

    is_L_ZS = is_local_ZS_val(Local_val_sym, PA_local_sym)
    is_L_AS = is_local_AS_val(Local_val_sym, PB_local_sym)
    # is_L_DFI implies Local_val_sym > PA_local_sym and Local_val_sym < PB_local_sym

    # Map Local ZS to Global ZS
    assertions.append(Implies(is_L_ZS, And(glob_repr["is_zero"], Not(glob_repr["is_areo"]), Not(glob_repr["is_finite"]))))
    
    # Map Local AS to Global AS
    assertions.append(Implies(is_L_AS, And(glob_repr["is_areo"], Not(glob_repr["is_zero"]), Not(glob_repr["is_finite"]),
                                         Equals(glob_repr["val"], Omega_global_smt))))

    # Map Local DFI using "Broader" strategy
    # k_L is the local DFI step number (1, 2, ...)
    k_L_sym = Local_val_sym - PA_local_sym 

    # If local DFI, map k_L to Fp_G(k_L) if 1 <= k_L < Omega_Global, else to AS_G
    map_to_Fp_G = And(
        glob_repr["is_finite"], Not(glob_repr["is_zero"]), Not(glob_repr["is_areo"]),
        Equals(glob_repr["val"], k_L_sym),
        k_L_sym > Int(0), # Ensured by is_local_DFI_val for Local_val_sym
        k_L_sym < Omega_global_smt # Broader mapping condition
    )
    map_to_AS_G = And(
        glob_repr["is_areo"], Not(glob_repr["is_zero"]), Not(glob_repr["is_finite"]),
        Equals(glob_repr["val"], Omega_global_smt)
    )

    assertions.append(Implies(
        is_local_DFI_val(Local_val_sym, PA_local_sym, PB_local_sym), # If input is local DFI
        Ite(
            And(k_L_sym > Int(0), k_L_sym < Omega_global_smt), # Check if k_L is representable as Fp_G
            map_to_Fp_G,
            map_to_AS_G # k_L is too large (or <=0, though DFI prevents <=0) for Fp_G, map to AS_G
        )
    ))
    # Ensure basic validity of mapped Fp_G value
    assertions.append(Implies(glob_repr["is_finite"], And(glob_repr["val"] > Int(0), glob_repr["val"] < Omega_global_smt)))

    return glob_repr, assertions

# --- Phase 4: Generic Property Prover ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True):
    # (Copied from previous script, includes robust FNode printing)
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
            for var_item in model_vars_to_print:
                if isinstance(var_item, dict) and "name" in var_item : 
                    val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                    is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                    is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode):
                    name_to_print = var_item.symbol_name() if var_item.is_symbol() else f"Expression({str(var_item)})"
                    value_str = "?"
                    try: value_str = str(solver.get_value(var_item))
                    except Exception: value_str = "(Error getting value)" # Should not happen if SAT
                    print(f"  {name_to_print}: {value_str}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Inter-Cycle Coarse GCA Sensitivity Test ======\n")

    s = Solver(name="z3")
    global_omega_smt = Int(GLOBAL_CANONICAL_OMEGA_PY)
    print(f"\n\n===== TESTING INTER-CYCLE OPERATIONS WITH COARSE GCA (Omega_G = {GLOBAL_CANONICAL_OMEGA_PY}) =====\n")

    # --- Local Frame X Definitions ---
    PA_X_val_sym = Symbol("PA_X_cgs", solver_INT_TYPE) # cgs for Coarse GCA Sensitivity
    PB_X_val_sym = Symbol("PB_X_cgs", solver_INT_TYPE)
    S_X_val_sym  = Symbol("S_X_cgs", solver_INT_TYPE)
    s.add_assertion(Equals(PA_X_val_sym, Int(DEFAULT_P_A_OFFSET_X)))
    s.add_assertion(Equals(S_X_val_sym, Int(LOCAL_SPAN_S_X_PY)))
    s.add_assertion(Equals(PB_X_val_sym, PA_X_val_sym + S_X_val_sym))
    s.add_assertion(S_X_val_sym > Int(0))

    # --- Local Frame Y Definitions ---
    PA_Y_val_sym = Symbol("PA_Y_cgs", solver_INT_TYPE)
    PB_Y_val_sym = Symbol("PB_Y_cgs", solver_INT_TYPE)
    S_Y_val_sym  = Symbol("S_Y_cgs", solver_INT_TYPE)
    s.add_assertion(Equals(PA_Y_val_sym, Int(DEFAULT_P_A_OFFSET_Y)))
    s.add_assertion(Equals(S_Y_val_sym, Int(LOCAL_SPAN_S_Y_PY)))
    s.add_assertion(Equals(PB_Y_val_sym, PA_Y_val_sym + S_Y_val_sym))
    s.add_assertion(S_Y_val_sym > Int(0))

    # --- Symbolic Local Values ---
    LX1_val_sym = Symbol("LX1_cgs", solver_INT_TYPE)
    LX2_val_sym = Symbol("LX2_cgs", solver_INT_TYPE)
    LY1_val_sym = Symbol("LY1_cgs", solver_INT_TYPE)
    LY2_val_sym = Symbol("LY2_cgs", solver_INT_TYPE)

    # --- Test IC-CGS-1: Sensitivity of Addition (LX1 + LY1) vs (LX2 + LY2) ---
    # LX1, LX2 are different local DFIs in Frame X. LY1, LY2 are different local DFIs in Frame Y.
    # Do they become equivalent after mapping and GCA operation due to coarse GCA?
    print(f"--- Test IC-CGS-1: (LX1+LY1) vs (LX2+LY2) with coarse GCA Omega_G={GLOBAL_CANONICAL_OMEGA_PY} ---")
    s.push()
    # Setup specific local DFI values to induce aliasing or distinct mapping
    # LX1 = PA_X + 2 (k_L=2). For GCA Omega=3, maps to Fp_G(2)
    # LX2 = PA_X + 4 (k_L=4). For GCA Omega=3, maps to AS_G (since 4 >= 3)
    s.add_assertion(Equals(LX1_val_sym, PA_X_val_sym + Int(2)))
    s.add_assertion(Equals(LX2_val_sym, PA_X_val_sym + Int(4)))
    s.add_assertion(is_local_DFI_val(LX1_val_sym, PA_X_val_sym, PB_X_val_sym)) # 2 is DFI in S_X=7
    s.add_assertion(is_local_DFI_val(LX2_val_sym, PA_X_val_sym, PB_X_val_sym)) # 4 is DFI in S_X=7

    # LY1 = PA_Y + 1 (k_L=1). For GCA Omega=3, maps to Fp_G(1)
    s.add_assertion(Equals(LY1_val_sym, PA_Y_val_sym + Int(1)))
    s.add_assertion(is_local_DFI_val(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym)) # 1 is DFI in S_Y=5

    # Map to Global
    LX1_glob_repr, lx1_glob_asserts = map_local_to_global_archetype_repr_broader(LX1_val_sym, PA_X_val_sym, PB_X_val_sym, global_omega_smt, "LX1glob_cgs1")
    LX2_glob_repr, lx2_glob_asserts = map_local_to_global_archetype_repr_broader(LX2_val_sym, PA_X_val_sym, PB_X_val_sym, global_omega_smt, "LX2glob_cgs1")
    LY1_glob_repr, ly1_glob_asserts = map_local_to_global_archetype_repr_broader(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym, global_omega_smt, "LY1glob_cgs1")
    s.add_assertions(lx1_glob_asserts + lx2_glob_asserts + ly1_glob_asserts)
    
    # Operations in GCA
    Res1_glob = define_smart_raw_add_global_result(LX1_glob_repr, LY1_glob_repr, f"Res1_G_cgs1", global_omega_smt)
    Res2_glob = define_smart_raw_add_global_result(LX2_glob_repr, LY1_glob_repr, f"Res2_G_cgs1", global_omega_smt)
    s.add_assertions([
        Res1_glob["definition"], 
        Res1_glob["constraints"], 
        Implies(Res1_glob["is_areo"], Equals(Res1_glob["val"], global_omega_smt))
    ])
    s.add_assertions([
        Res2_glob["definition"], 
        Res2_glob["constraints"], 
        Implies(Res2_glob["is_areo"], Equals(Res2_glob["val"], global_omega_smt))
    ])
    prop_iccgs1 = avc_equiv_global(Res1_glob, Res2_glob)
    prove_or_find_counterexample(s, f"IC-CGS-1 (LX1+LY1) ~ (LX2+LY1) with Omega_G={GLOBAL_CANONICAL_OMEGA_PY}",
                                 [], prop_iccgs1, # Assertions already added
                                 model_vars_to_print=[LX1_val_sym, LX1_glob_repr, LX2_val_sym, LX2_glob_repr, LY1_val_sym, LY1_glob_repr, Res1_glob, Res2_glob])
    s.pop()

    # --- Test IC-CGS-2: Making results equivalent due to coarse GCA sum ---
    # (LX1 + LY1) vs (LX2 + LY2) where LX1,LY1 and LX2,LY2 map to GCA terms that sum equivalently.
    print(f"\n--- Test IC-CGS-2: (LX1+LY1) vs (LX2+LY2) equivalent sum (Omega_G={GLOBAL_CANONICAL_OMEGA_PY}) ---")
    s.push()
    # LX1 = PA_X + 1 (k_L=1 -> Fp_G(1))
    # LY1 = PA_Y + 2 (k_L=2 -> Fp_G(2))
    # Sum1_G = Fp_G(1) + Fp_G(2) -> AS_G(3) for Omega_G=3
    s.add_assertion(Equals(LX1_val_sym, PA_X_val_sym + Int(1)))
    s.add_assertion(Equals(LY1_val_sym, PA_Y_val_sym + Int(2)))
    s.add_assertion(is_local_DFI_val(LX1_val_sym, PA_X_val_sym, PB_X_val_sym))
    s.add_assertion(is_local_DFI_val(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym))

    # LX2 = PA_X + 2 (k_L=2 -> Fp_G(2))
    # LY2 = PA_Y + 1 (k_L=1 -> Fp_G(1))
    # Sum2_G = Fp_G(2) + Fp_G(1) -> AS_G(3) for Omega_G=3
    s.add_assertion(Equals(LX2_val_sym, PA_X_val_sym + Int(2)))
    s.add_assertion(Equals(LY2_val_sym, PA_Y_val_sym + Int(1)))
    s.add_assertion(is_local_DFI_val(LX2_val_sym, PA_X_val_sym, PB_X_val_sym))
    s.add_assertion(is_local_DFI_val(LY2_val_sym, PA_Y_val_sym, PB_Y_val_sym))

    LX1_glob_repr_cgs2, lx1_glob_asserts_cgs2 = map_local_to_global_archetype_repr_broader(LX1_val_sym, PA_X_val_sym, PB_X_val_sym, global_omega_smt, "LX1glob_cgs2")
    LY1_glob_repr_cgs2, ly1_glob_asserts_cgs2 = map_local_to_global_archetype_repr_broader(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym, global_omega_smt, "LY1glob_cgs2")
    LX2_glob_repr_cgs2, lx2_glob_asserts_cgs2 = map_local_to_global_archetype_repr_broader(LX2_val_sym, PA_X_val_sym, PB_X_val_sym, global_omega_smt, "LX2glob_cgs2")
    LY2_glob_repr_cgs2, ly2_glob_asserts_cgs2 = map_local_to_global_archetype_repr_broader(LY2_val_sym, PA_Y_val_sym, PB_Y_val_sym, global_omega_smt, "LY2glob_cgs2")
    s.add_assertions(lx1_glob_asserts_cgs2 + ly1_glob_asserts_cgs2 + lx2_glob_asserts_cgs2 + ly2_glob_asserts_cgs2)

    Res1_glob_cgs2 = define_smart_raw_add_global_result(LX1_glob_repr_cgs2, LY1_glob_repr_cgs2, f"Res1_G_cgs2", global_omega_smt)
    Res2_glob_cgs2 = define_smart_raw_add_global_result(LX2_glob_repr_cgs2, LY2_glob_repr_cgs2, f"Res2_G_cgs2", global_omega_smt)
    s.add_assertions([
        Res1_glob_cgs2["definition"], 
        Res1_glob_cgs2["constraints"], 
        Implies(Res1_glob_cgs2["is_areo"], Equals(Res1_glob_cgs2["val"], global_omega_smt))
    ])
    s.add_assertions([
        Res2_glob_cgs2["definition"], 
        Res2_glob_cgs2["constraints"], 
        Implies(Res2_glob_cgs2["is_areo"], Equals(Res2_glob_cgs2["val"], global_omega_smt))
    ])

    prop_iccgs2 = avc_equiv_global(Res1_glob_cgs2, Res2_glob_cgs2)
    prove_or_find_counterexample(s, f"IC-CGS-2 (LX1+LY1) ~ (LX2+LY2) equivalent sum Omega_G={GLOBAL_CANONICAL_OMEGA_PY}",
                                 [], prop_iccgs2,
                                 model_vars_to_print=[
                                     LX1_val_sym, LX1_glob_repr_cgs2, LY1_val_sym, LY1_glob_repr_cgs2, Res1_glob_cgs2,
                                     LX2_val_sym, LX2_glob_repr_cgs2, LY2_val_sym, LY2_glob_repr_cgs2, Res2_glob_cgs2,
                                 ])
    s.pop()
    
    del s
    print("-" * 80)

    print("\n====== AVC Inter-Cycle Coarse GCA Sensitivity Test Complete ======")