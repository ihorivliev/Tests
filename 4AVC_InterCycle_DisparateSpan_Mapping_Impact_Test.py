from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# GCA_OMEGA_VARIANTS = [3, 7] # Test with a coarse GCA and a richer GCA
GCA_OMEGA_VARIANTS = [3, 5, 7] # Test with a coarse GCA and a richer GCA. S=5 added for GCA testing

# Local Frame Specs
LOCAL_FRAME_SPECS = [
    {"name": "X_Rich", "span": 10, "pa_offset": 0}, # Richer local frame
    {"name": "Y_Poor", "span": 3,  "pa_offset": 20} # Poorer local frame
]

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

def avc_equiv_global(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any]) -> FNode:
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
    PA_local_sym: FNode, PB_local_sym: FNode, 
    Omega_global_smt: FNode, 
    global_repr_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    
    glob_repr = create_intensity_representation(global_repr_name_prefix)
    assertions = [glob_repr["constraints"]]

    is_L_ZS = is_local_ZS_val(Local_val_sym, PA_local_sym)
    is_L_AS = is_local_AS_val(Local_val_sym, PB_local_sym)
    
    assertions.append(Implies(is_L_ZS, And(glob_repr["is_zero"], Not(glob_repr["is_areo"]), Not(glob_repr["is_finite"]))))
    assertions.append(Implies(is_L_AS, And(glob_repr["is_areo"], Not(glob_repr["is_zero"]), Not(glob_repr["is_finite"]),
                                         Equals(glob_repr["val"], Omega_global_smt))))

    k_L_sym = Local_val_sym - PA_local_sym 
    map_to_Fp_G = And(
        glob_repr["is_finite"], Not(glob_repr["is_zero"]), Not(glob_repr["is_areo"]),
        Equals(glob_repr["val"], k_L_sym),
        k_L_sym > Int(0), 
        k_L_sym < Omega_global_smt
    )
    map_to_AS_G = And(
        glob_repr["is_areo"], Not(glob_repr["is_zero"]), Not(glob_repr["is_finite"]),
        Equals(glob_repr["val"], Omega_global_smt)
    )
    assertions.append(Implies(
        is_local_DFI_val(Local_val_sym, PA_local_sym, PB_local_sym), 
        Ite(And(k_L_sym > Int(0), k_L_sym < Omega_global_smt), map_to_Fp_G, map_to_AS_G)))
    assertions.append(Implies(glob_repr["is_finite"], And(glob_repr["val"] > Int(0), glob_repr["val"] < Omega_global_smt)))
    return glob_repr, assertions

# --- Phase 4: Generic Property Prover ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True):
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
                    except Exception: value_str = "(Error getting value)"
                    print(f"  {name_to_print}: {value_str}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Inter-Cycle Disparate Span Mapping Impact Test ======\n")

    # Define Local Frame X ("Rich")
    PA_X_val_sym = Symbol("PA_X_idsm", solver_INT_TYPE) # idsm for Inter-Cycle Disparate Span Mapping
    PB_X_val_sym = Symbol("PB_X_idsm", solver_INT_TYPE)
    S_X_val_sym  = Symbol("S_X_idsm", solver_INT_TYPE)
    # Define Local Frame Y ("Poor")
    PA_Y_val_sym = Symbol("PA_Y_idsm", solver_INT_TYPE)
    PB_Y_val_sym = Symbol("PB_Y_idsm", solver_INT_TYPE)
    S_Y_val_sym  = Symbol("S_Y_idsm", solver_INT_TYPE)

    # Symbolic Local Values
    LX1_val_sym = Symbol("LX1_idsm", solver_INT_TYPE)
    LX2_val_sym = Symbol("LX2_idsm", solver_INT_TYPE)
    LY1_val_sym = Symbol("LY1_idsm", solver_INT_TYPE)
    # LY2_val_sym = Symbol("LY2_idsm", solver_INT_TYPE) # For IC-CGS-2 style test if added

    for global_omega_py in GCA_OMEGA_VARIANTS:
        s = Solver(name="z3")
        current_global_omega_smt = Int(global_omega_py)
        
        frame_x_spec = LOCAL_FRAME_SPECS[0]
        frame_y_spec = LOCAL_FRAME_SPECS[1]

        print(f"\n\n===== TESTING WITH GCA Omega_G = {global_omega_py} =====")
        print(f"Local Frame X ('{frame_x_spec['name']}'): Span S_X = {frame_x_spec['span']}, PA_X = {frame_x_spec['pa_offset']}")
        print(f"Local Frame Y ('{frame_y_spec['name']}'): Span S_Y = {frame_y_spec['span']}, PA_Y = {frame_y_spec['pa_offset']}\n")

        # Setup Frame X
        s.add_assertion(Equals(PA_X_val_sym, Int(frame_x_spec['pa_offset'])))
        s.add_assertion(Equals(S_X_val_sym, Int(frame_x_spec['span'])))
        s.add_assertion(Equals(PB_X_val_sym, PA_X_val_sym + S_X_val_sym))
        s.add_assertion(S_X_val_sym > Int(0))
        # Setup Frame Y
        s.add_assertion(Equals(PA_Y_val_sym, Int(frame_y_spec['pa_offset'])))
        s.add_assertion(Equals(S_Y_val_sym, Int(frame_y_spec['span'])))
        s.add_assertion(Equals(PB_Y_val_sym, PA_Y_val_sym + S_Y_val_sym))
        s.add_assertion(S_Y_val_sym > Int(0))

        # --- Test IDS-1: (LX_small_step_X + LY_small_step_Y) vs (LX_large_step_to_ASG_X + LY_small_step_Y) ---
        # LX_small_step_X: k_L=1 from Frame X. Maps to Fp_G(1) if Omega_G > 1.
        # LX_large_step_to_ASG_X: k_L such that it maps to AS_G for current Omega_G.
        # LY_small_step_Y: k_L=1 from Frame Y. Maps to Fp_G(1) if Omega_G > 1.
        print(f"--- Test IDS-1 (Omega_G={global_omega_py}): (LX_k1_X + LY_k1_Y) vs (LX_k_ge_OmegaG_X + LY_k1_Y) ---")
        s.push()
        
        # LX1 = PA_X + 1 (k_L=1 for Frame X)
        s.add_assertion(Equals(LX1_val_sym, PA_X_val_sym + Int(1)))
        s.add_assertion(is_local_DFI_val(LX1_val_sym, PA_X_val_sym, PB_X_val_sym)) # Must be valid DFI in X

        # LX2 = PA_X + Omega_G (k_L=Omega_G for Frame X, so maps to AS_G)
        # Ensure Omega_G <= S_X so PA_X + Omega_G can be a valid DFI or AS in Frame X
        if global_omega_py <= frame_x_spec['span']:
            s.add_assertion(Equals(LX2_val_sym, PA_X_val_sym + current_global_omega_smt))
            # This LX2 might be AS_X or DFI_X depending on Omega_G vs S_X
            s.add_assertion(And(LX2_val_sym >= PA_X_val_sym, LX2_val_sym <= PB_X_val_sym))
        else: # Omega_G is larger than S_X, so any k_L from S_X will map to Fp_G
              # Make LX2 a different DFI from LX1 that still maps to Fp_G if possible
            if frame_x_spec['span'] > 1:
                 s.add_assertion(Equals(LX2_val_sym, PA_X_val_sym + Int(2)))
                 s.add_assertion(is_local_DFI_val(LX2_val_sym, PA_X_val_sym, PB_X_val_sym))
            else: # S_X = 1, LX1 is not DFI. This case needs LX1 to be ZS/AS.
                  # For simplicity, this test branch will be less meaningful if S_X=1.
                  # The test primarily targets rich S_X.
                  # To avoid issues, if S_X=1, we can force LX1 to be PA_X and LX2 to be PB_X.
                  # However, the setup requires LX1,LX2 to be specific steps from PA_X.
                  # For now, this branch of the test is more meaningful if S_X >= Omega_G or S_X has multiple DFIs.
                  # Let's assume S_X is rich enough for PA_X + Omega_G to be meaningful or PA_X + 2 for comparison.
                  # If S_X = 1, LX1=PA_X+1 would be PB_X (AS_X).
                  # For this test, we need LX1 (k_L=1) and LX2 (k_L >= Omega_G).
                  # If S_X < Omega_G, then all k_L from S_X are < Omega_G, so all map to Fp_G.
                  # We need to ensure LX1 and LX2 map differently (Fp_G vs AS_G) if possible.
                  # To ensure LX2 maps to AS_G, its k_L must be >= Omega_G.
                  # So, we must have S_X >= Omega_G for LX2 to be PA_X + Omega_G and be valid in Frame X.
                  pass # Will be handled by the SMT if PA_X + Omega_G is out of bounds for S_X

        # LY1 = PA_Y + 1 (k_L=1 for Frame Y)
        s.add_assertion(Equals(LY1_val_sym, PA_Y_val_sym + Int(1)))
        s.add_assertion(is_local_DFI_val(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym)) # Must be valid DFI in Y


        LX1_glob_repr, lx1_asserts = map_local_to_global_archetype_repr_broader(LX1_val_sym, PA_X_val_sym, PB_X_val_sym, current_global_omega_smt, "LX1g_ids1")
        LX2_glob_repr, lx2_asserts = map_local_to_global_archetype_repr_broader(LX2_val_sym, PA_X_val_sym, PB_X_val_sym, current_global_omega_smt, "LX2g_ids1")
        LY1_glob_repr, ly1_asserts = map_local_to_global_archetype_repr_broader(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym, current_global_omega_smt, "LY1g_ids1")
        s.add_assertions(lx1_asserts + lx2_asserts + ly1_asserts)

        Res1_glob = define_smart_raw_add_global_result(LX1_glob_repr, LY1_glob_repr, f"R1g_ids1", current_global_omega_smt)
        Res2_glob = define_smart_raw_add_global_result(LX2_glob_repr, LY1_glob_repr, f"R2g_ids1", current_global_omega_smt)
        s.add_assertions([Res1_glob["definition"], Res1_glob["constraints"], Implies(Res1_glob["is_areo"], Equals(Res1_glob["val"], current_global_omega_smt))])
        s.add_assertions([Res2_glob["definition"], Res2_glob["constraints"], Implies(Res2_glob["is_areo"], Equals(Res2_glob["val"], current_global_omega_smt))])

        prop_ids1 = avc_equiv_global(Res1_glob, Res2_glob)
        # Only run if LX2 setup is valid (i.e. S_X allows k_L >= Omega_G or a distinct k_L)
        # This requires careful conditional execution or ensuring S_X is large enough.
        # The SMT solver will find it UNSAT (property proved) if no counterexample for LX2 can be found.
        # If LX2 = PA_X + current_global_omega_smt is not a DFI in X (e.g. PB_X or > PB_X), mapping logic handles it.
        # We just need to ensure LX1_val_sym and LX2_val_sym are themselves valid values in Frame X.
        # The test setup for LX2_val_sym is:
        # if global_omega_py <= frame_x_spec['span']: LX2 = PA_X + Omega_G (this k_L maps to AS_G)
        # else (Omega_G > S_X): LX2 = PA_X + 2 (this k_L maps to Fp_G(2) if S_X > 1).
        # In this 'else' case, LX1 (k_L=1) maps to Fp_G(1) and LX2 (k_L=2) maps to Fp_G(2).
        # Then Fp_G(1)+Fp_G(1) vs Fp_G(2)+Fp_G(1). These will likely be different. This tests a different aliasing.

        if not (global_omega_py <= frame_x_spec['span'] or frame_x_spec['span'] > 1):
            # If S_X=1, LX1 becomes AS_X. If Omega_G > 1, LX2 setup is tricky.
            # This specific test (LX_k1 vs LX_k_ge_OmegaG) makes most sense if S_X can produce both types of mappings.
             print(f"  Skipping IDS-1 for S_X={frame_x_spec['span']}, Omega_G={global_omega_py} as LX2 setup is less meaningful.")
        else:
            prove_or_find_counterexample(s, f"IDS-1 (LX_k1_X+LY_k1_Y) vs (LX_k_ge_OmegaG_X+LY_k1_Y) (Omega_G={global_omega_py})",
                                     [], prop_ids1,
                                     model_vars_to_print=[LX1_val_sym, LX1_glob_repr, LX2_val_sym, LX2_glob_repr, LY1_val_sym, LY1_glob_repr, Res1_glob, Res2_glob,
                                                          PA_X_val_sym, PB_X_val_sym, S_X_val_sym, PA_Y_val_sym, PB_Y_val_sym, S_Y_val_sym])
        s.pop()
        
        del s
        print("-" * 80)

    print("\n====== AVC Inter-Cycle Disparate Span Mapping Impact Test Complete ======")