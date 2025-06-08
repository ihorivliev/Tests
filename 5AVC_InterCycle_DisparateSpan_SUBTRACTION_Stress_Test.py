# Script Name: AVC_InterCycle_DisparateSpan_SUBTRACTION_Stress_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Requirement 3 (Extended with Subtraction): Disparate Span Interaction, Varying GCA, Mappings
GCA_OMEGA_VARIANTS = [2, 3, 5, 7, 10, 12] 
LOCAL_FRAME_SPECS = [
    {"name": "X_Rich", "span_py": 10, "pa_offset_py": 0},
    {"name": "Y_Poor", "span_py": 3,  "pa_offset_py": 20}
]
LX1_OFFSET_FROM_PA_X = 1 
LX2_OFFSET_FROM_PA_X = 5 
LY1_OFFSET_FROM_PA_Y = 1 

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

# --- Phase 2: Global Canonical Raw Operations (GCA Operations) ---
# Using the corrected smart_raw_sub_canonical_logic_builder from previous successful test
def smart_raw_sub_canonical_logic_builder(A_repr: Dict[str, Any], B_repr: Dict[str, Any],
                                          Res_repr: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    res_is_ZS_true = Res_repr["is_zero"]
    res_is_AS_false_for_ZS = Not(Res_repr["is_areo"])
    res_is_Fp_false_for_ZS = Not(Res_repr["is_finite"])
    set_res_ZS = And(res_is_ZS_true, res_is_AS_false_for_ZS, res_is_Fp_false_for_ZS)

    res_is_ZS_false_for_AS = Not(Res_repr["is_zero"])
    res_is_AS_true = Res_repr["is_areo"]
    res_is_Fp_false_for_AS = Not(Res_repr["is_finite"])
    res_val_is_Omega = Equals(Res_repr["val"], current_omega_smt)
    set_res_AS = And(res_is_ZS_false_for_AS, res_is_AS_true, res_is_Fp_false_for_AS, res_val_is_Omega)

    res_is_ZS_false_for_Fp = Not(Res_repr["is_zero"])
    res_is_AS_false_for_Fp = Not(Res_repr["is_areo"])
    res_is_Fp_true = Res_repr["is_finite"]
    def set_res_Fp(val_expr: FNode) -> FNode:
        return And(res_is_ZS_false_for_Fp, res_is_AS_false_for_Fp, res_is_Fp_true, Equals(Res_repr["val"], val_expr))

    return Ite(A_repr["is_zero"],
               Ite(B_repr["is_zero"], set_res_ZS,
               Ite(B_repr["is_finite"], set_res_AS,
               set_res_ZS
               )),
           Ite(A_repr["is_areo"],
               Ite(B_repr["is_zero"], set_res_ZS, 
               Ite(B_repr["is_finite"], set_res_AS,
               set_res_ZS
               )),
               Ite(B_repr["is_zero"], set_res_Fp(A_repr["val"]),
               Ite(B_repr["is_finite"],
                   Ite(Equals(A_repr["val"], B_repr["val"]), set_res_ZS,
                   Ite(A_repr["val"] > B_repr["val"], set_res_Fp(A_repr["val"] - B_repr["val"]),
                                                      set_res_AS
                   )),
               set_res_Fp(A_repr["val"])
               ))
           ))

def define_smart_raw_sub_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any],
                                       result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_sub_canonical_logic_builder(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], global_omega_smt)))
    return res_repr
    
# --- Phase 3: Local Frame Definitions and Mappings to GCA ---
def is_local_ZS_val(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS_val(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI_val(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

# Mapping Strategy 1: "Broader" Mapping
def map_local_to_global_repr_broader(
    Local_val_sym: FNode,
    PA_local_sym: FNode, PB_local_sym: FNode, 
    Omega_global_smt: FNode,
    global_repr_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    glob_repr = create_intensity_representation(global_repr_name_prefix)
    assertions = [glob_repr["constraints"], Implies(glob_repr["is_areo"], Equals(glob_repr["val"], Omega_global_smt))]

    is_L_ZS = is_local_ZS_val(Local_val_sym, PA_local_sym)
    is_L_AS = is_local_AS_val(Local_val_sym, PB_local_sym)
    is_L_DFI = is_local_DFI_val(Local_val_sym, PA_local_sym, PB_local_sym)

    assertions.append(Implies(is_L_ZS, And(glob_repr["is_zero"], Not(glob_repr["is_areo"]), Not(glob_repr["is_finite"]))))
    assertions.append(Implies(is_L_AS, And(glob_repr["is_areo"], Not(glob_repr["is_zero"]), Not(glob_repr["is_finite"]))))

    k_L_sym = Local_val_sym - PA_local_sym
    map_to_Fp_G = And(
        glob_repr["is_finite"], Not(glob_repr["is_zero"]), Not(glob_repr["is_areo"]),
        Equals(glob_repr["val"], k_L_sym),
        k_L_sym > Int(0),
        k_L_sym < Omega_global_smt
    )
    map_to_AS_G = And(glob_repr["is_areo"], Not(glob_repr["is_zero"]), Not(glob_repr["is_finite"]))
    assertions.append(Implies(is_L_DFI, Ite(And(k_L_sym > Int(0), k_L_sym < Omega_global_smt), map_to_Fp_G, map_to_AS_G)))
    assertions.append(Implies(glob_repr["is_finite"], And(glob_repr["val"] > Int(0), glob_repr["val"] < Omega_global_smt)))
    return glob_repr, assertions

# Mapping Strategy 2: "Proportional-Quantized" Mapping
def map_local_to_global_repr_proportional_quantized(
    Local_val_sym: FNode,
    PA_local_sym: FNode, PB_local_sym: FNode, S_local_sym: FNode, 
    Omega_global_smt: FNode, Omega_global_py: int, 
    global_repr_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    glob_repr = create_intensity_representation(global_repr_name_prefix)
    assertions = [glob_repr["constraints"], Implies(glob_repr["is_areo"], Equals(glob_repr["val"], Omega_global_smt))]

    is_L_ZS = is_local_ZS_val(Local_val_sym, PA_local_sym)
    is_L_AS = is_local_AS_val(Local_val_sym, PB_local_sym)
    is_L_DFI = is_local_DFI_val(Local_val_sym, PA_local_sym, PB_local_sym)

    assertions.append(Implies(is_L_ZS, And(glob_repr["is_zero"], Not(glob_repr["is_areo"]), Not(glob_repr["is_finite"]))))
    assertions.append(Implies(is_L_AS, And(glob_repr["is_areo"], Not(glob_repr["is_zero"]), Not(glob_repr["is_finite"]))))

    map_dfi_to_AS_G = And(glob_repr["is_areo"], Not(glob_repr["is_zero"]), Not(glob_repr["is_finite"]))
    
    if Omega_global_py <= 1:
        assertions.append(Implies(is_L_DFI, map_dfi_to_AS_G))
    else:
        # This branch assumes S_local_sym >= 2 for DFI to be true
        k_L_one_based = Local_val_sym - PA_local_sym
        k_L_zero_based = k_L_one_based - Int(1)
        
        num_local_dfi_intervals = S_local_sym - Int(1)
        num_global_dfi_intervals = Omega_global_smt - Int(1)

        # Default to AS_G if local span is too small to have intervals for scaling DFI
        # or if global DFI range is trivial (already handled by Omega_global_py <=1)
        # This ITE handles S_local_sym = 1 (num_local_dfi_intervals = 0), preventing division by zero.
        # is_L_DFI implies S_local_sym >= 2, so num_local_dfi_intervals >= 1.
        
        scaled_numerator = k_L_zero_based * num_global_dfi_intervals
        # Denominator S_local_sym - Int(1) will be >= 1 if is_L_DFI is true (S_local_sym >= 2)
        quantized_global_zero_based_step = scaled_numerator / num_local_dfi_intervals
        final_global_one_based_val = quantized_global_zero_based_step + Int(1)

        map_to_Fp_G_prop = And(
            glob_repr["is_finite"], Not(glob_repr["is_zero"]), Not(glob_repr["is_areo"]),
            Equals(glob_repr["val"], final_global_one_based_val)
            # Constraints for final_global_one_based_val ( >0, < Omega_global_smt) are implicitly handled by formula if inputs are valid DFI
        )
        assertions.append(Implies(is_L_DFI, map_to_Fp_G_prop ))
            
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
                elif isinstance(var_item, FNode) and var_item.is_symbol():
                     print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
    solver.pop()
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Inter-Cycle Disparate Span SUBTRACTION Stress Test ======\n")

    frame_x_spec = LOCAL_FRAME_SPECS[0]
    frame_y_spec = LOCAL_FRAME_SPECS[1]

    PA_X_val_sym = Symbol(f"PA_{frame_x_spec['name']}", solver_INT_TYPE)
    PB_X_val_sym = Symbol(f"PB_{frame_x_spec['name']}", solver_INT_TYPE)
    S_X_val_sym  = Symbol(f"S_{frame_x_spec['name']}", solver_INT_TYPE)
    PA_Y_val_sym = Symbol(f"PA_{frame_y_spec['name']}", solver_INT_TYPE)
    PB_Y_val_sym = Symbol(f"PB_{frame_y_spec['name']}", solver_INT_TYPE)
    S_Y_val_sym  = Symbol(f"S_{frame_y_spec['name']}", solver_INT_TYPE)

    LX1_val_sym = Symbol("LX1_val", solver_INT_TYPE)
    LX2_val_sym = Symbol("LX2_val", solver_INT_TYPE)
    LY1_val_sym = Symbol("LY1_val", solver_INT_TYPE)

    mapping_strategies = {
        "Broader": map_local_to_global_repr_broader,
        "PropQuant": map_local_to_global_repr_proportional_quantized
    }

    for global_omega_py in GCA_OMEGA_VARIANTS:
        for map_name, map_function in mapping_strategies.items():
            s = Solver(name="z3")
            current_global_omega_smt = Int(global_omega_py)
            
            print(f"\n\n===== GCA Omega_G = {global_omega_py}, Mapping = {map_name}, Op = SUBTRACTION =====")
            print(f"Local X ('{frame_x_spec['name']}'): S_X={frame_x_spec['span_py']}, PA_X={frame_x_spec['pa_offset_py']}")
            print(f"Local Y ('{frame_y_spec['name']}'): S_Y={frame_y_spec['span_py']}, PA_Y={frame_y_spec['pa_offset_py']}\n")

            # Setup Frames
            s.add_assertion(Equals(PA_X_val_sym, Int(frame_x_spec['pa_offset_py'])))
            s.add_assertion(Equals(S_X_val_sym, Int(frame_x_spec['span_py'])))
            s.add_assertion(Equals(PB_X_val_sym, PA_X_val_sym + S_X_val_sym))
            s.add_assertion(S_X_val_sym > Int(0))
            s.add_assertion(Equals(PA_Y_val_sym, Int(frame_y_spec['pa_offset_py'])))
            s.add_assertion(Equals(S_Y_val_sym, Int(frame_y_spec['span_py'])))
            s.add_assertion(Equals(PB_Y_val_sym, PA_Y_val_sym + S_Y_val_sym))
            s.add_assertion(S_Y_val_sym > Int(0))

            s.push() 
            val_LX1 = PA_X_val_sym + Int(LX1_OFFSET_FROM_PA_X)
            val_LX2 = PA_X_val_sym + Int(LX2_OFFSET_FROM_PA_X)
            val_LY1 = PA_Y_val_sym + Int(LY1_OFFSET_FROM_PA_Y)
            s.add_assertion(Equals(LX1_val_sym, val_LX1))
            s.add_assertion(Equals(LX2_val_sym, val_LX2))
            s.add_assertion(Equals(LY1_val_sym, val_LY1))
            if LX1_OFFSET_FROM_PA_X > 0 and LX1_OFFSET_FROM_PA_X < frame_x_spec['span_py']:
                 s.add_assertion(is_local_DFI_val(LX1_val_sym, PA_X_val_sym, PB_X_val_sym))
            if LX2_OFFSET_FROM_PA_X > 0 and LX2_OFFSET_FROM_PA_X < frame_x_spec['span_py']:
                 s.add_assertion(is_local_DFI_val(LX2_val_sym, PA_X_val_sym, PB_X_val_sym))
            if LY1_OFFSET_FROM_PA_Y > 0 and LY1_OFFSET_FROM_PA_Y < frame_y_spec['span_py']:
                 s.add_assertion(is_local_DFI_val(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym))

            name_suffix = f"G{global_omega_py}_{map_name}"
            if map_name == "PropQuant":
                LX1_glob_repr, lx1_asserts = map_function(LX1_val_sym, PA_X_val_sym, PB_X_val_sym, S_X_val_sym, current_global_omega_smt, global_omega_py, f"LX1gS_{name_suffix}")
                LX2_glob_repr, lx2_asserts = map_function(LX2_val_sym, PA_X_val_sym, PB_X_val_sym, S_X_val_sym, current_global_omega_smt, global_omega_py, f"LX2gS_{name_suffix}")
                LY1_glob_repr, ly1_asserts = map_function(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym, S_Y_val_sym, current_global_omega_smt, global_omega_py, f"LY1gS_{name_suffix}")
            else: # Broader
                LX1_glob_repr, lx1_asserts = map_function(LX1_val_sym, PA_X_val_sym, PB_X_val_sym, current_global_omega_smt, f"LX1gS_{name_suffix}")
                LX2_glob_repr, lx2_asserts = map_function(LX2_val_sym, PA_X_val_sym, PB_X_val_sym, current_global_omega_smt, f"LX2gS_{name_suffix}")
                LY1_glob_repr, ly1_asserts = map_function(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym, current_global_omega_smt, f"LY1gS_{name_suffix}")
            s.add_assertions(lx1_asserts + lx2_asserts + ly1_asserts)

            # Test IDSUB-1: (LX1_G - LY1_G) ~_G (LX2_G - LY1_G)
            Res1_G_ids1 = define_smart_raw_sub_global_result(LX1_glob_repr, LY1_glob_repr, f"Res1S1_{name_suffix}", current_global_omega_smt)
            Res2_G_ids1 = define_smart_raw_sub_global_result(LX2_glob_repr, LY1_glob_repr, f"Res2S1_{name_suffix}", current_global_omega_smt)
            s.add_assertions([Res1_G_ids1["definition"], Res1_G_ids1["constraints"], Res2_G_ids1["definition"], Res2_G_ids1["constraints"]])
            prop_ids1 = avc_equiv_global(Res1_G_ids1, Res2_G_ids1)
            model_vars_ids1 = [PA_X_val_sym, PB_X_val_sym, S_X_val_sym, LX1_val_sym, LX2_val_sym, PA_Y_val_sym, PB_Y_val_sym, S_Y_val_sym, LY1_val_sym, LX1_glob_repr, LX2_glob_repr, LY1_glob_repr, Res1_G_ids1, Res2_G_ids1]
            prove_or_find_counterexample(s, f"IDSUB-1 (LX1-LY1) vs (LX2-LY1) (Omega_G={global_omega_py}, Map={map_name})", [], prop_ids1, model_vars_to_print=model_vars_ids1)

            # Test IDSUB-2: (LY1_G - LX1_G) ~_G (LY1_G - LX2_G)
            Res1_G_ids2 = define_smart_raw_sub_global_result(LY1_glob_repr, LX1_glob_repr, f"Res1S2_{name_suffix}", current_global_omega_smt)
            Res2_G_ids2 = define_smart_raw_sub_global_result(LY1_glob_repr, LX2_glob_repr, f"Res2S2_{name_suffix}", current_global_omega_smt)
            s.add_assertions([Res1_G_ids2["definition"], Res1_G_ids2["constraints"], Res2_G_ids2["definition"], Res2_G_ids2["constraints"]])
            prop_ids2 = avc_equiv_global(Res1_G_ids2, Res2_G_ids2)
            model_vars_ids2 = [PA_X_val_sym, PB_X_val_sym, S_X_val_sym, LX1_val_sym, LX2_val_sym, PA_Y_val_sym, PB_Y_val_sym, S_Y_val_sym, LY1_val_sym, LX1_glob_repr, LX2_glob_repr, LY1_glob_repr, Res1_G_ids2, Res2_G_ids2]
            prove_or_find_counterexample(s, f"IDSUB-2 (LY1-LX1) vs (LY1-LX2) (Omega_G={global_omega_py}, Map={map_name})", [], prop_ids2, model_vars_to_print=model_vars_ids2)

            s.pop() 
            del s
            print("-" * 80)
    print("\n====== AVC Inter-Cycle Disparate Span SUBTRACTION Stress Test Complete ======")