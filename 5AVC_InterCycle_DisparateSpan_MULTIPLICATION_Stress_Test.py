# Script Name: AVC_InterCycle_DisparateSpan_MULTIPLICATION_Stress_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Requirement 3 (Extended with Multiplication): Disparate Span Interaction, Varying GCA, Mappings
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
def raw_mul_logic_builder_gca(i1: Dict[str, Any], i2: Dict[str, Any],
                              res: Dict[str, Any], global_omega_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"]
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]),
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], global_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]), # AS * Fp(>0) -> AS
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], global_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]), # Fp(>0) * AS -> AS
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], global_omega_smt)) ))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_prod >= global_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], global_omega_smt)),
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
    return And(formulas)

def define_raw_mul_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any],
                                   result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder_gca(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
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
    
    # This condition implies local DFI exists, so S_local_sym >= 2
    # And GCA DFI exists, so Omega_global_py >= 2 (Omega_global_smt >= 2)
    dfi_mapping_condition = And(is_L_DFI, S_local_sym >= Int(2), Omega_global_smt >= Int(2))

    k_L_one_based = Local_val_sym - PA_local_sym 
    k_L_zero_based = k_L_one_based - Int(1)       # Ranges from 0 to S_local_sym - 2
    
    num_local_dfi_intervals = S_local_sym - Int(1)  # Denominator: num distinct DFIs
    num_global_dfi_intervals = Omega_global_smt - Int(1) # Multiplier: num distinct GCA DFIs

    scaled_numerator = k_L_zero_based * num_global_dfi_intervals 
    # Denominator num_local_dfi_intervals will be >= 1 if dfi_mapping_condition implies S_local_sym >= 2
    quantized_global_zero_based_step = scaled_numerator / num_local_dfi_intervals 
    final_global_one_based_val = quantized_global_zero_based_step + Int(1)

    map_to_Fp_G_prop = And(
        glob_repr["is_finite"], Not(glob_repr["is_zero"]), Not(glob_repr["is_areo"]),
        Equals(glob_repr["val"], final_global_one_based_val)
    )
    
    assertions.append(Implies(dfi_mapping_condition, map_to_Fp_G_prop))
    # If not dfi_mapping_condition (but is_L_DFI is true), it means Omega_global_py <=1 (no GCA DFI), map to AS_G
    assertions.append(Implies(And(is_L_DFI, Not(And(S_local_sym >= Int(2), Omega_global_smt >= Int(2)))), map_dfi_to_AS_G))
            
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
    print("====== AVC Inter-Cycle Disparate Span MULTIPLICATION Stress Test ======\n")

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
            
            print(f"\n\n===== GCA Omega_G = {global_omega_py}, Mapping = {map_name}, Op = MULTIPLICATION =====")
            print(f"Local X ('{frame_x_spec['name']}'): S_X={frame_x_spec['span_py']}, PA_X={frame_x_spec['pa_offset_py']}")
            print(f"Local Y ('{frame_y_spec['name']}'): S_Y={frame_y_spec['span_py']}, PA_Y={frame_y_spec['pa_offset_py']}\n")

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
            elif LX1_OFFSET_FROM_PA_X == 0 : s.add_assertion(is_local_ZS_val(LX1_val_sym, PA_X_val_sym))
            elif LX1_OFFSET_FROM_PA_X == frame_x_spec['span_py']: s.add_assertion(is_local_AS_val(LX1_val_sym, PB_X_val_sym))

            if LX2_OFFSET_FROM_PA_X > 0 and LX2_OFFSET_FROM_PA_X < frame_x_spec['span_py']:
                 s.add_assertion(is_local_DFI_val(LX2_val_sym, PA_X_val_sym, PB_X_val_sym))
            elif LX2_OFFSET_FROM_PA_X == 0 : s.add_assertion(is_local_ZS_val(LX2_val_sym, PA_X_val_sym))
            elif LX2_OFFSET_FROM_PA_X == frame_x_spec['span_py']: s.add_assertion(is_local_AS_val(LX2_val_sym, PB_X_val_sym))

            if LY1_OFFSET_FROM_PA_Y > 0 and LY1_OFFSET_FROM_PA_Y < frame_y_spec['span_py']:
                 s.add_assertion(is_local_DFI_val(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym))
            elif LY1_OFFSET_FROM_PA_Y == 0 : s.add_assertion(is_local_ZS_val(LY1_val_sym, PA_Y_val_sym))
            elif LY1_OFFSET_FROM_PA_Y == frame_y_spec['span_py']: s.add_assertion(is_local_AS_val(LY1_val_sym, PB_Y_val_sym))


            name_suffix = f"G{global_omega_py}M_{map_name}" # M for Mul
            if map_name == "PropQuant":
                LX1_glob_repr, lx1_asserts = map_function(LX1_val_sym, PA_X_val_sym, PB_X_val_sym, S_X_val_sym, current_global_omega_smt, global_omega_py, f"LX1gS_{name_suffix}")
                LX2_glob_repr, lx2_asserts = map_function(LX2_val_sym, PA_X_val_sym, PB_X_val_sym, S_X_val_sym, current_global_omega_smt, global_omega_py, f"LX2gS_{name_suffix}")
                LY1_glob_repr, ly1_asserts = map_function(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym, S_Y_val_sym, current_global_omega_smt, global_omega_py, f"LY1gS_{name_suffix}")
            else: # Broader
                LX1_glob_repr, lx1_asserts = map_function(LX1_val_sym, PA_X_val_sym, PB_X_val_sym, current_global_omega_smt, f"LX1gS_{name_suffix}")
                LX2_glob_repr, lx2_asserts = map_function(LX2_val_sym, PA_X_val_sym, PB_X_val_sym, current_global_omega_smt, f"LX2gS_{name_suffix}")
                LY1_glob_repr, ly1_asserts = map_function(LY1_val_sym, PA_Y_val_sym, PB_Y_val_sym, current_global_omega_smt, f"LY1gS_{name_suffix}")
            s.add_assertions(lx1_asserts + lx2_asserts + ly1_asserts)

            # Test IDMUL-1: (LX1_G * LY1_G) ~_G (LX2_G * LY1_G)
            Res1_G_idm1 = define_raw_mul_global_result(LX1_glob_repr, LY1_glob_repr, f"Res1M1_{name_suffix}", current_global_omega_smt)
            Res2_G_idm1 = define_raw_mul_global_result(LX2_glob_repr, LY1_glob_repr, f"Res2M1_{name_suffix}", current_global_omega_smt)
            s.add_assertions([Res1_G_idm1["definition"], Res1_G_idm1["constraints"], Res2_G_idm1["definition"], Res2_G_idm1["constraints"]])
            prop_idm1 = avc_equiv_global(Res1_G_idm1, Res2_G_idm1)
            model_vars_idm1 = [PA_X_val_sym, PB_X_val_sym, S_X_val_sym, LX1_val_sym, LX2_val_sym, PA_Y_val_sym, PB_Y_val_sym, S_Y_val_sym, LY1_val_sym, LX1_glob_repr, LX2_glob_repr, LY1_glob_repr, Res1_G_idm1, Res2_G_idm1]
            prove_or_find_counterexample(s, f"IDMUL-1 (LX1*LY1) vs (LX2*LY1) (Omega_G={global_omega_py}, Map={map_name})", [], prop_idm1, model_vars_to_print=model_vars_idm1)

            # Test IDMUL-2: (LY1_G * LX1_G) ~_G (LY1_G * LX2_G)
            Res1_G_idm2 = define_raw_mul_global_result(LY1_glob_repr, LX1_glob_repr, f"Res1M2_{name_suffix}", current_global_omega_smt)
            Res2_G_idm2 = define_raw_mul_global_result(LY1_glob_repr, LX2_glob_repr, f"Res2M2_{name_suffix}", current_global_omega_smt)
            s.add_assertions([Res1_G_idm2["definition"], Res1_G_idm2["constraints"], Res2_G_idm2["definition"], Res2_G_idm2["constraints"]])
            prop_idm2 = avc_equiv_global(Res1_G_idm2, Res2_G_idm2)
            model_vars_idm2 = [PA_X_val_sym, PB_X_val_sym, S_X_val_sym, LX1_val_sym, LX2_val_sym, PA_Y_val_sym, PB_Y_val_sym, S_Y_val_sym, LY1_val_sym, LX1_glob_repr, LX2_glob_repr, LY1_glob_repr, Res1_G_idm2, Res2_G_idm2]
            prove_or_find_counterexample(s, f"IDMUL-2 (LY1*LX1) vs (LY1*LX2) (Omega_G={global_omega_py}, Map={map_name})", [], prop_idm2, model_vars_to_print=model_vars_idm2)

            s.pop() 
            del s
            print("-" * 80)
    print("\n====== AVC Inter-Cycle Disparate Span MULTIPLICATION Stress Test Complete ======")