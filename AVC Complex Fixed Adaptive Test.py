from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7, 10] # Test various local spans
DEFAULT_P_A_OFFSET = 0 
COMPLEX_CANONICAL_OMEGA_PY = 7 # The fixed "complex" archetype Omega
COMPLEX_CANONICAL_OMEGA_SMT = Int(COMPLEX_CANONICAL_OMEGA_PY)

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

# --- Phase 2: Canonical Raw Operations (Parameterized by current_omega_smt) ---
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

# --- Phase 3: Local Frame, Complex Fixed Adaptive Omega, and Mappings ---

def is_local_ZS(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

def avc_equiv_local(X1_L_val_sym: FNode, X2_L_val_sym: FNode, 
                    P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Or(
        And(is_local_ZS(X1_L_val_sym, P_A_val_sym), is_local_ZS(X2_L_val_sym, P_A_val_sym)),
        And(is_local_AS(X1_L_val_sym, P_B_val_sym), is_local_AS(X2_L_val_sym, P_B_val_sym)),
        And(is_local_ZS(X1_L_val_sym, P_A_val_sym), is_local_AS(X2_L_val_sym, P_B_val_sym)),
        And(is_local_AS(X1_L_val_sym, P_B_val_sym), is_local_ZS(X2_L_val_sym, P_A_val_sym)),
        And(is_local_DFI(X1_L_val_sym, P_A_val_sym, P_B_val_sym), 
            is_local_DFI(X2_L_val_sym, P_A_val_sym, P_B_val_sym), 
            Equals(X1_L_val_sym, X2_L_val_sym)))

def determine_effective_canonical_omega_complex(S_val_sym: FNode) -> FNode:
    """ Determines Omega_eff_C based on local span S.
        S=1 -> Omega_eff_C=1
        S=2 -> Omega_eff_C=2
        S>=3 -> Omega_eff_C=COMPLEX_CANONICAL_OMEGA_SMT (e.g., 7)
    """
    return Ite(Equals(S_val_sym, Int(1)), Int(1),
           Ite(Equals(S_val_sym, Int(2)), Int(2),
                                           COMPLEX_CANONICAL_OMEGA_SMT)) 

def map_local_to_complex_adaptive_archetype_input_repr(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, # S_sym is local span
    Omega_eff_C_sym: FNode, # Effective Omega for the canonical archetype (1, 2, or COMPLEX_CANONICAL_OMEGA_SMT)
    arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    arch_repr = create_intensity_representation(arch_name_prefix)
    
    is_L_ZS_cond = is_local_ZS(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS(Local_val_sym, PB_sym)
    is_L_DFI_cond = is_local_DFI(Local_val_sym, PA_sym, PB_sym)

    kind_assertions = [arch_repr["constraints"]]
    kind_assertions.append(Implies(is_L_ZS_cond, And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_L_AS_cond, And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_L_DFI_cond, 
        Ite(Equals(Omega_eff_C_sym, Int(1)), # If local DFI exists (S>=2) but maps to Omega_eff_C=1 (S=1 case)
            And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"])), # Map to Canon AS
            And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"])  # Standard DFI -> Canon Fp
        )))
    
    val_assertions = [Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym))]

    # Canonical Fp value mapping:
    # val_for_canon_dfi is Local_val_sym - PA_sym, which is in range [1, S_sym-1]
    val_for_canon_dfi = Local_val_sym - PA_sym

    # If Omega_eff_C_sym = 1, arch_repr["is_finite"] is false.
    # If Omega_eff_C_sym = 2, Canon Fp val is 1. (Any local DFI maps to Canon Fp(1))
    val_if_omega_eff_is_2 = Int(1)
    
    # If Omega_eff_C_sym = COMPLEX_CANONICAL_OMEGA_SMT (e.g., 7)
    # Map local DFI [1, S_sym-1] to canonical DFI [1, COMPLEX_CANONICAL_OMEGA_SMT-1]
    # Simple mapping: map P_A+k to Fp_C(k), but cap at Omega_eff_C_sym-1
    # Example: if Omega_eff_C_sym=7, canonical DFI is {1,2,3,4,5,6}
    # If local DFI val (relative to PA) is k, map to min(k, Omega_eff_C_sym - 1)
    # Ensure result is > 0. Since val_for_canon_dfi is >=1, min will be >=1.
    val_if_omega_eff_is_complex = Ite(val_for_canon_dfi >= Omega_eff_C_sym, # Should be val_for_canon_dfi >= (Omega_eff_C_sym -1) effectively
                                        Omega_eff_C_sym - Int(1), # Cap at max DFI_C
                                        val_for_canon_dfi) # Use direct translated value if smaller
    # Ensure it's at least 1 if it's finite and Omega_eff_C > 1
    val_if_omega_eff_is_complex_gt_0 = Ite(val_if_omega_eff_is_complex < Int(1), Int(1), val_if_omega_eff_is_complex)


    val_assertions.append(
        Implies(arch_repr["is_finite"], 
            Ite(Equals(Omega_eff_C_sym, Int(1)), FALSE(), 
            Ite(Equals(Omega_eff_C_sym, Int(2)), Equals(arch_repr["val"], val_if_omega_eff_is_2),
                Equals(arch_repr["val"], val_if_omega_eff_is_complex_gt_0 ) # For Omega_eff_C = COMPLEX_CANONICAL_OMEGA_SMT
            )))
    )
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))
    
    return arch_repr, kind_assertions + val_assertions

def map_complex_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode 
) -> FNode:
    # Default for Fp_C from Omega_eff_C=1 (should not happen)
    val_from_fp_if_omega_eff_is_1 = PB_sym 
    
    # For Fp_C from Omega_eff_C=2 (Arch_Res_Repr.val must be 1)
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))

    # For Fp_C from Omega_eff_C=COMPLEX_CANONICAL_OMEGA_SMT (e.g. 7)
    # Arch_Res_Repr.val is in [1, COMPLEX_CANONICAL_OMEGA_SMT-1]
    # Map back: PA_sym + Arch_Res_Repr.val. Cap at PB_sym-1 if S_sym is small.
    potential_local_dfi_val = PA_sym + Arch_Res_Repr["val"]
    val_from_fp_if_omega_eff_is_complex = Ite(potential_local_dfi_val >= PB_sym,
                                              PB_sym - Int(1), # Cap at last local DFI step
                                              potential_local_dfi_val)
    # Ensure result is > PA_sym if S_sym > 1, otherwise map to PB_sym if S_sym=1 (no DFI)
    val_from_fp_if_omega_eff_is_complex_final = Ite(Equals(S_sym, Int(1)), PB_sym,
                                                 Ite(val_from_fp_if_omega_eff_is_complex <= PA_sym, # Should not happen if Arch_Res_Repr.val > 0
                                                     PA_sym + Int(1), # Smallest DFI
                                                     val_from_fp_if_omega_eff_is_complex))


    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                    Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                        val_from_fp_if_omega_eff_is_complex_final))

    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
               fp_result_val 
           ))

def define_local_op_complex_adaptive_result(
    op_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    S_val_sym = P_B_val_sym - P_A_val_sym
    Omega_eff_C_sym = determine_effective_canonical_omega_complex(S_val_sym)

    X_canon_repr, x_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_xc")
    defining_assertions_for_local_op.extend(x_canon_assertions)
    Y_canon_repr, y_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_yc")
    defining_assertions_for_local_op.extend(y_canon_assertions)

    Res_canon_repr = op_canonical_result_definer(X_canon_repr, Y_canon_repr, f"{result_name_prefix_local}_resc", Omega_eff_C_sym)
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])

    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_complex_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym)
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))
    debug_info = {"X_canon_repr_dbg": X_canon_repr, "Y_canon_repr_dbg": Y_canon_repr,
                  "Res_canon_repr_dbg": Res_canon_repr, "Omega_eff_C_sym_dbg": Omega_eff_C_sym,
                  "S_val_sym_dbg": S_val_sym, "parent_dict_name_for_debug": result_name_prefix_local }
    return {"val_L_sym": Res_L_val_sym, "defining_assertions": defining_assertions_for_local_op, "debug_info": debug_info}

# --- Generic Property Prover (Copied and enhanced) ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True, 
                                 op_result_dicts_for_debug: List[Dict[str,Any]] = []):
    # ... (Same as in AVC_Adaptive_Refined_Test.py)
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
                print("  DEBUG Canonical Mappings in Counterexample:")
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
                            for repr_key in ["X_canon_repr_dbg", "Y_canon_repr_dbg", "Res_canon_repr_dbg"]:
                                repr_dict = debug_info.get(repr_key)
                                if repr_dict and isinstance(repr_dict, dict) and "name" in repr_dict:
                                    val_str = f"V={solver.get_value(repr_dict['val'])}" if repr_dict['val'] in solver.get_model() else "V=?"
                                    is_z_str = f"Z={solver.get_value(repr_dict['is_zero'])}" if repr_dict['is_zero'] in solver.get_model() else "Z=?"
                                    is_a_str = f"A={solver.get_value(repr_dict['is_areo'])}" if repr_dict['is_areo'] in solver.get_model() else "A=?"
                                    is_f_str = f"F={solver.get_value(repr_dict['is_finite'])}" if repr_dict['is_finite'] in solver.get_model() else "F=?"
                                    print(f"        {repr_dict['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print(f"====== AVC Complex Fixed Adaptive Test (Canon Omega={COMPLEX_CANONICAL_OMEGA_PY} for S>=3) ======\n")

    P_A_val_sym = Symbol("PA_val_cfat", solver_INT_TYPE) # cfat for ComplexFixedAdaptiveTest
    P_B_val_sym = Symbol("PB_val_cfat", solver_INT_TYPE)
    
    La_val_sym = Symbol("La_val_cfat", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val_cfat", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val_cfat", solver_INT_TYPE)

    Li1_val_sym = Symbol("Li1_val_cfat", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val_cfat", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val_cfat", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val_cfat", solver_INT_TYPE)
    
    # Symbolic integer values for DFI Haven tests
    val_La_dfi_sym = Symbol("val_La_dfi_cfat", solver_INT_TYPE)
    val_Lb_dfi_sym = Symbol("val_Lb_dfi_cfat", solver_INT_TYPE)
    val_Lc_dfi_sym = Symbol("val_Lc_dfi_cfat", solver_INT_TYPE)


    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        effective_omega_for_print = 1 if current_local_span_S_py == 1 else (2 if current_local_span_S_py == 2 else COMPLEX_CANONICAL_OMEGA_PY)
        print(f"\n\n===== LOCAL SPAN S = {current_local_span_S_py} (Maps to Eff. Canon. Omega={effective_omega_for_print}) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) 

        # --- L1_CFAT: Well-Definedness ---
        print(f"--- Test L1_CFAT (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym)); s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym)); s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))
        premise_L1CFAT = And(avc_equiv_local(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym), avc_equiv_local(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        op_L1CFAT_add_r1 = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1CFAT_add_r1")
        op_L1CFAT_add_r2 = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1CFAT_add_r2")
        conc_L1CFAT_add = avc_equiv_local(op_L1CFAT_add_r1["val_L_sym"], op_L1CFAT_add_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.1CFAT Add respects avc_equiv_local (S={current_local_span_S_py})", [premise_L1CFAT] + op_L1CFAT_add_r1["defining_assertions"] + op_L1CFAT_add_r2["defining_assertions"], conc_L1CFAT_add, model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L1CFAT_add_r1["val_L_sym"],op_L1CFAT_add_r2["val_L_sym"]], op_result_dicts_for_debug=[op_L1CFAT_add_r1, op_L1CFAT_add_r2])
        op_L1CFAT_mul_r1 = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1CFAT_mul_r1")
        op_L1CFAT_mul_r2 = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1CFAT_mul_r2")
        conc_L1CFAT_mul = avc_equiv_local(op_L1CFAT_mul_r1["val_L_sym"], op_L1CFAT_mul_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.2CFAT Mul respects avc_equiv_local (S={current_local_span_S_py})", [premise_L1CFAT] + op_L1CFAT_mul_r1["defining_assertions"] + op_L1CFAT_mul_r2["defining_assertions"], conc_L1CFAT_mul, model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L1CFAT_mul_r1["val_L_sym"],op_L1CFAT_mul_r2["val_L_sym"]], op_result_dicts_for_debug=[op_L1CFAT_mul_r1, op_L1CFAT_mul_r2])
        s.pop()

        general_setup_L_abc = [ And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym),
                                And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym),
                                And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym) ]

        # --- L2_CFAT: Associativity of Add ---
        print(f"\n--- Test L2_CFAT Add Assoc (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        sum_ab_L2CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2CFAT_sum_ab")
        lhs_L2CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, sum_ab_L2CFAT["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2CFAT_lhs")
        sum_bc_L2CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2CFAT_sum_bc")
        rhs_L2CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, La_val_sym, sum_bc_L2CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym, "L2CFAT_rhs")
        all_L2CFAT_asserts = sum_ab_L2CFAT["defining_assertions"] + lhs_L2CFAT["defining_assertions"] + sum_bc_L2CFAT["defining_assertions"] + rhs_L2CFAT["defining_assertions"]
        prove_or_find_counterexample(s, f"L2CFAT Add Assoc (S={current_local_span_S_py})", all_L2CFAT_asserts, avc_equiv_local(lhs_L2CFAT["val_L_sym"], rhs_L2CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,sum_ab_L2CFAT["val_L_sym"],lhs_L2CFAT["val_L_sym"],sum_bc_L2CFAT["val_L_sym"],rhs_L2CFAT["val_L_sym"]], op_result_dicts_for_debug=[sum_ab_L2CFAT, lhs_L2CFAT, sum_bc_L2CFAT, rhs_L2CFAT])
        s.pop()
        
        # --- L3_CFAT: Associativity of Mul ---
        print(f"\n--- Test L3_CFAT Mul Assoc (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        prod_ab_L3CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3CFAT_prod_ab")
        lhs_mul_L3CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, prod_ab_L3CFAT["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3CFAT_lhs_mul")
        prod_bc_L3CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3CFAT_prod_bc")
        rhs_mul_L3CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, prod_bc_L3CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym, "L3CFAT_rhs_mul")
        all_L3CFAT_asserts = prod_ab_L3CFAT["defining_assertions"] + lhs_mul_L3CFAT["defining_assertions"] + prod_bc_L3CFAT["defining_assertions"] + rhs_mul_L3CFAT["defining_assertions"]
        prove_or_find_counterexample(s, f"L3CFAT Mul Assoc (S={current_local_span_S_py})", all_L3CFAT_asserts, avc_equiv_local(lhs_mul_L3CFAT["val_L_sym"], rhs_mul_L3CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym], op_result_dicts_for_debug=[prod_ab_L3CFAT, lhs_mul_L3CFAT, prod_bc_L3CFAT, rhs_mul_L3CFAT])
        s.pop()

        # --- L4_CFAT: Distributivity ---
        print(f"\n--- Test L4_CFAT Distributivity (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        sum_bc_L4CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L4CFAT_sum_bc")
        lhs_dist_L4CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, sum_bc_L4CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym, "L4CFAT_lhs_dist")
        prod_ab_L4CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4CFAT_prod_ab")
        prod_ac_L4CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L4CFAT_prod_ac")
        rhs_dist_L4CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, prod_ab_L4CFAT["val_L_sym"], prod_ac_L4CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym, "L4CFAT_rhs_dist")
        all_L4CFAT_asserts = sum_bc_L4CFAT["defining_assertions"] + lhs_dist_L4CFAT["defining_assertions"] + prod_ab_L4CFAT["defining_assertions"] + prod_ac_L4CFAT["defining_assertions"] + rhs_dist_L4CFAT["defining_assertions"]
        op_results_L4CFAT_debug = [sum_bc_L4CFAT, lhs_dist_L4CFAT, prod_ab_L4CFAT, prod_ac_L4CFAT, rhs_dist_L4CFAT]
        prove_or_find_counterexample(s, f"L4CFAT Distributivity (S={current_local_span_S_py})", all_L4CFAT_asserts, avc_equiv_local(lhs_dist_L4CFAT["val_L_sym"], rhs_dist_L4CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,sum_bc_L4CFAT["val_L_sym"],lhs_dist_L4CFAT["val_L_sym"],prod_ab_L4CFAT["val_L_sym"],prod_ac_L4CFAT["val_L_sym"],rhs_dist_L4CFAT["val_L_sym"]], op_result_dicts_for_debug=op_results_L4CFAT_debug)
        s.pop()
        
        # --- L5_CFAT: Additive Cancellation ---
        print(f"\n--- Test L5_CFAT Additive Cancellation (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        add_ab_L5CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5CFAT_add_ab")
        add_ac_L5CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L5CFAT_add_ac")
        premise_L5CFAT = And(avc_equiv_local(add_ab_L5CFAT["val_L_sym"], add_ac_L5CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym))
        conclusion_L5CFAT = avc_equiv_local(Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym)
        all_L5CFAT_asserts = add_ab_L5CFAT["defining_assertions"] + add_ac_L5CFAT["defining_assertions"]
        prove_or_find_counterexample(s, f"L5CFAT Additive Cancellation (S={current_local_span_S_py})", [premise_L5CFAT] + all_L5CFAT_asserts, conclusion_L5CFAT, model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,add_ab_L5CFAT["val_L_sym"],add_ac_L5CFAT["val_L_sym"]], op_result_dicts_for_debug=[add_ab_L5CFAT, add_ac_L5CFAT])
        s.pop()

        # --- L6_CFAT: Additive Idempotence ---
        print(f"\n--- Test L6_CFAT Additive Idempotence (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        add_aa_L6CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, La_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L6CFAT_add_aa")
        prove_or_find_counterexample(s, f"L6CFAT Additive Idempotence La+La ~ La (S={current_local_span_S_py})", add_aa_L6CFAT["defining_assertions"], avc_equiv_local(add_aa_L6CFAT["val_L_sym"], La_val_sym, P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,add_aa_L6CFAT["val_L_sym"]], op_result_dicts_for_debug=[add_aa_L6CFAT])
        s.pop()
        
        # --- L7_CFAT: Multiplicative Cancellation ---
        print(f"\n--- Test L7_CFAT Multiplicative Cancellation (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        mul_ab_L7CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L7CFAT_mul_ab")
        mul_ac_L7CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L7CFAT_mul_ac")
        premise_L7CFAT = And(avc_equiv_local(mul_ab_L7CFAT["val_L_sym"], mul_ac_L7CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym), Not(is_local_ZS(La_val_sym, P_A_val_sym)))
        conclusion_L7CFAT = avc_equiv_local(Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym)
        all_L7CFAT_asserts = mul_ab_L7CFAT["defining_assertions"] + mul_ac_L7CFAT["defining_assertions"]
        prove_or_find_counterexample(s, f"L7CFAT Multiplicative Cancellation (S={current_local_span_S_py})", [premise_L7CFAT] + all_L7CFAT_asserts, conclusion_L7CFAT, model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,mul_ab_L7CFAT["val_L_sym"],mul_ac_L7CFAT["val_L_sym"]], op_result_dicts_for_debug=[mul_ab_L7CFAT, mul_ac_L7CFAT])
        s.pop()

        # --- L8_CFAT: Multiplicative Idempotence ---
        print(f"\n--- Test L8_CFAT Multiplicative Idempotence (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        mul_aa_L8CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L8CFAT_mul_aa")
        prove_or_find_counterexample(s, f"L8CFAT Multiplicative Idempotence La*La ~ La (S={current_local_span_S_py})", mul_aa_L8CFAT["defining_assertions"], avc_equiv_local(mul_aa_L8CFAT["val_L_sym"], La_val_sym, P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,mul_aa_L8CFAT["val_L_sym"]], op_result_dicts_for_debug=[mul_aa_L8CFAT])
        s.pop()

        # DFI Haven Setup: Constrain La, Lb, Lc to be symbolic local DFI values
        dfi_haven_setup_constraints = [
            is_local_DFI(La_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI(Lb_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI(Lc_val_sym, P_A_val_sym, P_B_val_sym)
        ]

        # --- L9_CFAT_DFI_Haven_Assoc_Add ---
        print(f"\n--- Test L9_CFAT DFI Haven Add Assoc (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(dfi_haven_setup_constraints)
        sum_ab_L9CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L9CFAT_sum_ab")
        lhs_L9CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, sum_ab_L9CFAT["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L9CFAT_lhs")
        sum_bc_L9CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L9CFAT_sum_bc")
        rhs_L9CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, La_val_sym, sum_bc_L9CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym, "L9CFAT_rhs")
        all_L9CFAT_defs = sum_ab_L9CFAT["defining_assertions"] + lhs_L9CFAT["defining_assertions"] + sum_bc_L9CFAT["defining_assertions"] + rhs_L9CFAT["defining_assertions"]
        dfi_haven_conds_L9CFAT = [ 
            is_local_DFI(sum_ab_L9CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym), is_local_DFI(lhs_L9CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(sum_bc_L9CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym), is_local_DFI(rhs_L9CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym)
        ]
        prove_or_find_counterexample(s, f"L9CFAT Add Assoc (DFI Haven, S={current_local_span_S_py})", all_L9CFAT_defs + dfi_haven_conds_L9CFAT, 
                                     avc_equiv_local(lhs_L9CFAT["val_L_sym"], rhs_L9CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,sum_ab_L9CFAT["val_L_sym"],lhs_L9CFAT["val_L_sym"],sum_bc_L9CFAT["val_L_sym"],rhs_L9CFAT["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_L9CFAT, lhs_L9CFAT, sum_bc_L9CFAT, rhs_L9CFAT])
        s.pop()

        # --- L10_CFAT_DFI_Haven_Dist ---
        print(f"\n--- Test L10_CFAT DFI Haven Distributivity (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(dfi_haven_setup_constraints)
        sum_bc_L10CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L10CFAT_sum_bc")
        lhs_dist_L10CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, sum_bc_L10CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym, "L10CFAT_lhs_dist")
        prod_ab_L10CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L10CFAT_prod_ab")
        prod_ac_L10CFAT = define_local_op_complex_adaptive_result(define_raw_mul_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L10CFAT_prod_ac")
        rhs_dist_L10CFAT = define_local_op_complex_adaptive_result(define_smart_raw_add_canonical_result, prod_ab_L10CFAT["val_L_sym"], prod_ac_L10CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym, "L10CFAT_rhs_dist")
        all_L10CFAT_defs = sum_bc_L10CFAT["defining_assertions"] + lhs_dist_L10CFAT["defining_assertions"] + prod_ab_L10CFAT["defining_assertions"] + prod_ac_L10CFAT["defining_assertions"] + rhs_dist_L10CFAT["defining_assertions"]
        dfi_haven_conds_L10CFAT = [
            is_local_DFI(sum_bc_L10CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym), is_local_DFI(lhs_dist_L10CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(prod_ab_L10CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym), is_local_DFI(prod_ac_L10CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(rhs_dist_L10CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym)
        ]
        op_results_L10CFAT_debug = [sum_bc_L10CFAT, lhs_dist_L10CFAT, prod_ab_L10CFAT, prod_ac_L10CFAT, rhs_dist_L10CFAT]
        prove_or_find_counterexample(s, f"L10CFAT Distributivity (DFI Haven, S={current_local_span_S_py})", all_L10CFAT_defs + dfi_haven_conds_L10CFAT, 
                                     avc_equiv_local(lhs_dist_L10CFAT["val_L_sym"], rhs_dist_L10CFAT["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,sum_bc_L10CFAT["val_L_sym"],lhs_dist_L10CFAT["val_L_sym"],prod_ab_L10CFAT["val_L_sym"],prod_ac_L10CFAT["val_L_sym"],rhs_dist_L10CFAT["val_L_sym"]],
                                     op_result_dicts_for_debug=op_results_L10CFAT_debug)
        s.pop()
        
        del s 
        print("-" * 80)

    print(f"\n====== AVC Complex Fixed Adaptive Test (Canon Omega={COMPLEX_CANONICAL_OMEGA_PY} for S>=3) Complete ======")

