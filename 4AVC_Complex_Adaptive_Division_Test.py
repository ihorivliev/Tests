from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7, 10] 
DEFAULT_P_A_OFFSET = 0 

# Effective Canonical Omega for Complex Fixed Adaptive Model
COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY = 7

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
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), 
        Or( 
            And(i1["is_zero"], 
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), 
            And(i1["is_areo"],  
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(i1["is_finite"], 
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), 
                    rem_sym >= Int(0), 
                    rem_sym < i2["val"]), 
                
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)), 
                    Ite(q_sym >= current_omega_eff_c_smt, 
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym)) 
                    ), 
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]))
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

# --- Phase 3: Local Frame, Complex Adaptive Omega, and Mappings ---
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

def determine_effective_canonical_omega_complex(S_val_sym: FNode, complex_omega_smt: FNode) -> FNode:
    """ S=1 -> Omega_eff_C=1; S=2 -> Omega_eff_C=2; S>=3 -> Omega_eff_C=complex_omega_smt (e.g., 7) """
    return Ite(Equals(S_val_sym, Int(1)), Int(1),
           Ite(Equals(S_val_sym, Int(2)), Int(2),
                                           complex_omega_smt)) 

def map_local_to_complex_adaptive_archetype_input_repr(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode, complex_omega_py_val: int, # Python value of complex_omega_smt for logic
    arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    arch_repr = create_intensity_representation(arch_name_prefix)
    
    is_L_ZS_cond = is_local_ZS_val(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS_val(Local_val_sym, PB_sym)
    is_L_DFI_cond = is_local_DFI_val(Local_val_sym, PA_sym, PB_sym)

    kind_assertions = [arch_repr["constraints"]]
    kind_assertions.append(Implies(is_L_ZS_cond, And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_L_AS_cond, And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))))
    kind_assertions.append(Implies(is_L_DFI_cond, And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"])))
    
    val_assertions = [Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym))]

    # Canonical Fp value mapping:
    # If Omega_eff_C is 1 (S_sym=1), arch_repr cannot be finite if Local_val was a valid DFI.
    # If Omega_eff_C is 2 (S_sym=2), the single Local DFI (PA+1) maps to Fp_C(1).
    # If Omega_eff_C is complex_omega_py_val (e.g., 7) (S_sym>=3):
    #   Map local DFI PA+k to Fp_C(min(k, complex_omega_py_val - 1)), ensuring val is at least 1.
    k_L_val = Local_val_sym - PA_sym # Relative local DFI value (1, 2, ..., S-1)
    
    # Value if Omega_eff_C is 2 (DFI_C = {1})
    val_if_omega_eff_is_2 = Int(1)
    
    # Value if Omega_eff_C is complex_omega_py_val (e.g., 7)
    # Map k_L to min(k_L, complex_omega_py_val - 1). Since k_L is always >= 1 for DFI.
    # complex_omega_py_val - 1 is the max DFI value in the complex archetype.
    # Example: if complex_omega_py_val = 7, max DFI_C val is 6.
    # So, local DFI k_L maps to canonical min(k_L, 6).
    # This requires k_L to be an SMT expression here.
    # This means k_L can be 1, 2, 3, 4, 5, 6.
    # If k_L (from local) is > 6, it still maps to 6.
    val_if_omega_eff_is_complex = k_L_val # Default to k_L
    # Apply capping if k_L > (complex_omega_py_val - 1)
    # This needs to be done carefully with Ite if complex_omega_py_val is symbolic, but it's Py for now.
    # Let's assume Omega_eff_C_sym (the SMT version of complex_omega_py_val for S>=3) is used.
    # And k_L_val is already an SMT expression.
    # So canon_val = Ite(k_L_val >= Omega_eff_C_sym, Omega_eff_C_sym - Int(1), k_L_val) - but this is wrong for Fp.
    # canon_val should be capped at Omega_eff_C_sym - 1.
    # And k_L_val > 0.
    # A simple way is to use python int for cap, assuming Omega_eff_C_sym IS complex_omega_smt for S>=3.
    cap_val_for_complex_dfi = Int(complex_omega_py_val - 1)
    val_if_omega_eff_is_complex_mapped = Ite(k_L_val > cap_val_for_complex_dfi, 
                                             cap_val_for_complex_dfi, 
                                             Ite(k_L_val <= Int(0), Int(1), k_L_val)) # ensure positive, k_L can't be 0 if DFI

    val_assertions.append(
        Implies(arch_repr["is_finite"], 
            Ite(Equals(Omega_eff_C_sym, Int(1)), 
                FALSE(), # Should be unreachable if arch_repr is finite & S=1 (no local DFI)
            Ite(Equals(Omega_eff_C_sym, Int(2)), 
                Equals(arch_repr["val"], val_if_omega_eff_is_2),
                # Else Omega_eff_C_sym is complex_omega_smt
                Equals(arch_repr["val"], val_if_omega_eff_is_complex_mapped) 
            ))
        )
    )
    val_assertions.append(Implies(arch_repr["is_finite"], And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))

    return arch_repr, kind_assertions + val_assertions

def map_complex_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode, complex_omega_py_val: int
) -> FNode:
    # Map Fp_C result back to local DFI
    # If Omega_eff_C was 1: Arch_Res_Repr cannot be Fp. Fallback to P_B.
    val_from_fp_if_omega_eff_is_1 = PB_sym 
    
    # If Omega_eff_C was 2 (Arch_Res_Repr.val must be 1):
    #   If S_sym (local span) is 1: map to P_B (no local DFI).
    #   If S_sym >= 2: map to PA_sym + 1.
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))

    # If Omega_eff_C was complex_omega_py_val (e.g. 7) (Arch_Res_Repr.val is in [1, complex_omega_py_val-1]):
    #   The canonical value Arch_Res_Repr["val"] is k_C.
    #   We need to map k_C back to a local DFI step PA_sym + k_L.
    #   The mapping was PA_sym + k_L -> Fp_C(min(k_L, complex_omega_py_val-1)).
    #   This implies k_C = min(k_L, complex_omega_py_val-1).
    #   If k_C < complex_omega_py_val-1, then k_L = k_C. So local value is PA_sym + k_C.
    #   If k_C = complex_omega_py_val-1, k_L could be complex_omega_py_val-1 or anything larger up to S_sym-1.
    #   For simplicity in reverse mapping, if k_C = complex_omega_py_val-1, map it to PB_sym - 1 (last local DFI if S_sym > 1).
    #   If k_C < complex_omega_py_val-1, map to PA_sym + k_C.
    #   This needs to ensure the result is within (PA_sym, PB_sym).
    
    # Simplified reverse mapping for Fp from complex archetype:
    # If S_sym=1, map to PB_sym (no local DFI).
    # If S_sym=2, local DFI is PA+1.
    #    If Arch_Res_Repr["val"] (from complex, e.g. Omega=7) is 1, map to PA+1.
    #    If Arch_Res_Repr["val"] > 1, map to PB_sym (effectively AS_L, as PA+1 is the only DFI_L).
    # If S_sym >= 3:
    #    If Arch_Res_Repr["val"] == 1, map to PA_sym + 1.
    #    If Arch_Res_Repr["val"] == (complex_omega_py_val - 1) AND (complex_omega_py_val -1) < S_sym: map to PB_sym -1.
    #    Else (e.g. Arch_Res_Repr["val"] is some intermediate value like 2,3,4,5 for Omega=7) map to PA_sym + Arch_Res_Repr["val"],
    #        but ensure this doesn't exceed PB_sym-1.
    # This mapping needs to be robust. Let's use a simpler version from AVC_Adaptive_Refined_Test.py for now.
    # That one was: if Omega_eff_C=3 (val is 1 or 2): if S=1->PB; if S=2 (val=1 -> PA+1, val=2 -> PB); if S>=3 (val=1->PA+1, val=2->PB-1)
    # We are adapting for Omega_eff_C=7, Arch_Res_Repr["val"] in [1..6]
    val_from_fp_if_omega_eff_is_complex_final = Arch_Res_Repr["val"] # This is v_canonical
    # Map v_canonical to local offset:
    # Simple: PA_sym + v_canonical, but must be < PB_sym. If not, becomes PB_sym.
    # This ensures it maps to a valid local DFI if possible, or ASL.
    # More careful:
    # If S_sym = 1: map to PB_sym
    # If S_sym = 2: local DFI is PA+1. If v_canonical=1, map to PA+1. If v_canonical > 1 (e.g. 2 to 6 from Omega=7), map to PB_sym.
    # If S_sym >= 3: map PA_sym + v_canonical, as long as PA_sym + v_canonical < PB_sym. Otherwise PB_sym.
    # This is tricky. Let's use the mapping from AVC_Complex_Fixed_Adaptive_Test_Hard (previous analysis memo's description)
    # map_complex_adaptive_archetype_result_to_local(Arch_Res_Repr, PA_sym, PB_sym, S_sym, Omega_eff_C_sym, complex_omega_py_val)
    # If Arch_Res_Repr['val'] (v_C) maps to something >= S_sym, then result is PB_sym. Else PA_sym + v_C.
    # No, the provided mapping logic in AVC_Complex_Fixed_Adaptive_Test was:
    # potential_local_dfi_val = PA_sym + Arch_Res_Repr['val']
    # mapped_val = Ite(potential_local_dfi_val >= PB_sym, PB_sym - Int(1), potential_local_dfi_val)
    # result = Ite(mapped_val <= PA_sym, PA_sym + Int(1), mapped_val)
    # This needs to be adapted for current Omega_eff_C_sym structure
    
    val_from_fp_if_omega_eff_is_complex = Ite(S_sym <= Int(1), PB_sym, # No DFI if S=1
        Ite(Equals(S_sym, Int(2)), # Local DFI is {PA+1}
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym), # From Omega=7, if val_C=1 -> PA+1; if val_C>1 -> PB
            # Else S_sym >=3. Max local DFI is PB-1. Map canonical val back.
            # If Arch_Res_Repr["val"] from Omega=7 can be directly represented locally (i.e., PA + val_C < PB)
            Ite(PA_sym + Arch_Res_Repr["val"] < PB_sym, PA_sym + Arch_Res_Repr["val"], PB_sym - Int(1)) # Cap at PB-1
        )
    )

    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                    Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                         val_from_fp_if_omega_eff_is_complex))

    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
               fp_result_val 
           ))

def define_local_op_complex_adaptive_archetype_result(
    op_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    
    S_val_sym = P_B_val_sym - P_A_val_sym
    complex_omega_smt = Int(COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY)
    Omega_eff_C_sym = determine_effective_canonical_omega_complex(S_val_sym, complex_omega_smt)

    X_canon_repr, x_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, f"{result_name_prefix_local}_xc"
    )
    defining_assertions_for_local_op.extend(x_canon_assertions)

    Y_canon_repr, y_canon_assertions = map_local_to_complex_adaptive_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY, f"{result_name_prefix_local}_yc"
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
    local_result_value_formula = map_complex_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY
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
                                (None, "Res_canon_repr_dbg") 
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
    print("====== AVC Complex Adaptive Division Properties Test ======\n")

    P_A_val_sym = Symbol("PA_val_cadiv", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val_cadiv", solver_INT_TYPE)
    
    La_val_sym = Symbol("La_val_cadiv", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val_cadiv", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val_cadiv", solver_INT_TYPE)

    Li1_val_sym = Symbol("Li1_val_cadiv", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val_cadiv", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val_cadiv", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val_cadiv", solver_INT_TYPE)

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        complex_omega_smt = Int(COMPLEX_CANONICAL_OMEGA_FOR_S_GE_3_PY)
        
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S_py} (Complex Adaptive Omega for Division) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) 

        # --- L1-Div-CA: Well-Definedness of raw_div_local_complex_adaptive ---
        print(f"--- Test L1-Div-CA (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))
        premise_L1DivCA = And(avc_equiv_local_val(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym),
                              avc_equiv_local_val(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        
        op_L1DivCA_r1 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1DivCA_r1")
        op_L1DivCA_r2 = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1DivCA_r2")
        conc_L1DivCA = avc_equiv_local_val(op_L1DivCA_r1["val_L_sym"], op_L1DivCA_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1-Div-CA raw_div_local_complex_adaptive respects avc_equiv_local (S={current_local_span_S_py})",
                                     [premise_L1DivCA] + op_L1DivCA_r1["defining_assertions"] + op_L1DivCA_r2["defining_assertions"], conc_L1DivCA,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L1DivCA_r1["val_L_sym"],op_L1DivCA_r2["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L1DivCA_r1, op_L1DivCA_r2])
        s.pop()

        general_L_abc_setup = [
            And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym),
            And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym),
            And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym)
        ]

        # --- L2-Div-CA: Commutativity of raw_div_local_complex_adaptive ---
        print(f"\n--- Test L2-Div-CA Commutativity (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(general_L_abc_setup)
        op_ab_L2DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2DivCA_ab")
        op_ba_L2DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, Lb_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L2DivCA_ba")
        conc_L2DivCA = avc_equiv_local_val(op_ab_L2DivCA["val_L_sym"], op_ba_L2DivCA["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L2-Div-CA Commutativity (S={current_local_span_S_py})", 
                                     op_ab_L2DivCA["defining_assertions"] + op_ba_L2DivCA["defining_assertions"], conc_L2DivCA,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,op_ab_L2DivCA["val_L_sym"],op_ba_L2DivCA["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_ab_L2DivCA, op_ba_L2DivCA])
        s.pop()

        # --- L3-Div-CA: Associativity of raw_div_local_complex_adaptive ---
        print(f"\n--- Test L3-Div-CA Associativity (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertions(general_L_abc_setup)
        div_ab_L3DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3DivCA_ab")
        lhs_L3DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, div_ab_L3DivCA["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3DivCA_lhs") # Corrected Lc_val_sym
        div_bc_L3DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3DivCA_bc")
        rhs_L3DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, div_bc_L3DivCA["val_L_sym"], P_A_val_sym, P_B_val_sym, "L3DivCA_rhs")
        all_L3DivCA_asserts = div_ab_L3DivCA["defining_assertions"] + lhs_L3DivCA["defining_assertions"] + div_bc_L3DivCA["defining_assertions"] + rhs_L3DivCA["defining_assertions"]
        conc_L3DivCA = avc_equiv_local_val(lhs_L3DivCA["val_L_sym"], rhs_L3DivCA["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L3-Div-CA Associativity (S={current_local_span_S_py})", all_L3DivCA_asserts, conc_L3DivCA,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,lhs_L3DivCA["val_L_sym"],rhs_L3DivCA["val_L_sym"]], # Corrected Lc_val_sym to Lc_L_val for printing if that was the intent, or use Lc_val_sym
                                     op_result_dicts_for_debug=[div_ab_L3DivCA, lhs_L3DivCA, div_bc_L3DivCA, rhs_L3DivCA])
        s.pop()
        
        # --- L4-Div-CA: Cancellation Law 1: (La *_L Lb_DFI) /_L Lb_DFI ~_L La ---
        print(f"\n--- Test L4-Div-CA Cancellation 1 (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)) 
        s.add_assertion(is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym))    
        
        prod_ab_L4DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4DivCA_prod_ab")
        res_div_L4DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, prod_ab_L4DivCA["val_L_sym"], Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4DivCA_res_div")
        conc_L4DivCA = avc_equiv_local_val(res_div_L4DivCA["val_L_sym"], La_val_sym, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L4-Div-CA (La*_L Lb_DFI)/_L Lb_DFI ~_L La (S={current_local_span_S_py})",
                                     prod_ab_L4DivCA["defining_assertions"] + res_div_L4DivCA["defining_assertions"], conc_L4DivCA,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,prod_ab_L4DivCA["val_L_sym"],res_div_L4DivCA["val_L_sym"]],
                                     op_result_dicts_for_debug=[prod_ab_L4DivCA, res_div_L4DivCA])
        s.pop()

        # --- L5-Div-CA: Cancellation Law 2: (La /_L Lb_DFI) *_L Lb_DFI ~_L La (if La/_L Lb_DFI is DFI_L) ---
        print(f"\n--- Test L5-Div-CA Cancellation 2 (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)) 
        s.add_assertion(is_local_DFI_val(Lb_val_sym, P_A_val_sym, P_B_val_sym))    
        
        div_ab_L5DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5DivCA_div_ab")
        s.add_assertion(is_local_DFI_val(div_ab_L5DivCA["val_L_sym"], P_A_val_sym, P_B_val_sym))
        
        res_mul_L5DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_mul_canonical_result, div_ab_L5DivCA["val_L_sym"], Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5DivCA_res_mul")
        conc_L5DivCA = avc_equiv_local_val(res_mul_L5DivCA["val_L_sym"], La_val_sym, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L5-Div-CA (La/_L Lb_DFI)*_L Lb_DFI ~_L La (if Res DFI_L) (S={current_local_span_S_py})",
                                     div_ab_L5DivCA["defining_assertions"] + res_mul_L5DivCA["defining_assertions"], conc_L5DivCA,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,div_ab_L5DivCA["val_L_sym"],res_mul_L5DivCA["val_L_sym"]],
                                     op_result_dicts_for_debug=[div_ab_L5DivCA, res_mul_L5DivCA])
        s.pop()

        # --- L6-Div-CA: Division by Local Poles ---
        print(f"\n--- Test L6-Div-CA Division by Poles (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)) 

        res_div_zs_L6DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, P_A_val_sym, P_A_val_sym, P_B_val_sym, "L6DivCA_zs")
        conc_L61DivCA = is_local_AS_val(res_div_zs_L6DivCA["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L6.1-Div-CA La/_L ZS_L ~_L AS_L (S={current_local_span_S_py})",
                                     res_div_zs_L6DivCA["defining_assertions"], conc_L61DivCA,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,res_div_zs_L6DivCA["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_div_zs_L6DivCA])
        s.pop()

        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        res_div_as_L6DivCA = define_local_op_complex_adaptive_archetype_result(define_raw_div_canonical_result, La_val_sym, P_B_val_sym, P_A_val_sym, P_B_val_sym, "L6DivCA_as")
        conc_L62DivCA = is_local_AS_val(res_div_as_L6DivCA["val_L_sym"], P_B_val_sym)
        prove_or_find_counterexample(s, f"L6.2-Div-CA La/_L AS_L ~_L AS_L (S={current_local_span_S_py})",
                                     res_div_as_L6DivCA["defining_assertions"], conc_L62DivCA,
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,res_div_as_L6DivCA["val_L_sym"]],
                                     op_result_dicts_for_debug=[res_div_as_L6DivCA])
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC Complex Adaptive Division Properties Test Complete ======")