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

# --- Phase 3: Local Frame, Adaptive Omega, and Mappings ---

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

def determine_effective_canonical_omega(S_val_sym: FNode) -> FNode:
    """ Determines Omega_eff_C based on local span S. """
    # If S=1, Omega_eff_C=1 (ZS_C ~ AS_C, no DFI_C)
    # If S=2, Omega_eff_C=2 (DFI_C={1})
    # If S>=3, Omega_eff_C=3 (DFI_C={1,2})
    return Ite(Equals(S_val_sym, Int(1)), Int(1),
           Ite(Equals(S_val_sym, Int(2)), Int(2),
                                           Int(3))) # Assumes S_val_sym >= 1 constraint elsewhere

def map_local_to_adaptive_archetype_input_repr(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, # S_sym is PB_sym - PA_sym
    Omega_eff_C_sym: FNode, # Effective Omega for the canonical archetype
    arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    """
    Maps a local value to a state of the ADAPTIVE canonical archetype [0, Omega_eff_C_sym].
    """
    arch_repr = create_intensity_representation(arch_name_prefix)
    assertions = [arch_repr["constraints"]]

    is_L_ZS_cond = is_local_ZS(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS(Local_val_sym, PB_sym)
    
    # --- Define Canonical Kind ---
    assertions.append(
        Ite(is_L_ZS_cond, 
            And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"])), # Local ZS -> Canon ZS
            Ite(is_L_AS_cond,
                And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"])), # Local AS -> Canon AS
                And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"])  # Local DFI -> Canon Fp
            )
        )
    )
    
    # --- Define Canonical Value (val field of arch_repr) ---
    # For Canon ZS, val is unconstrained by mapping (but must be >0 if it were Fp, which it isn't).
    # For Canon AS, its value must be Omega_eff_C_sym.
    assertions.append(Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym)))

    # For Canon Fp, its value depends on the mapping from Local DFI to Canonical DFI [1, Omega_eff_C-1]
    # This mapping depends on S_sym and Omega_eff_C_sym
    
    # Canonical DFI val if Omega_eff_C_sym = 1 (no DFI, this case should not make arch_repr Fp)
    # (Handled by arch_repr["is_finite"] being false if Omega_eff_C_sym=1 and input is DFI - this needs robust handling)

    # Canonical DFI val if Omega_eff_C_sym = 2 (Canon DFI is {1})
    # Any Local DFI maps to Canon Fp(1)
    val_if_omega_eff_is_2 = Int(1)

    # Canonical DFI val if Omega_eff_C_sym = 3 (Canon DFI is {1,2})
    # Map Local DFI (P_A+k where 1 <= k < S) to Canon Fp(1) or Fp(2)
    # Simplistic mapping: P_A+1 maps to Fp_C(1). P_A+k (k>1, k<S) maps to Fp_C(2).
    # This ensures that if S>=3, both Fp_C(1) and Fp_C(2) can be targeted.
    val_if_omega_eff_is_3 = Ite(Equals(Local_val_sym, PA_sym + Int(1)), # If it's the first local DFI step
                                Int(1),
                                Int(2)  # All other local DFIs map to the "higher" canonical DFI step
                               )
    
    # Assign arch_repr["val"] for the Finite case based on Omega_eff_C_sym
    # Note: The Implies(arch_repr["is_finite"], arch_repr["val"] > Int(0)) is from create_intensity_representation
    # And Implies(arch_repr["is_finite"], arch_repr["val"] < Omega_eff_C_sym) must hold.
    
    # If Omega_eff_C is 1, arch_repr cannot be finite (DFI is empty).
    # The mapping logic for kind already handles this: if local is DFI and S=1 (so Omega_eff_C=1),
    # the DFI will still map to arch_repr["is_finite"]=True. This is a problem.
    # The kind mapping must depend on Omega_eff_C_sym for DFI.
    
    # Revised Kind Mapping for Local DFI:
    # If Local is DFI:
    #   If Omega_eff_C_sym = 1 (i.e. S_sym = 1, local DFI is empty): This input is invalid.
    #      For robustness, map invalid local DFI for S=1 to Canonical AS.
    #   Else (Omega_eff_C_sym = 2 or 3): Map to Canonical Fp.
    
    # Let's refine the kind mapping part first:
    assertions_kind = [arch_repr["constraints"]] # Start with fresh assertions for kind
    
    # Case 1: Local input is ZS
    assertions_kind.append(Implies(is_L_ZS_cond, 
        And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))))
    # Case 2: Local input is AS
    assertions_kind.append(Implies(is_L_AS_cond,
        And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))))
    
    # Case 3: Local input is DFI
    #   If S_sym (and thus Omega_eff_C_sym) is 1, there's no local DFI.
    #   If a value IS a local DFI (so S_sym must be >= 2), then map to canonical Fp.
    #   The Omega_eff_C_sym will be >=2 if S_sym >=2.
    assertions_kind.append(Implies(And(Not(is_L_ZS_cond), Not(is_L_AS_cond)), # If Local is DFI
        And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"]) # Then Canonical is Fp
    ))
    
    # Now, refine canonical value assignment for the Fp case:
    assertions_value = [
        Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym)),
        Implies(And(arch_repr["is_finite"], Equals(Omega_eff_C_sym, Int(2))), # Mapped to Fp, and Canon Arch is Omega=2 type
                Equals(arch_repr["val"], Int(1))), # Only Fp_C(1) exists
        Implies(And(arch_repr["is_finite"], Equals(Omega_eff_C_sym, Int(3))), # Mapped to Fp, and Canon Arch is Omega=3 type
                Equals(arch_repr["val"], val_if_omega_eff_is_3)), # Value is 1 or 2 based on local DFI
        # Constraint that canonical Fp value is < Omega_eff_C_sym
        Implies(arch_repr["is_finite"], arch_repr["val"] < Omega_eff_C_sym) # Also val > 0 from create_intensity
    ]

    # Replace original assertions with refined ones
    assertions = assertions_kind + assertions_value
    
    return arch_repr, assertions


def map_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], # Result from the canonical archetype operation
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, # Local frame parameters
    Omega_eff_C_sym: FNode # The Omega_eff_C used for the canonical operation
) -> FNode:
    """ Maps a result from the ADAPTIVE canonical archetype back to a local value. """
    
    # If canonical result is Fp_C(1) from Omega_eff_C=2 archetype (meaning S_sym=2)
    val_if_fp_from_omega2 = PA_sym + Int(1) # Maps to the single local DFI P_A+1

    # If canonical result is Fp_C(1) or Fp_C(2) from Omega_eff_C=3 archetype (meaning S_sym >=3)
    val_if_fp_from_omega3 = Ite(Equals(Arch_Res_Repr["val"], Int(1)),
                                PA_sym + Int(1),       # Canon Fp(1) -> Local P_A+1
                                PB_sym - Int(1)        # Canon Fp(2) -> Local P_B-1 (last DFI)
                               )
    # This PB-1 needs S_sym >= 2 to be valid DFI, and S_sym >=3 for it to be distinct from PA+1 if Omega_eff_C=3
    # We must ensure the result is sensible if S_sym is small.

    # Corrected logic for Fp mapping back:
    # If Arch_Res_Repr is Fp:
    #   If Omega_eff_C_sym was 1: This is an impossible state (no Fp in Omega=1 arch). Default to PB.
    #   If Omega_eff_C_sym was 2 (so Arch_Res_Repr.val must be 1):
    #       If S_sym (local span) is 1: map to PB_sym (no local DFI, Fp(1) acts like AS_C)
    #       If S_sym >= 2: map to PA_sym + 1
    #   If Omega_eff_C_sym was 3 (so Arch_Res_Repr.val is 1 or 2):
    #       If S_sym is 1: map to PB_sym
    #       If S_sym is 2: (local DFI is PA+1)
    #           If Arch_Res_Repr.val is 1, map to PA_sym + 1
    #           If Arch_Res_Repr.val is 2, map to PB_sym (effectively AS_L)
    #       If S_sym >= 3:
    #           If Arch_Res_Repr.val is 1, map to PA_sym + 1
    #           If Arch_Res_Repr.val is 2, map to PB_sym - 1
    
    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), PB_sym, # Should not happen for Fp result
                    Ite(Equals(Omega_eff_C_sym, Int(2)), # Canon.val must be 1
                        Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1)),
                        # Else Omega_eff_C_sym is 3 (Canon.val is 1 or 2)
                        Ite(Equals(S_sym, Int(1)), PB_sym,
                        Ite(Equals(S_sym, Int(2)), # Local DFI is PA+1
                            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym), 
                            # Else S_sym >= 3
                            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), PB_sym - Int(1))
                           ))
                       ))

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

    Res_canon_repr = op_canonical_result_definer( # This uses the canonical logic builder
        X_canon_repr, Y_canon_repr, 
        f"{result_name_prefix_local}_resc", 
        Omega_eff_C_sym # Pass the ADAPTIVE Omega_eff_C
    )
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])

    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym
    )
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))

    # For debugging the mapping and canonical results:
    debug_info = {
        "X_canon_repr_dbg": X_canon_repr, 
        "Y_canon_repr_dbg": Y_canon_repr,
        "Res_canon_repr_dbg": Res_canon_repr,
        "Omega_eff_C_sym_dbg": Omega_eff_C_sym
    }

    return {
        "val_L_sym": Res_L_val_sym, 
        "defining_assertions": defining_assertions_for_local_op,
        "debug_info": debug_info
    }

# --- Phase 4: Generic Property Prover (Copied) ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True, print_debug_reprs: List[Dict[str,Any]] = []):
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
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode): 
                     print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
            if print_debug_reprs:
                print("  DEBUG Canonical Representations in Counterexample:")
                for repr_dict in print_debug_reprs:
                    if repr_dict: # Ensure it's not None
                        val_str = f"V={solver.get_value(repr_dict['val'])}" if repr_dict['val'] in solver.get_model() else "V=?"
                        is_z_str = f"Z={solver.get_value(repr_dict['is_zero'])}" if repr_dict['is_zero'] in solver.get_model() else "Z=?"
                        is_a_str = f"A={solver.get_value(repr_dict['is_areo'])}" if repr_dict['is_areo'] in solver.get_model() else "A=?"
                        is_f_str = f"F={solver.get_value(repr_dict['is_finite'])}" if repr_dict['is_finite'] in solver.get_model() else "F=?"
                        omega_eff_C_val_str = ""
                        if "Omega_eff_C_sym_dbg" in repr_dict and repr_dict["Omega_eff_C_sym_dbg"] in solver.get_model(): # Check if it's a debug_info dict
                             omega_eff_C_val_str = f", Omega_eff_C={solver.get_value(repr_dict['Omega_eff_C_sym_dbg'])}"
                        print(f"    {repr_dict['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}{omega_eff_C_val_str}")


    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Adaptive Archetype Test ======\n")

    P_A_val_sym = Symbol("PA_val", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val", solver_INT_TYPE)
    La_val_sym = Symbol("La_val", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val", solver_INT_TYPE)

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S_py} (Maps to Adaptive Canonical Omega) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0))

        # --- Test L2_Adapt: Associativity of smart_raw_add_local_adaptive ---
        print(f"--- Test L2_Adapt: Associativity of smart_raw_add_local_adaptive (Local Span S={current_local_span_S_py}) ---")
        s.push()
        # For this general test, La, Lb, Lc can be any valid local values (ZS, AS, or DFI)
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))

        sum_ab_L2A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2A_sum_ab")
        lhs_L2A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, sum_ab_L2A_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2A_lhs")
        sum_bc_L2A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2A_sum_bc")
        rhs_L2A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, La_val_sym, sum_bc_L2A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L2A_rhs")
        
        all_L2A_assertions = sum_ab_L2A_dict["defining_assertions"] + lhs_L2A_dict["defining_assertions"] + \
                               sum_bc_L2A_dict["defining_assertions"] + rhs_L2A_dict["defining_assertions"]
        
        debug_reprs_L2A = [
            sum_ab_L2A_dict["debug_info"]["X_canon_repr_dbg"], sum_ab_L2A_dict["debug_info"]["Y_canon_repr_dbg"], sum_ab_L2A_dict["debug_info"]["Res_canon_repr_dbg"],
            lhs_L2A_dict["debug_info"]["X_canon_repr_dbg"], lhs_L2A_dict["debug_info"]["Y_canon_repr_dbg"], lhs_L2A_dict["debug_info"]["Res_canon_repr_dbg"],
            sum_bc_L2A_dict["debug_info"]["X_canon_repr_dbg"], sum_bc_L2A_dict["debug_info"]["Y_canon_repr_dbg"], sum_bc_L2A_dict["debug_info"]["Res_canon_repr_dbg"],
            rhs_L2A_dict["debug_info"]["X_canon_repr_dbg"], rhs_L2A_dict["debug_info"]["Y_canon_repr_dbg"], rhs_L2A_dict["debug_info"]["Res_canon_repr_dbg"],
        ]

        prove_or_find_counterexample(s, f"L2A Assoc. smart_raw_add_local_adaptive (S={current_local_span_S_py})",
                                     all_L2A_assertions,
                                     avc_equiv_local(lhs_L2A_dict["val_L_sym"], rhs_L2A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym, 
                                                          sum_ab_L2A_dict["val_L_sym"], lhs_L2A_dict["val_L_sym"], 
                                                          sum_bc_L2A_dict["val_L_sym"], rhs_L2A_dict["val_L_sym"]],
                                     print_debug_reprs=debug_reprs_L2A)
        s.pop()

        # --- Test L3_Adapt: Associativity of raw_mul_local_adaptive ---
        print(f"\n--- Test L3_Adapt: Associativity of raw_mul_local_adaptive (Local Span S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))

        prod_ab_L3A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3A_prod_ab")
        lhs_mul_L3A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, prod_ab_L3A_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3A_lhs_mul")
        prod_bc_L3A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3A_prod_bc")
        rhs_mul_L3A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, prod_bc_L3A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L3A_rhs_mul")

        all_L3A_assertions = prod_ab_L3A_dict["defining_assertions"] + lhs_mul_L3A_dict["defining_assertions"] + \
                               prod_bc_L3A_dict["defining_assertions"] + rhs_mul_L3A_dict["defining_assertions"]

        prove_or_find_counterexample(s, f"L3A Assoc. raw_mul_local_adaptive (S={current_local_span_S_py})",
                                     all_L3A_assertions,
                                     avc_equiv_local(lhs_mul_L3A_dict["val_L_sym"], rhs_mul_L3A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym])
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC Adaptive Archetype Test Complete ======")

