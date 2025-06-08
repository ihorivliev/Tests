from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# OMEGA_VARIANTS_FOR_LOCAL_SPAN_S will define the SPAN S = P_B - P_A for local frames
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7] 
DEFAULT_P_A_OFFSET = 0 

# Configuration for the FIXED Canonical Archetype
FIXED_CANONICAL_OMEGA_PY = 2
FIXED_CANONICAL_OMEGA_SMT = Int(FIXED_CANONICAL_OMEGA_PY)
# The DFI of this fixed canonical archetype is just {Int(1)}

# --- Phase 1: Foundational Definitions (Canonical AVC - used by both approaches) ---
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

# --- Phase 2: Canonical Raw Operations Definitions (Operating on the FIXED Archetype [0, FIXED_CANONICAL_OMEGA_SMT]) ---
# These are our standard operation logic builders, but they will always receive FIXED_CANONICAL_OMEGA_SMT as current_omega_smt

def smart_raw_add_logic_builder_fixed_arch(i1: Dict[str, Any], i2: Dict[str, Any], 
                                     res: Dict[str, Any], _fixed_omega_smt: FNode = FIXED_CANONICAL_OMEGA_SMT) -> FNode:
    # Using _fixed_omega_smt to emphasize it's always the global fixed Omega for this builder
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
                            Ite(val_sum >= _fixed_omega_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) 
                            )))
    return And(formulas)

def define_smart_raw_add_fixed_arch_result(i1_fixed_arch_repr: Dict[str, Any], i2_fixed_arch_repr: Dict[str, Any], 
                                           result_name_prefix: str) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    # Constraints for i1_fixed_arch_repr, i2_fixed_arch_repr (e.g. val < FIXED_CANONICAL_OMEGA_SMT if finite)
    # are assumed to be handled by the mapping function that creates them.
    res_repr["definition"] = smart_raw_add_logic_builder_fixed_arch(i1_fixed_arch_repr, i2_fixed_arch_repr, res_repr, FIXED_CANONICAL_OMEGA_SMT)
    return res_repr

def raw_mul_logic_builder_fixed_arch(i1: Dict[str, Any], i2: Dict[str, Any], 
                               res: Dict[str, Any], _fixed_omega_smt: FNode = FIXED_CANONICAL_OMEGA_SMT) -> FNode:
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
                            Ite(val_prod >= _fixed_omega_smt, And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
    return And(formulas)

def define_raw_mul_fixed_arch_result(i1_fixed_arch_repr: Dict[str, Any], i2_fixed_arch_repr: Dict[str, Any], 
                                     result_name_prefix: str) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder_fixed_arch(i1_fixed_arch_repr, i2_fixed_arch_repr, res_repr, FIXED_CANONICAL_OMEGA_SMT)
    return res_repr

# --- Phase 3: Local Frame Definitions and Mappings to FIXED Canonical Archetype ---

def is_local_ZS(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    # Ensure S > 0 by P_A < P_B. If P_A = P_B-1 (span is 1), DFI is empty.
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

def map_local_to_fixed_archetype_input_repr(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, # Defines the local frame
    fixed_arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    """
    Maps a local value to one of the three states of the FIXED canonical archetype [0, FIXED_CANONICAL_OMEGA_SMT].
    Returns the fixed archetype Intensity representation and defining assertions.
    """
    fixed_arch_repr = create_intensity_representation(fixed_arch_name_prefix)
    assertions = [fixed_arch_repr["constraints"]]

    is_L_ZS_cond = is_local_ZS(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS(Local_val_sym, PB_sym)
    # is_L_DFI_cond is implicit if not ZS or AS

    # Map local kind to fixed canonical kind flags
    # ZS_Local -> ZS_FixedArch
    # AS_Local -> AS_FixedArch
    # DFI_Local -> Fp_FixedArch(1) (since fixed archetype DFI is just {1})
    assertions.append(
        Ite(is_L_ZS_cond, 
            And(fixed_arch_repr["is_zero"], Not(fixed_arch_repr["is_areo"]), Not(fixed_arch_repr["is_finite"])),
            Ite(is_L_AS_cond,
                And(Not(fixed_arch_repr["is_zero"]), fixed_arch_repr["is_areo"], Not(fixed_arch_repr["is_finite"])),
                And(Not(fixed_arch_repr["is_zero"]), Not(fixed_arch_repr["is_areo"]), fixed_arch_repr["is_finite"])
            )
        )
    )
    
    # Define fixed canonical value based on fixed canonical kind
    # For ZS_FixedArch, val is unconstrained by mapping.
    # For AS_FixedArch, its value must be FIXED_CANONICAL_OMEGA_SMT.
    assertions.append(Implies(fixed_arch_repr["is_areo"], Equals(fixed_arch_repr["val"], FIXED_CANONICAL_OMEGA_SMT)))
    # For Fp_FixedArch, its value must be 1 (the only DFI value in the fixed archetype).
    assertions.append(Implies(fixed_arch_repr["is_finite"], Equals(fixed_arch_repr["val"], Int(1))))
    
    return fixed_arch_repr, assertions

def define_local_op_fixed_archetype_result(
    op_fixed_arch_result_definer: Callable, # e.g., define_smart_raw_add_fixed_arch_result
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str
) -> Dict[str, Any]:
    """
    Defines a local operation by mapping to a FIXED canonical archetype,
    applying the operation there, and mapping the result back.
    """
    defining_assertions_for_local_op = []
    
    # 1. Create fixed archetype representations for local inputs
    X_fixed_arch_repr, x_fixed_arch_assertions = map_local_to_fixed_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, f"{result_name_prefix_local}_xfarch"
    )
    defining_assertions_for_local_op.extend(x_fixed_arch_assertions)

    Y_fixed_arch_repr, y_fixed_arch_assertions = map_local_to_fixed_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, f"{result_name_prefix_local}_yfarch"
    )
    defining_assertions_for_local_op.extend(y_fixed_arch_assertions)

    # 2. Perform operation in the FIXED canonical archetype frame
    Res_fixed_arch_repr = op_fixed_arch_result_definer( # This definer uses FIXED_CANONICAL_OMEGA_SMT internally
        X_fixed_arch_repr, Y_fixed_arch_repr, 
        f"{result_name_prefix_local}_resfarch"
    )
    defining_assertions_for_local_op.append(Res_fixed_arch_repr["definition"])
    defining_assertions_for_local_op.append(Res_fixed_arch_repr["constraints"])

    # 3. Define the local result value based on the fixed archetype result
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    
    # Map fixed archetype result kind back to the local frame's scale
    # ZS_FixedArch -> P_A (Local ZS)
    # AS_FixedArch -> P_B (Local AS)
    # Fp_FixedArch(1) -> P_A + 1 (first DFI step in local frame, if span allows for a DFI)
    #                   If span S=1 (e.g. PA=0, PB=1), DFI is empty. Fp_FixedArch(1) should map to P_B (Local AS).
    #                   If span S=0 (PA=PB), this is invalid by constraint P_A < P_B.
    
    S_val = P_B_val_sym - P_A_val_sym # Local span

    # Define backward mapping for Fp_FixedArch(1)
    # If S_val (span) is 1, Fp_FixedArch(1) from canonical [0,2] is like "hitting the ceiling" relative to a single DFI step.
    # So, it should map to P_B_val_sym.
    # If S_val >= 2, there is room for at least one local DFI, map Fp_FixedArch(1) to P_A_val_sym + 1.
    map_fp_fixed_to_local_val = Ite(Equals(S_val, Int(1)),
                                    P_B_val_sym, # Effectively, the single DFI step hits the local Areo
                                    P_A_val_sym + Int(1) # Maps to the first DFI element
                                   )

    local_result_value_formula = Ite(Res_fixed_arch_repr["is_zero"], P_A_val_sym,
                                 Ite(Res_fixed_arch_repr["is_areo"], P_B_val_sym,
                                     map_fp_fixed_to_local_val 
                                 ))
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))

    return {
        "val_L_sym": Res_L_val_sym, 
        "defining_assertions": defining_assertions_for_local_op,
        # For debugging the mapping:
        "X_fixed_arch_repr": X_fixed_arch_repr,
        "Y_fixed_arch_repr": Y_fixed_arch_repr,
        "Res_fixed_arch_repr": Res_fixed_arch_repr
    }

# --- Phase 4: Generic Property Prover (Copied) ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, 
                                 model_vars_to_print: List[Any] = [],
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
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode): 
                     print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
                else:
                    print(f"  Unknown model var type: {var_item}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print(f"====== AVC Relativistic Deep Scrutiny (Fixed Canonical Archetype Omega={FIXED_CANONICAL_OMEGA_PY}) ======\n")

    P_A_val_sym = Symbol("PA_val", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val", solver_INT_TYPE)
    La_val_sym = Symbol("La_val", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val", solver_INT_TYPE)
    Li1_val_sym = Symbol("Li1_val", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val", solver_INT_TYPE)

    for current_local_span_S in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S} (Maps to Fixed Canonical Omega={FIXED_CANONICAL_OMEGA_PY}) =====\n")

        # Define P_A and P_B for this local span
        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + Int(current_local_span_S)))
        s.add_assertion(Int(current_local_span_S) > Int(0)) # Ensure span is positive

        # --- Test L0_FixedArch: Sanity of avc_equiv_local ---
        print(f"--- Test L0_FixedArch: Sanity of avc_equiv_local (Local Span S={current_local_span_S}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        prove_or_find_counterexample(s, f"L0.1F Reflexivity (S={current_local_span_S})",
                                     [], avc_equiv_local(La_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym])
        s.pop(); s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        prop_L0_2 = Implies(avc_equiv_local(La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym),
                              avc_equiv_local(Lb_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym))
        prove_or_find_counterexample(s, f"L0.2F Symmetry (S={current_local_span_S})", [], prop_L0_2,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym])
        s.pop(); s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))
        premise_L0_3 = And(avc_equiv_local(La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym),
                             avc_equiv_local(Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym))
        conclusion_L0_3 = avc_equiv_local(La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.3F Transitivity (S={current_local_span_S})", [premise_L0_3], conclusion_L0_3,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym])
        s.pop()

        # --- Test L1_FixedArch: Well-Definedness of Local Operations (Fixed Archetype) ---
        print(f"\n--- Test L1_FixedArch: Well-Definedness (Fixed Arch, Local Span S={current_local_span_S}) ---")
        s.push()
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))
        premise_L1F = And(avc_equiv_local(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym),
                          avc_equiv_local(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        
        op_L1F_add_r1_dict = define_local_op_fixed_archetype_result(define_smart_raw_add_fixed_arch_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1F_add_r1")
        op_L1F_add_r2_dict = define_local_op_fixed_archetype_result(define_smart_raw_add_fixed_arch_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1F_add_r2")
        conclusion_L1F_add = avc_equiv_local(op_L1F_add_r1_dict["val_L_sym"], op_L1F_add_r2_dict["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.1F smart_raw_add_local_fixed respects avc_equiv_local (S={current_local_span_S})",
                                     [premise_L1F] + op_L1F_add_r1_dict["defining_assertions"] + op_L1F_add_r2_dict["defining_assertions"],
                                     conclusion_L1F_add,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, Li1_val_sym, Lj1_val_sym, Li2_val_sym, Lj2_val_sym, 
                                                          op_L1F_add_r1_dict["val_L_sym"], op_L1F_add_r2_dict["val_L_sym"],
                                                          op_L1F_add_r1_dict["X_fixed_arch_repr"], op_L1F_add_r1_dict["Y_fixed_arch_repr"], op_L1F_add_r1_dict["Res_fixed_arch_repr"],
                                                          op_L1F_add_r2_dict["X_fixed_arch_repr"], op_L1F_add_r2_dict["Y_fixed_arch_repr"], op_L1F_add_r2_dict["Res_fixed_arch_repr"]])

        op_L1F_mul_r1_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1F_mul_r1")
        op_L1F_mul_r2_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1F_mul_r2")
        conclusion_L1F_mul = avc_equiv_local(op_L1F_mul_r1_dict["val_L_sym"], op_L1F_mul_r2_dict["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.2F raw_mul_local_fixed respects avc_equiv_local (S={current_local_span_S})",
                                     [premise_L1F] + op_L1F_mul_r1_dict["defining_assertions"] + op_L1F_mul_r2_dict["defining_assertions"],
                                     conclusion_L1F_mul,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, Li1_val_sym, Lj1_val_sym, Li2_val_sym, Lj2_val_sym, op_L1F_mul_r1_dict["val_L_sym"], op_L1F_mul_r2_dict["val_L_sym"]])
        s.pop()

        # --- Test L2_FixedArch: Associativity of smart_raw_add_local_fixed_archetype ---
        print(f"\n--- Test L2_FixedArch: Associativity of smart_raw_add_local_fixed (Local Span S={current_local_span_S}) ---")
        s.push()
        # For this test, La, Lb, Lc are general local values (can be poles or DFI)
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))

        sum_ab_L2F_dict = define_local_op_fixed_archetype_result(define_smart_raw_add_fixed_arch_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2F_sum_ab")
        lhs_L2F_dict = define_local_op_fixed_archetype_result(define_smart_raw_add_fixed_arch_result, sum_ab_L2F_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2F_lhs")
        sum_bc_L2F_dict = define_local_op_fixed_archetype_result(define_smart_raw_add_fixed_arch_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2F_sum_bc")
        rhs_L2F_dict = define_local_op_fixed_archetype_result(define_smart_raw_add_fixed_arch_result, La_val_sym, sum_bc_L2F_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L2F_rhs")
        
        all_L2F_assertions = sum_ab_L2F_dict["defining_assertions"] + lhs_L2F_dict["defining_assertions"] + \
                               sum_bc_L2F_dict["defining_assertions"] + rhs_L2F_dict["defining_assertions"]
        
        prove_or_find_counterexample(s, f"L2F Assoc. smart_raw_add_local_fixed (S={current_local_span_S})",
                                     all_L2F_assertions,
                                     avc_equiv_local(lhs_L2F_dict["val_L_sym"], rhs_L2F_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym, 
                                                          sum_ab_L2F_dict["val_L_sym"], lhs_L2F_dict["val_L_sym"], 
                                                          sum_bc_L2F_dict["val_L_sym"], rhs_L2F_dict["val_L_sym"],
                                                          sum_ab_L2F_dict["Res_fixed_arch_repr"], lhs_L2F_dict["Res_fixed_arch_repr"], # Debug canonical results
                                                          sum_bc_L2F_dict["Res_fixed_arch_repr"], rhs_L2F_dict["Res_fixed_arch_repr"]])
        s.pop()

        # --- Test L3_FixedArch: Associativity of raw_mul_local_fixed_archetype ---
        print(f"\n--- Test L3_FixedArch: Associativity of raw_mul_local_fixed (Local Span S={current_local_span_S}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))

        prod_ab_L3F_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3F_prod_ab")
        lhs_mul_L3F_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, prod_ab_L3F_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3F_lhs_mul")
        prod_bc_L3F_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3F_prod_bc")
        rhs_mul_L3F_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, La_val_sym, prod_bc_L3F_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L3F_rhs_mul")

        all_L3F_assertions = prod_ab_L3F_dict["defining_assertions"] + lhs_mul_L3F_dict["defining_assertions"] + \
                               prod_bc_L3F_dict["defining_assertions"] + rhs_mul_L3F_dict["defining_assertions"]

        prove_or_find_counterexample(s, f"L3F Assoc. raw_mul_local_fixed (S={current_local_span_S})",
                                     all_L3F_assertions,
                                     avc_equiv_local(lhs_mul_L3F_dict["val_L_sym"], rhs_mul_L3F_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym])
        s.pop()

        # --- Test L5_FixedArch: Distributivity (Local, Fixed Archetype) ---
        # La *L (Lb +L Lc) ~L (La *L Lb) +L (La *L Lc)
        print(f"\n--- Test L5_FixedArch: Distributivity (Local Fixed Arch, Local Span S={current_local_span_S}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))

        sum_bc_L5F_dict = define_local_op_fixed_archetype_result(define_smart_raw_add_fixed_arch_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L5F_sum_bc")
        lhs_dist_L5F_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, La_val_sym, sum_bc_L5F_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L5F_lhs_dist")
        prod_ab_L5F_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5F_prod_ab")
        prod_ac_L5F_dict = define_local_op_fixed_archetype_result(define_raw_mul_fixed_arch_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L5F_prod_ac")
        rhs_dist_L5F_dict = define_local_op_fixed_archetype_result(define_smart_raw_add_fixed_arch_result, prod_ab_L5F_dict["val_L_sym"], prod_ac_L5F_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L5F_rhs_dist")

        all_L5F_definitions = sum_bc_L5F_dict["defining_assertions"] + lhs_dist_L5F_dict["defining_assertions"] + \
                               prod_ab_L5F_dict["defining_assertions"] + prod_ac_L5F_dict["defining_assertions"] + \
                               rhs_dist_L5F_dict["defining_assertions"]
        
        prove_or_find_counterexample(s, f"L5F Distributivity (Local Fixed Arch, S={current_local_span_S})",
                                     all_L5F_definitions,
                                     avc_equiv_local(lhs_dist_L5F_dict["val_L_sym"], rhs_dist_L5F_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym,
                                                          sum_bc_L5F_dict["val_L_sym"], lhs_dist_L5F_dict["val_L_sym"],
                                                          prod_ab_L5F_dict["val_L_sym"], prod_ac_L5F_dict["val_L_sym"],
                                                          rhs_dist_L5F_dict["val_L_sym"],
                                                          sum_bc_L5F_dict["Res_fixed_arch_repr"], lhs_dist_L5F_dict["Res_fixed_arch_repr"],
                                                          prod_ab_L5F_dict["Res_fixed_arch_repr"], prod_ac_L5F_dict["Res_fixed_arch_repr"],
                                                          rhs_dist_L5F_dict["Res_fixed_arch_repr"]])
        s.pop()

        del s 
        print("-" * 80)

    print(f"\n====== AVC Relativistic Deep Scrutiny (Fixed Canonical Archetype Omega={FIXED_CANONICAL_OMEGA_PY}) Test Complete ======")

