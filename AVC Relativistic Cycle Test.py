from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# OMEGA_VARIANTS_TO_TEST will define the SPAN S = P_B - P_A for local frames
OMEGA_VARIANTS_TO_TEST = [2, 3, 5, 7] # Spans for the local cycle
# DEFAULT_P_A_OFFSET can be used to test translation invariance, e.g., cycle [0,S] vs [100, 100+S]
DEFAULT_P_A_OFFSET = 0 # Could also test with 100 or other values

# --- Phase 1: Foundational Definitions (Canonical AVC) ---
# These are the standard definitions for an AVC operating in a [0, Omega_canonical] frame.

def create_intensity_representation(name_prefix: str) -> Dict[str, Any]:
    """
    Creates PySMT symbols for a Canonical Intensity and its critical validity constraints.
    An Intensity is abstractly one of: ZeroState, AreoState, or Finite(PosNat).
    """
    is_zero = Symbol(f"{name_prefix}_is_zero", solver_BOOL_TYPE)
    is_areo = Symbol(f"{name_prefix}_is_areo", solver_BOOL_TYPE)
    is_finite = Symbol(f"{name_prefix}_is_finite", solver_BOOL_TYPE)
    val = Symbol(f"{name_prefix}_val", solver_INT_TYPE) # Value if finite

    # Constraint: Must be exactly one of ZS, AS, or Fp
    constraint_exactly_one_state = ExactlyOne(is_zero, is_areo, is_finite)
    # Constraint: If Finite, its value must be a Positive Natural (val > 0)
    # The upper bound (val < Omega_canonical) is context-dependent and applied by the canonical representation builder.
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

# --- Phase 2: Canonical Raw Operations Definitions (Copied from previous robust versions) ---
# These operate on canonical Intensity representations and take a current_omega_smt (which will be the span S).

def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    """
    Logic builder for canonical smart_raw_add. AS_C + Fp_C -> Fp_C.
    Assumes i1, i2, res are canonical Intensity representations.
    current_omega_smt is the Omega for this canonical operation (i.e., the span S).
    """
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    
    # Case 1: i1 is ZeroState_Canonical (ZS_C + X_C -> X_C)
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), # ZS_C + ZS_C -> ZS_C
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # ZS_C + AS_C -> AS_C
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) # ZS_C + Fp_C -> Fp_C
    )))
    
    # Case 2: i1 is AreoState_Canonical (AS_C + X_C -> X_C, due to AS_C ~ ZS_C for this op)
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  # AS_C + ZS_C -> AS_C
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  # AS_C + AS_C -> AS_C
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) # AS_C + Fp_C -> Fp_C
    )))
    
    # Case 3: i1 is Finite_Canonical
    # Fp_C + ZS_C -> Fp_C
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    # Fp_C + AS_C -> Fp_C
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    # Fp_C1 + Fp_C2 -> thresholded sum
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
                            Ite(val_sum >= current_omega_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # result is AS_C
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) # result is Fp_C(sum)
                            )))
    return And(formulas)

def define_smart_raw_add_canonical_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                                     result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    # Canonical Finites must be < current_omega_smt. This is handled by define_canonical_repr_from_local.
    # The result's value constraint (if Fp_C) is handled by smart_raw_add_logic_builder.
    res_repr["definition"] = smart_raw_add_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    # Copied from previous robust versions
    formulas = []
    val_prod = i1["val"] * i2["val"] 
    
    # ZS_C is annihilator
    formulas.append(Implies(i1["is_zero"], 
                            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), 
                            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    
    # AS_C * AS_C -> AS_C
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), 
                                i1["is_areo"], i2["is_areo"]), 
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    
    # AS_C * Fp_C -> if Fp_C.val > 0 then AS_C else ZS_C
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i1["is_areo"], i2["is_finite"]), 
                            Ite(i2["val"] > Int(0), # Fp_C.val > 0 is already in its constraints
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  
                            )))
    # Fp_C * AS_C -> if Fp_C.val > 0 then AS_C else ZS_C
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i2["is_areo"], i1["is_finite"]), 
                            Ite(i1["val"] > Int(0), # Fp_C.val > 0 is already in its constraints
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  
                            )))
    
    # Fp_C1 * Fp_C2 -> thresholded product
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
                            Ite(val_prod >= current_omega_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                                    Equals(res["val"], val_prod)) 
                            )))
    return And(formulas)

def define_raw_mul_canonical_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                               result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)
    return res_repr

# --- Phase 3: Local Frame Definitions and Transformations ---

def is_local_ZS(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

def avc_equiv_local(X1_L_val_sym: FNode, X2_L_val_sym: FNode, 
                    P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    """Defines avc_equiv for local intensity values within frame [P_A, P_B]."""
    return Or(
        And(is_local_ZS(X1_L_val_sym, P_A_val_sym), is_local_ZS(X2_L_val_sym, P_A_val_sym)),
        And(is_local_AS(X1_L_val_sym, P_B_val_sym), is_local_AS(X2_L_val_sym, P_B_val_sym)),
        And(is_local_ZS(X1_L_val_sym, P_A_val_sym), is_local_AS(X2_L_val_sym, P_B_val_sym)), # Local Unio
        And(is_local_AS(X1_L_val_sym, P_B_val_sym), is_local_ZS(X2_L_val_sym, P_A_val_sym)), # Local Unio
        And(
            is_local_DFI(X1_L_val_sym, P_A_val_sym, P_B_val_sym), 
            is_local_DFI(X2_L_val_sym, P_A_val_sym, P_B_val_sym), 
            Equals(X1_L_val_sym, X2_L_val_sym)
        )
    )

def define_canonical_repr_from_local(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, # S_sym is PB_sym - PA_sym, the canonical Omega
    canon_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    """
    Creates a canonical Intensity representation from a local value and its frame.
    Returns the canonical representation dict and a list of assertions defining it.
    """
    canon_repr = create_intensity_representation(canon_name_prefix)
    assertions = [canon_repr["constraints"]] # Basic validity of the canonical structure

    val_for_canon_calc = Local_val_sym - PA_sym # Value relative to local zero, for canonical DFI

    is_L_ZS_cond = is_local_ZS(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS(Local_val_sym, PB_sym)
    # is_L_DFI_cond = is_local_DFI(Local_val_sym, PA_sym, PB_sym) # Implicit if not ZS or AS

    # Map local kind to canonical kind flags
    assertions.append(Ite(is_L_ZS_cond, 
                          And(canon_repr["is_zero"], Not(canon_repr["is_areo"]), Not(canon_repr["is_finite"])),
                          Ite(is_L_AS_cond,
                              And(Not(canon_repr["is_zero"]), canon_repr["is_areo"], Not(canon_repr["is_finite"])),
                              And(Not(canon_repr["is_zero"]), Not(canon_repr["is_areo"]), canon_repr["is_finite"])
                             )
                         ))
    
    # Define canonical value based on canonical kind
    # For ZS_C, val is unconstrained by mapping but must satisfy its own PosNat if it were Fp_C (which it isn't).
    # For AS_C, its value must be S_sym (the canonical Omega).
    assertions.append(Implies(canon_repr["is_areo"], Equals(canon_repr["val"], S_sym)))
    # For Fp_C, its value is the translated local DFI value.
    assertions.append(Implies(canon_repr["is_finite"], Equals(canon_repr["val"], val_for_canon_calc)))
    
    # Additional constraints for the canonical Fp_C value (val_for_canon_calc):
    # It must be > 0 (already in canon_repr["constraints"] via Implies(is_finite, val > 0))
    # It must be < S_sym (the canonical Omega for this frame)
    assertions.append(Implies(canon_repr["is_finite"], val_for_canon_calc < S_sym))
    # Note: val_for_canon_calc > 0 is also implied if Local_val_sym is a local DFI.

    return canon_repr, assertions

def define_local_op_result(
    op_canonical_result_definer: Callable, # e.g., define_smart_raw_add_canonical_result
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str
) -> Dict[str, Any]:
    """
    Defines a local operation by transforming inputs to a canonical frame,
    applying the canonical operation, and transforming the result back.
    Returns a dict with the SMT symbol for the local result value and all defining SMT assertions.
    """
    defining_assertions_for_local_op = []
    
    current_S_val_sym = P_B_val_sym - P_A_val_sym # This is Omega_Canonical for this local frame

    # 1. Create canonical representations for local inputs X_L_val_sym and Y_L_val_sym
    X_canon_repr, x_canon_assertions = define_canonical_repr_from_local(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, current_S_val_sym, f"{result_name_prefix_local}_xc"
    )
    defining_assertions_for_local_op.extend(x_canon_assertions)

    Y_canon_repr, y_canon_assertions = define_canonical_repr_from_local(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, current_S_val_sym, f"{result_name_prefix_local}_yc"
    )
    defining_assertions_for_local_op.extend(y_canon_assertions)

    # 2. Perform operation in the canonical frame
    Res_canon_repr = op_canonical_result_definer(
        X_canon_repr, Y_canon_repr, 
        f"{result_name_prefix_local}_resc", 
        current_S_val_sym # Pass the span S as the Omega for the canonical operation
    )
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"]) # Constraints of the result representation

    # 3. Define the local result value based on the canonical result
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    
    # Map canonical result kind and value back to the local frame's scale
    local_result_value_formula = Ite(Res_canon_repr["is_zero"], P_A_val_sym,          # Canonical ZS -> Local ZS (P_A)
                                 Ite(Res_canon_repr["is_areo"], P_B_val_sym,          # Canonical AS -> Local AS (P_B)
                                     P_A_val_sym + Res_canon_repr["val"]     # Canonical Fp(v') -> P_A + v'
                                 ))
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))

    return {
        "val_L_sym": Res_L_val_sym, 
        "defining_assertions": defining_assertions_for_local_op
    }

# --- Phase 4: Generic Property Prover (Copied) ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, 
                                 model_vars_to_print: List[Any] = [], # Can be Dict[str,Any] or FNode
                                 print_model_on_fail: bool = True):
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions: solver.add_assertion(assertion)
    
    solver.add_assertion(Not(property_to_prove_true))
        
    proved_universally = False
    if not solver.solve(): # If "NOT property_to_prove_true" is UNSAT
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved_universally = True
    else: # If "NOT property_to_prove_true" is SAT, then "property_to_prove_true" does NOT hold universally
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_fail:
            for var_item in model_vars_to_print:
                if isinstance(var_item, dict) and "name" in var_item : # It's an Intensity representation
                    val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                    is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                    is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode): # It's a raw SMT symbol (like P_A_val_sym or a local result value)
                     print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
                else:
                    print(f"  Unknown model var type: {var_item}")
            
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Relativistic Cycle Test ======\n")

    # Symbolic local frame poles, used across different span settings
    P_A_val_sym = Symbol("PA_val", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val", solver_INT_TYPE)

    # Symbolic local intensity values for general tests
    La_val_sym = Symbol("La_val", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val", solver_INT_TYPE)

    # Symbolic local intensity values for respectfulness tests
    Li1_val_sym = Symbol("Li1_val", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val", solver_INT_TYPE)

    for current_span_value in OMEGA_VARIANTS_TO_TEST:
        s = Solver(name="z3") # Fresh solver for each span configuration
        print(f"\n\n===== TESTING RELATIVISTIC CYCLE WITH LOCAL SPAN S = {current_span_value} =====\n")

        # Define P_A and P_B for this span
        # Let P_A be a fixed offset, P_B determined by span
        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + Int(current_span_value)))
        
        # Assert P_A < P_B and Span > 0 (implicitly true by above for current_span_value > 0)
        # s.add_assertion(P_A_val_sym < P_B_val_sym) # Ensured by P_B = P_A + S and S > 0
        s.add_assertion(Int(current_span_value) > Int(0)) # Ensure span is positive

        # --- Test L0: Sanity of avc_equiv_local ---
        print(f"--- Test L0: Sanity of avc_equiv_local (Span S={current_span_value}) ---")
        # Assert La_val_sym is a valid value within the current local frame for reflexivity
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        prove_or_find_counterexample(s, f"L0.1 Reflexivity of avc_equiv_local (S={current_span_value})",
                                     [], avc_equiv_local(La_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym])
        s.pop()
        # For symmetry and transitivity, we need more symbolic local values
        # Setup for symmetry: La_val_sym, Lb_val_sym are valid local values
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        prop_L0_2 = Implies(avc_equiv_local(La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym),
                              avc_equiv_local(Lb_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym))
        prove_or_find_counterexample(s, f"L0.2 Symmetry of avc_equiv_local (S={current_span_value})",
                                     [], prop_L0_2,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym])
        s.pop()
        # Setup for transitivity: La, Lb, Lc are valid local values
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))
        premise_L0_3 = And(avc_equiv_local(La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym),
                             avc_equiv_local(Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym))
        conclusion_L0_3 = avc_equiv_local(La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.3 Transitivity of avc_equiv_local (S={current_span_value})",
                                     [premise_L0_3], conclusion_L0_3, # Test P => Q by checking if P and Not Q is SAT
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym])
        s.pop()

        # --- Test L1: Well-Definedness of Local Operations ---
        print(f"\n--- Test L1: Well-Definedness of Local Operations (Span S={current_span_value}) ---")
        s.push()
        # Assert Li1, Lj1, Li2, Lj2 are valid values in the local frame
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))

        premise_L1 = And(avc_equiv_local(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym),
                         avc_equiv_local(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        
        # Test for smart_raw_add_local
        op_L1_add_res1_dict = define_local_op_result(define_smart_raw_add_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1_add_r1")
        op_L1_add_res2_dict = define_local_op_result(define_smart_raw_add_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1_add_r2")
        conclusion_L1_add = avc_equiv_local(op_L1_add_res1_dict["val_L_sym"], op_L1_add_res2_dict["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.1 smart_raw_add_local respects avc_equiv_local (S={current_span_value})",
                                     [premise_L1] + op_L1_add_res1_dict["defining_assertions"] + op_L1_add_res2_dict["defining_assertions"],
                                     conclusion_L1_add,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, Li1_val_sym, Lj1_val_sym, Li2_val_sym, Lj2_val_sym, op_L1_add_res1_dict["val_L_sym"], op_L1_add_res2_dict["val_L_sym"]])

        # Test for raw_mul_local
        op_L1_mul_res1_dict = define_local_op_result(define_raw_mul_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1_mul_r1")
        op_L1_mul_res2_dict = define_local_op_result(define_raw_mul_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1_mul_r2")
        conclusion_L1_mul = avc_equiv_local(op_L1_mul_res1_dict["val_L_sym"], op_L1_mul_res2_dict["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.2 raw_mul_local respects avc_equiv_local (S={current_span_value})",
                                     [premise_L1] + op_L1_mul_res1_dict["defining_assertions"] + op_L1_mul_res2_dict["defining_assertions"],
                                     conclusion_L1_mul,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, Li1_val_sym, Lj1_val_sym, Li2_val_sym, Lj2_val_sym, op_L1_mul_res1_dict["val_L_sym"], op_L1_mul_res2_dict["val_L_sym"]])
        s.pop()

        # --- Test L2: Associativity of smart_raw_add_local ---
        # Inputs La, Lb, Lc are constrained to be local DFIs for this general test of non-assoc.
        print(f"\n--- Test L2: Associativity of smart_raw_add_local (Span S={current_span_value}) ---")
        s.push()
        s.add_assertion(is_local_DFI(La_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI(Lb_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI(Lc_val_sym, P_A_val_sym, P_B_val_sym))

        sum_ab_L_dict = define_local_op_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2_sum_ab")
        lhs_L_dict = define_local_op_result(define_smart_raw_add_canonical_result, sum_ab_L_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2_lhs")
        sum_bc_L_dict = define_local_op_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2_sum_bc")
        rhs_L_dict = define_local_op_result(define_smart_raw_add_canonical_result, La_val_sym, sum_bc_L_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L2_rhs")
        
        all_L2_assertions = sum_ab_L_dict["defining_assertions"] + lhs_L_dict["defining_assertions"] + \
                              sum_bc_L_dict["defining_assertions"] + rhs_L_dict["defining_assertions"]
        
        prove_or_find_counterexample(s, f"L2 Associativity of smart_raw_add_local (S={current_span_value})",
                                     all_L2_assertions,
                                     avc_equiv_local(lhs_L_dict["val_L_sym"], rhs_L_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym, 
                                                          sum_ab_L_dict["val_L_sym"], lhs_L_dict["val_L_sym"], 
                                                          sum_bc_L_dict["val_L_sym"], rhs_L_dict["val_L_sym"]])
        s.pop()

        # --- Test L3: Associativity of raw_mul_local ---
        print(f"\n--- Test L3: Associativity of raw_mul_local (Span S={current_span_value}) ---")
        s.push()
        s.add_assertion(is_local_DFI(La_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI(Lb_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI(Lc_val_sym, P_A_val_sym, P_B_val_sym))

        prod_ab_L_dict = define_local_op_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3_prod_ab")
        lhs_mul_L_dict = define_local_op_result(define_raw_mul_canonical_result, prod_ab_L_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3_lhs_mul")
        prod_bc_L_dict = define_local_op_result(define_raw_mul_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3_prod_bc")
        rhs_mul_L_dict = define_local_op_result(define_raw_mul_canonical_result, La_val_sym, prod_bc_L_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L3_rhs_mul")

        all_L3_assertions = prod_ab_L_dict["defining_assertions"] + lhs_mul_L_dict["defining_assertions"] + \
                              prod_bc_L_dict["defining_assertions"] + rhs_mul_L_dict["defining_assertions"]

        prove_or_find_counterexample(s, f"L3 Associativity of raw_mul_local (S={current_span_value})",
                                     all_L3_assertions,
                                     avc_equiv_local(lhs_mul_L_dict["val_L_sym"], rhs_mul_L_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym,
                                                          prod_ab_L_dict["val_L_sym"], lhs_mul_L_dict["val_L_sym"],
                                                          prod_bc_L_dict["val_L_sym"], rhs_mul_L_dict["val_L_sym"]])
        s.pop()
        
        # --- Test L4: "DFI Haven" for smart_raw_add_local ---
        print(f"\n--- Test L4: DFI Haven for smart_raw_add_local (Span S={current_span_value}) ---")
        s.push()
        # Inputs La, Lb, Lc are local DFIs
        s.add_assertion(is_local_DFI(La_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI(Lb_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI(Lc_val_sym, P_A_val_sym, P_B_val_sym))

        # Define results for LHS and RHS
        sum_ab_L4_dict = define_local_op_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4_sum_ab")
        lhs_L4_dict = define_local_op_result(define_smart_raw_add_canonical_result, sum_ab_L4_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L4_lhs")
        sum_bc_L4_dict = define_local_op_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L4_sum_bc")
        rhs_L4_dict = define_local_op_result(define_smart_raw_add_canonical_result, La_val_sym, sum_bc_L4_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L4_rhs")
        
        all_L4_definitions = sum_ab_L4_dict["defining_assertions"] + lhs_L4_dict["defining_assertions"] + \
                               sum_bc_L4_dict["defining_assertions"] + rhs_L4_dict["defining_assertions"]
        
        # DFI Haven Conditions: all intermediate and final results must also be local DFIs
        dfi_haven_conditions_L4 = [
            is_local_DFI(sum_ab_L4_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(lhs_L4_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(sum_bc_L4_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(rhs_L4_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
        ]
        
        prove_or_find_counterexample(s, f"L4 smart_raw_add_local Associativity (DFI Haven, S={current_span_value})",
                                     all_L4_definitions + dfi_haven_conditions_L4,
                                     avc_equiv_local(lhs_L4_dict["val_L_sym"], rhs_L4_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym,
                                                          sum_ab_L4_dict["val_L_sym"], lhs_L4_dict["val_L_sym"],
                                                          sum_bc_L4_dict["val_L_sym"], rhs_L4_dict["val_L_sym"]])
        s.pop()

        # --- Test L5: "DFI Haven" for Distributivity (Local) ---
        # La *L (Lb +L Lc) ~L (La *L Lb) +L (La *L Lc)
        print(f"\n--- Test L5: DFI Haven for Distributivity (Local) (Span S={current_span_value}) ---")
        s.push()
        # Inputs La, Lb, Lc are local DFIs
        s.add_assertion(is_local_DFI(La_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI(Lb_val_sym, P_A_val_sym, P_B_val_sym))
        s.add_assertion(is_local_DFI(Lc_val_sym, P_A_val_sym, P_B_val_sym))

        # LHS: La *L (Lb +L Lc)
        sum_bc_L5_dict = define_local_op_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L5_sum_bc")
        lhs_dist_L5_dict = define_local_op_result(define_raw_mul_canonical_result, La_val_sym, sum_bc_L5_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L5_lhs_dist")

        # RHS: (La *L Lb) +L (La *L Lc)
        prod_ab_L5_dict = define_local_op_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5_prod_ab")
        prod_ac_L5_dict = define_local_op_result(define_raw_mul_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L5_prod_ac")
        rhs_dist_L5_dict = define_local_op_result(define_smart_raw_add_canonical_result, prod_ab_L5_dict["val_L_sym"], prod_ac_L5_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L5_rhs_dist")

        all_L5_definitions = sum_bc_L5_dict["defining_assertions"] + lhs_dist_L5_dict["defining_assertions"] + \
                               prod_ab_L5_dict["defining_assertions"] + prod_ac_L5_dict["defining_assertions"] + \
                               rhs_dist_L5_dict["defining_assertions"]
        
        # DFI Haven Conditions for Distributivity
        dfi_haven_conditions_L5 = [
            is_local_DFI(sum_bc_L5_dict["val_L_sym"], P_A_val_sym, P_B_val_sym), # Lb +L Lc is DFI
            is_local_DFI(lhs_dist_L5_dict["val_L_sym"], P_A_val_sym, P_B_val_sym), # La *L (Lb +L Lc) is DFI
            is_local_DFI(prod_ab_L5_dict["val_L_sym"], P_A_val_sym, P_B_val_sym), # La *L Lb is DFI
            is_local_DFI(prod_ac_L5_dict["val_L_sym"], P_A_val_sym, P_B_val_sym), # La *L Lc is DFI
            is_local_DFI(rhs_dist_L5_dict["val_L_sym"], P_A_val_sym, P_B_val_sym)  # (La*Lb) +L (La*Lc) is DFI
        ]

        prove_or_find_counterexample(s, f"L5 Distributivity (Local DFI Haven, S={current_span_value})",
                                     all_L5_definitions + dfi_haven_conditions_L5,
                                     avc_equiv_local(lhs_dist_L5_dict["val_L_sym"], rhs_dist_L5_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym,
                                                          sum_bc_L5_dict["val_L_sym"], lhs_dist_L5_dict["val_L_sym"],
                                                          prod_ab_L5_dict["val_L_sym"], prod_ac_L5_dict["val_L_sym"],
                                                          rhs_dist_L5_dict["val_L_sym"]])
        s.pop()

        del s # Release solver for this span
        print("-" * 80)

    print("\n====== AVC Relativistic Cycle Test Complete ======")

