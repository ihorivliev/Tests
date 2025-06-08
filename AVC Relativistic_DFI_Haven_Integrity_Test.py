from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [3, 5, 7] # Spans where non-standard behavior is typically seen for general Fp,Fp,Fp
                                 # Span S=2 often behaves like Omega_C=2 (associative add, distrib)
                                 # We'll add S=2 to see its behavior under these specific DFI Haven constraints.
OMEGA_VARIANTS_TO_TEST_WITH_S2 = [2, 3, 5, 7]
DEFAULT_P_A_OFFSET = 0

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

# --- Phase 2: Canonical Raw Operations Definitions (Parameterized by current_omega_smt) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) 
    )))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])) 
    )))
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

# --- Phase 3: Local Frame Definitions and Transformations (Direct Span S as Omega_C) ---
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
            Equals(X1_L_val_sym, X2_L_val_sym))
    )

def define_local_op_direct_span_result(
    op_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode, # Inputs are SMT integer values
    P_A_val_sym: FNode, P_B_val_sym: FNode, # Local frame poles
    result_name_prefix_local: str
) -> Dict[str, Any]:
    """
    Defines a local operation by transforming local SMT integer values to a canonical frame [0,S],
    applying the canonical operation (which returns a canonical Intensity repr), 
    and transforming the canonical result back to a local SMT integer value.
    Returns a dict: {"val_L_sym": SMT_Int_Symbol_for_Local_Result, 
                     "defining_assertions": List_of_SMT_Assertions}
    """
    all_defining_assertions = []
    
    current_S_val_sym = P_B_val_sym - P_A_val_sym # This is Omega_Canonical for this local frame

    # 1. Create canonical representations for local input values X_L_val_sym and Y_L_val_sym
    X_canon_repr = create_intensity_representation(f"{result_name_prefix_local}_xc")
    Y_canon_repr = create_intensity_representation(f"{result_name_prefix_local}_yc")
    all_defining_assertions.extend([X_canon_repr["constraints"], Y_canon_repr["constraints"]])

    # Logic to set X_canon_repr based on X_L_val_sym, P_A_val_sym, P_B_val_sym, current_S_val_sym
    val_X_for_canon = X_L_val_sym - P_A_val_sym
    all_defining_assertions.append(
        Ite(is_local_ZS_val(X_L_val_sym, P_A_val_sym), 
            X_canon_repr["is_zero"], # And Not Areo, Not Finite implied by ExactlyOne
        Ite(is_local_AS_val(X_L_val_sym, P_B_val_sym),
            And(X_canon_repr["is_areo"], Equals(X_canon_repr["val"], current_S_val_sym)),
            And(X_canon_repr["is_finite"], Equals(X_canon_repr["val"], val_X_for_canon),
                val_X_for_canon > Int(0), val_X_for_canon < current_S_val_sym) # Ensure mapped DFI is valid for canonical
        ))
    )
    # Logic to set Y_canon_repr based on Y_L_val_sym (similar)
    val_Y_for_canon = Y_L_val_sym - P_A_val_sym
    all_defining_assertions.append(
        Ite(is_local_ZS_val(Y_L_val_sym, P_A_val_sym),
            Y_canon_repr["is_zero"],
        Ite(is_local_AS_val(Y_L_val_sym, P_B_val_sym),
            And(Y_canon_repr["is_areo"], Equals(Y_canon_repr["val"], current_S_val_sym)),
            And(Y_canon_repr["is_finite"], Equals(Y_canon_repr["val"], val_Y_for_canon),
                val_Y_for_canon > Int(0), val_Y_for_canon < current_S_val_sym)
        ))
    )
    
    # 2. Perform operation in the canonical frame [0,S]
    Res_canon_repr = op_canonical_result_definer(
        X_canon_repr, Y_canon_repr, 
        f"{result_name_prefix_local}_resc", 
        current_S_val_sym # Pass the span S as the Omega for the canonical operation
    )
    all_defining_assertions.append(Res_canon_repr["definition"])
    all_defining_assertions.append(Res_canon_repr["constraints"])

    # 3. Define the local result SMT integer value based on the canonical result representation
    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    
    local_result_value_formula = Ite(Res_canon_repr["is_zero"], P_A_val_sym,
                                 Ite(Res_canon_repr["is_areo"], P_B_val_sym,
                                     P_A_val_sym + Res_canon_repr["val"]
                                 ))
    all_defining_assertions.append(Equals(Res_L_val_sym, local_result_value_formula))

    return {
        "val_L_sym": Res_L_val_sym, 
        "defining_assertions": all_defining_assertions
    }

# --- Phase 4: Generic Property Prover ---
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
                    print(f"  Unknown model var type or structure: {var_item}")
            
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Relativistic DFI Haven Integrity Test ======\n")

    PA_val = Symbol("PA_val", solver_INT_TYPE)
    PB_val = Symbol("PB_val", solver_INT_TYPE)
    S_val = Symbol("S_val", solver_INT_TYPE)

    # Symbolic local DFI values (their raw integer values)
    La_DFI_val = Symbol("La_DFI_val", solver_INT_TYPE)
    Lb_DFI_val = Symbol("Lb_DFI_val", solver_INT_TYPE)
    Lc_DFI_val = Symbol("Lc_DFI_val", solver_INT_TYPE)

    # Local Pole values (not symbols, but direct SMT values for P_A or P_B)
    # P_A_pole_val will be PA_val
    # P_B_pole_val will be PB_val

    for current_span_py in OMEGA_VARIANTS_TO_TEST_WITH_S2:
        s = Solver(name="z3")
        current_S_smt = Int(current_span_py)
        print(f"\n\n===== TESTING DFI HAVEN INTEGRITY WITH LOCAL SPAN S = {current_span_py} =====\n")

        # Define P_A and P_B for this span
        s.add_assertion(Equals(PA_val, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(S_val, current_S_smt))
        s.add_assertion(S_val > Int(0)) 
        s.add_assertion(Equals(PB_val, PA_val + S_val))
        
        # Common assertions for each test block
        base_setup_for_laws = [
            is_local_DFI_val(La_DFI_val, PA_val, PB_val),
            is_local_DFI_val(Lb_DFI_val, PA_val, PB_val),
            is_local_DFI_val(Lc_DFI_val, PA_val, PB_val)
        ]
        # Add validity constraints for La_DFI_val, Lb_DFI_val, Lc_DFI_val themselves (P_A <= V <= P_B)
        # is_local_DFI already implies P_A < V < P_B, which is stricter and correct for DFI.

        # --- Test HIB-1: Conditional Additive Associativity with One Pole (Result forced to DFI_L) ---
        print(f"--- HIB-1: Additive Associativity with Poles (S={current_span_py}, Result in DFI_L) ---")
        
        test_cases_add_assoc = [
            ("ZS_L + (Lb_DFI + Lc_DFI)", PA_val, Lb_DFI_val, Lc_DFI_val), # (P_A + Lb) + Lc vs P_A + (Lb + Lc)
            ("(La_DFI + ZS_L) + Lc_DFI", La_DFI_val, PA_val, Lc_DFI_val), # (La + P_A) + Lc vs La + (P_A + Lc)
            ("(La_DFI + Lb_DFI) + ZS_L", La_DFI_val, Lb_DFI_val, PA_val), # (La + Lb) + P_A vs La + (Lb + P_A)
            ("AS_L + (Lb_DFI + Lc_DFI)", PB_val, Lb_DFI_val, Lc_DFI_val), # (P_B + Lb) + Lc vs P_B + (Lb + Lc)
            ("(La_DFI + AS_L) + Lc_DFI", La_DFI_val, PB_val, Lc_DFI_val), # (La + P_B) + Lc vs La + (P_B + Lc)
            ("(La_DFI + Lb_DFI) + AS_L", La_DFI_val, Lb_DFI_val, PB_val), # (La + Lb) + P_B vs La + (Lb + P_B)
        ]

        for desc, op_a_val, op_b_val, op_c_val in test_cases_add_assoc:
            s.push()
            s.add_assertions(base_setup_for_laws) # Ensure DFIs used are valid DFIs

            # Define operations ensuring all intermediates and final results are DFI_L
            sum_ab_L_dict = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, op_a_val, op_b_val, PA_val, PB_val, f"hib1_sum_ab_{desc.replace(' ','_')}")
            lhs_L_dict = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, sum_ab_L_dict["val_L_sym"], op_c_val, PA_val, PB_val, f"hib1_lhs_{desc.replace(' ','_')}")
            
            sum_bc_L_dict = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, op_b_val, op_c_val, PA_val, PB_val, f"hib1_sum_bc_{desc.replace(' ','_')}")
            rhs_L_dict = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, op_a_val, sum_bc_L_dict["val_L_sym"], PA_val, PB_val, f"hib1_rhs_{desc.replace(' ','_')}")

            all_op_definitions = sum_ab_L_dict["defining_assertions"] + lhs_L_dict["defining_assertions"] + \
                                 sum_bc_L_dict["defining_assertions"] + rhs_L_dict["defining_assertions"]
            
            dfi_haven_results_conds = [
                is_local_DFI_val(sum_ab_L_dict["val_L_sym"], PA_val, PB_val),
                is_local_DFI_val(lhs_L_dict["val_L_sym"], PA_val, PB_val),
                is_local_DFI_val(sum_bc_L_dict["val_L_sym"], PA_val, PB_val),
                is_local_DFI_val(rhs_L_dict["val_L_sym"], PA_val, PB_val)
            ]
            
            property_to_test = avc_equiv_local_val(lhs_L_dict["val_L_sym"], rhs_L_dict["val_L_sym"], PA_val, PB_val)
            
            model_vars = [PA_val, PB_val, S_val, La_DFI_val, Lb_DFI_val, Lc_DFI_val, # Primary DFIs
                          op_a_val, op_b_val, op_c_val, # Actual operands if poles are involved
                          sum_ab_L_dict["val_L_sym"], lhs_L_dict["val_L_sym"], 
                          sum_bc_L_dict["val_L_sym"], rhs_L_dict["val_L_sym"]]

            prove_or_find_counterexample(s, f"HIB-1 Add Assoc: {desc} (S={current_span_py})", 
                                         all_op_definitions + dfi_haven_results_conds, 
                                         property_to_test, model_vars_to_print=model_vars)
            s.pop()

        # --- Test HIB-2: Conditional Distributivity with One Pole (Result forced to DFI_L) ---
        print(f"\n--- HIB-2: Distributivity with Poles (S={current_span_py}, Result in DFI_L) ---")
        
        # Case 2.1: ZS_L * (Lb_DFI + Lc_DFI) ~ (ZS_L * Lb_DFI) + (ZS_L * Lc_DFI)
        s.push()
        s.add_assertions(base_setup_for_laws)
        op_a_val_21 = PA_val # ZS_L
        op_b_val_21 = Lb_DFI_val
        op_c_val_21 = Lc_DFI_val

        # LHS: op_a_val_21 * (op_b_val_21 + op_c_val_21)
        sum_bc_L_21 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, op_b_val_21, op_c_val_21, PA_val, PB_val, "hib21_sum_bc")
        lhs_L_21 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_21, sum_bc_L_21["val_L_sym"], PA_val, PB_val, "hib21_lhs")

        # RHS: (op_a_val_21 * op_b_val_21) + (op_a_val_21 * op_c_val_21)
        prod_ab_L_21 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_21, op_b_val_21, PA_val, PB_val, "hib21_prod_ab")
        prod_ac_L_21 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_21, op_c_val_21, PA_val, PB_val, "hib21_prod_ac")
        rhs_L_21 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ab_L_21["val_L_sym"], prod_ac_L_21["val_L_sym"], PA_val, PB_val, "hib21_rhs")

        all_op_defs_21 = sum_bc_L_21["defining_assertions"] + lhs_L_21["defining_assertions"] + \
                         prod_ab_L_21["defining_assertions"] + prod_ac_L_21["defining_assertions"] + \
                         rhs_L_21["defining_assertions"]
        
        dfi_haven_res_conds_21 = [ # All results and key intermediates must be DFI_L
            is_local_DFI_val(sum_bc_L_21["val_L_sym"], PA_val, PB_val), 
            is_local_DFI_val(lhs_L_21["val_L_sym"], PA_val, PB_val),
            # For ZS_L * X, result is ZS_L, so it cannot be DFI_L. This setup will be UNSAT if ZS_L is op_a.
            # This implies such a DFI Haven condition is too strict if a pole is involved that annihilates/absorbs.
            # The definition of DFI Haven needs to be carefully applied.
            # Let's test if the law holds if the FINAL LHS and RHS are DFI_L.
            # And if inputs Lb, Lc are DFI_L.
        ]
        # If op_a_val_21 is PA_val (ZS_L):
        # LHS: PA_val * (Lb_DFI + Lc_DFI). If sum is DFI_S, then PA_val * DFI_S -> PA_val.
        # RHS: (PA_val * Lb_DFI) + (PA_val * Lc_DFI) -> PA_val + PA_val -> PA_val.
        # So PA_val ~ PA_val. This should hold.
        # The constraint "result must be DFI_L" makes this impossible if a ZS_L factor results in ZS_L.
        # We test the law, and THEN check if LHS/RHS are DFI.

        # Revised: Test the law. If it holds, separately check kinds if needed.
        # DFI Haven means all terms are in DFI, so inputs a,b,c are DFI for it to be strict DFI haven.
        # For these HIB tests, one input IS a pole. So it's not a strict DFI Haven test.
        # It tests if standard laws hold when poles interact but results are forced back to DFI.
        # Thus, dfi_haven_res_conds_21 needs to apply only to the *final* LHS and RHS and specific intermediates.

        # For Case 2.1: ZS_L * (Lb_DFI + Lc_DFI) ~ (ZS_L * Lb_DFI) + (ZS_L * Lc_DFI)
        # Lb_DFI, Lc_DFI must be DFI_L. Sum Lb+Lc must be DFI_L. Prod ZS*Lb must be DFI_L (impossible, it's ZS_L).
        # This test needs reformulation if we force DFI results.

        # Let's redefine HIB tests: we constrain inputs (some poles, some DFIs)
        # and test the law. We only constrain the FINAL LHS and RHS to be DFI_L.
        # This explores if laws hold IF poles interact but overall outcome is DFI.

        dfi_final_results_conds_21 = [
             is_local_DFI_val(sum_bc_L_21["val_L_sym"], PA_val, PB_val), # sum of two DFIs must be DFI
             is_local_DFI_val(lhs_L_21["val_L_sym"], PA_val, PB_val),
             # prod_ab_L_21 (ZS_L * Lb_DFI) will be ZS_L, so it cannot be DFI. This test as formulated will be UNSAT.
             # prod_ac_L_21 (ZS_L * Lc_DFI) will be ZS_L.
             # rhs_L_21 (ZS_L + ZS_L) will be ZS_L.
             # So we'd be testing if DFI_L (from LHS) ~ ZS_L (from RHS), which will be false unless specific setup.
             # This highlights that forcing DFI results with pole inputs is very restrictive.
        ]
        # A more meaningful test of distributivity with poles is without forcing results into DFI unless natural.
        # The original DFI Haven test (L5 in previous script) was for a,b,c all DFI. That should remain.
        # For these HIB tests, let's remove the strict DFI_L constraint on all intermediates/results
        # and just test if the law holds for the given pole/DFI inputs.
        
        property_21 = avc_equiv_local_val(lhs_L_21["val_L_sym"], rhs_L_21["val_L_sym"], PA_val, PB_val)
        model_vars_21 = [PA_val, PB_val, S_val, Lb_DFI_val, Lc_DFI_val,
                         sum_bc_L_21["val_L_sym"], lhs_L_21["val_L_sym"],
                         prod_ab_L_21["val_L_sym"], prod_ac_L_21["val_L_sym"], rhs_L_21["val_L_sym"]]

        prove_or_find_counterexample(s, f"HIB-2.1 Distrib: ZS_L*(Lb_DFI+Lc_DFI) (S={current_span_py})",
                                     base_setup_for_laws[1:] + all_op_defs_21, # Lb,Lc are DFIs, op_a is PA_val
                                     property_21, model_vars_to_print=model_vars_21)
        s.pop()

        # Case 2.2: AS_L * (Lb_DFI + Lc_DFI) ~ (AS_L * Lb_DFI) + (AS_L * Lc_DFI)
        s.push()
        s.add_assertions(base_setup_for_laws)
        op_a_val_22 = PB_val # AS_L
        op_b_val_22 = Lb_DFI_val
        op_c_val_22 = Lc_DFI_val

        sum_bc_L_22 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, op_b_val_22, op_c_val_22, PA_val, PB_val, "hib22_sum_bc")
        lhs_L_22 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_22, sum_bc_L_22["val_L_sym"], PA_val, PB_val, "hib22_lhs")
        prod_ab_L_22 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_22, op_b_val_22, PA_val, PB_val, "hib22_prod_ab")
        prod_ac_L_22 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_22, op_c_val_22, PA_val, PB_val, "hib22_prod_ac")
        rhs_L_22 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ab_L_22["val_L_sym"], prod_ac_L_22["val_L_sym"], PA_val, PB_val, "hib22_rhs")
        all_op_defs_22 = sum_bc_L_22["defining_assertions"] + lhs_L_22["defining_assertions"] + \
                         prod_ab_L_22["defining_assertions"] + prod_ac_L_22["defining_assertions"] + \
                         rhs_L_22["defining_assertions"]
        property_22 = avc_equiv_local_val(lhs_L_22["val_L_sym"], rhs_L_22["val_L_sym"], PA_val, PB_val)
        model_vars_22 = [PA_val, PB_val, S_val, Lb_DFI_val, Lc_DFI_val,
                         sum_bc_L_22["val_L_sym"], lhs_L_22["val_L_sym"],
                         prod_ab_L_22["val_L_sym"], prod_ac_L_22["val_L_sym"], rhs_L_22["val_L_sym"]]
        prove_or_find_counterexample(s, f"HIB-2.2 Distrib: AS_L*(Lb_DFI+Lc_DFI) (S={current_span_py})",
                                     base_setup_for_laws[1:] + all_op_defs_22, # Lb,Lc are DFIs, op_a is PB_val
                                     property_22, model_vars_to_print=model_vars_22)
        s.pop()
        
        # Case 2.3: La_DFI * (ZS_L + Lc_DFI) ~ (La_DFI * ZS_L) + (La_DFI * Lc_DFI)
        s.push()
        s.add_assertions(base_setup_for_laws)
        op_a_val_23 = La_DFI_val
        op_b_val_23 = PA_val # ZS_L
        op_c_val_23 = Lc_DFI_val

        sum_bc_L_23 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, op_b_val_23, op_c_val_23, PA_val, PB_val, "hib23_sum_bc")
        lhs_L_23 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_23, sum_bc_L_23["val_L_sym"], PA_val, PB_val, "hib23_lhs")
        prod_ab_L_23 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_23, op_b_val_23, PA_val, PB_val, "hib23_prod_ab")
        prod_ac_L_23 = define_local_op_direct_span_result(define_raw_mul_canonical_result, op_a_val_23, op_c_val_23, PA_val, PB_val, "hib23_prod_ac")
        rhs_L_23 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ab_L_23["val_L_sym"], prod_ac_L_23["val_L_sym"], PA_val, PB_val, "hib23_rhs")
        all_op_defs_23 = sum_bc_L_23["defining_assertions"] + lhs_L_23["defining_assertions"] + \
                         prod_ab_L_23["defining_assertions"] + prod_ac_L_23["defining_assertions"] + \
                         rhs_L_23["defining_assertions"]
        property_23 = avc_equiv_local_val(lhs_L_23["val_L_sym"], rhs_L_23["val_L_sym"], PA_val, PB_val)
        model_vars_23 = [PA_val, PB_val, S_val, La_DFI_val, Lc_DFI_val,
                         sum_bc_L_23["val_L_sym"], lhs_L_23["val_L_sym"],
                         prod_ab_L_23["val_L_sym"], prod_ac_L_23["val_L_sym"], rhs_L_23["val_L_sym"]]
        prove_or_find_counterexample(s, f"HIB-2.3 Distrib: La_DFI*(ZS_L+Lc_DFI) (S={current_span_py})",
                                     [base_setup_for_laws[0], base_setup_for_laws[2]] + all_op_defs_23, # La,Lc DFIs
                                     property_23, model_vars_to_print=model_vars_23)
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC Relativistic DFI Haven Integrity Test Complete ======")