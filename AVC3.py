from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE

# --- Phase 1: Foundational Definitions (Copied from AVC1.py) ---
def create_intensity_representation(name_prefix: str):
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

def avc_equiv(i1_repr, i2_repr):
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"])
    finite_finite_equal_val = And(i1_repr["is_finite"], i2_repr["is_finite"], Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Phase 2: Raw Operations Definitions (Copied & Verified from AVC2.py) ---
Omega_max_val_nat = Int(7)

def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder):
    # op_logic_builder returns a single PySMT formula representing the complete definition
    core_logic_formula = op_logic_builder(i1_repr, i2_repr, res_repr)
    return core_logic_formula # Directly return the formula

# --- smart_raw_add ---
def smart_raw_add_logic_builder(i1, i2, res):
    formulas = [] # List to hold parts of the definition
    val_sum = i1["val"] + i2["val"] # Symbolic sum

    # Case: i1 is ZeroState
    formulas.append(Implies(i1["is_zero"],
        Or(
            And(i2["is_zero"],   # i1=ZS, i2=ZS => res=ZS
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            And(i2["is_areo"],    # i1=ZS, i2=AS => res=AS (as per smart_raw_add logic in Lean Phase 4 V1)
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i2["is_finite"],  # i1=ZS, i2=Finite p2 => res=Finite p2
                Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], i2["val"]))
        )
    ))

    # Case: i1 is AreoState
    formulas.append(Implies(i1["is_areo"],
        Or(
            And(i2["is_zero"],   # i1=AS, i2=ZS => res=AS (as per smart_raw_add logic in Lean Phase 4 V1)
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i2["is_areo"],    # i1=AS, i2=AS => res=AS
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i2["is_finite"],  # i1=AS, i2=Finite p2 => res=Finite p2 (as per smart_raw_add logic in Lean Phase 4 V1)
                Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], i2["val"]))
        )
    ))
    
    # Case: i1 is Finite
    #   Subcase: i2 is ZeroState
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), # i1=Finite p1, i2=ZS => res=Finite p1
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
            Equals(res["val"], i1["val"]))
    ))
    #   Subcase: i2 is AreoState
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), # i1=Finite p1, i2=AS => res=Finite p1 (as per smart_raw_add logic in Lean Phase 4 V1)
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
            Equals(res["val"], i1["val"]))
    ))
    #   Subcase: i2 is Finite
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), # i1=Finite p1, i2=Finite p2
        Ite(val_sum >= Omega_max_val_nat,
            # Sum >= Omega_max => res=AreoState
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            # Sum < Omega_max => res=Finite(sum)
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_sum))
        )
    ))
    return And(formulas) # Return a single formula combining all implications

def define_smart_raw_add_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder)
    return res_repr

# --- raw_mul ---
def raw_mul_logic_builder(i1, i2, res):
    formulas = []
    val_prod = i1["val"] * i2["val"] # Symbolic product

    # Case 1 & 2: ZeroState is annihilator (mutually exclusive with other main cases for i1)
    formulas.append(Implies(i1["is_zero"], # If i1 is ZS
        And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) # Result is ZS
    ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), # If i1 not ZS, but i2 is ZS
         And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) # Result is ZS
    ))

    # Case 3: Both AreoState (and neither is ZeroState)
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), 
                                i1["is_areo"], i2["is_areo"]),  # AS * AS => AS
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]))
    ))

    # Case 4: AreoState and Finite (and neither is ZeroState)
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i1["is_areo"], i2["is_finite"]), # AS * F(p)
        Ite(i2["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # res = AS if p.val > 0
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  # res = ZS if p.val is not > 0 (conceptually should not happen if p is valid PosNat)
        )
    ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i2["is_areo"], i1["is_finite"]), # Symmetric: F(p) * AS
        Ite(i1["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # res = AS
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  # res = ZS
        )
    ))

    # Case 5: Both Finite (and neither was ZeroState from Case 1&2, and neither was AreoState with the other)
    # This implies i1["is_finite"] and i2["is_finite"] due to ExactlyOne.
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), # Handles F(p1) * F(p2)
        Ite(val_prod >= Omega_max_val_nat,
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # res = AS
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_prod)) # res = Finite(prod)
        )
    ))
    return And(formulas)

def define_raw_mul_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_mul_logic_builder)
    return res_repr

# --- raw_sub_from_Unio_Areo_aspect ---
def raw_sub_from_Unio_Areo_aspect_logic_builder(i_unio_areo, _i_any, res): # _i_any is ignored
    # If i_unio_areo is ZeroState or AreoState (representing Unio's Areo aspect), result is AreoState.
    # If i_unio_areo is Finite (fallback if used incorrectly for Unio), result is AreoState.
    # This covers all cases for the first argument, ensuring the result is always AreoState.
    return And(Implies(Or(i_unio_areo["is_zero"], i_unio_areo["is_areo"], i_unio_areo["is_finite"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) # Result is always AreoState
    ))

def define_raw_sub_from_Unio_Areo_aspect_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_sub_from_Unio_Areo_aspect_logic_builder)
    return res_repr

# --- Phase 3: Testing Operation Postulates ---

# Corrected Structure for Postulate Testing (v2 from previous script)
def prove_avc_postulate_v2(postulate_name: str,
                        op_result_definer_func,
                        setup_formulas: list, # All formulas to set up inputs and their validity
                        op_arg1_repr, 
                        op_arg2_repr,
                        # Function that takes expected_sym_res and returns list of assertions defining it
                        define_expected_state_func 
                        ):
    print(f"--- Testing Postulate: {postulate_name} ---") # Changed from (v2) for clarity
    with Solver(name="z3") as s:
        # 1. Add assertions from setup_formulas
        #    This list should include validity constraints for all symbolic intensities
        #    involved in this specific postulate (e.g., i1_post, p_sym), and
        #    assertions to fix their kinds/values as per the postulate's premise.
        for formula in setup_formulas:
            s.add_assertion(formula)

        # 2. Define the actual result of the operation using the symbolic inputs
        actual_sym_res = op_result_definer_func(op_arg1_repr, op_arg2_repr, "actual_res_postulate")
        s.add_assertion(actual_sym_res["definition"])  # Assert how actual_sym_res is formed
        s.add_assertion(actual_sym_res["constraints"]) # Actual result must be a valid intensity

        # 3. Define a symbolic intensity that represents the expected outcome's state
        expected_sym_res = create_intensity_representation("expected_res_postulate")
        s.add_assertion(expected_sym_res["constraints"]) # Expected outcome must also be a valid intensity
        
        # Get the list of assertions that define the expected state and add them
        expected_state_assertions = define_expected_state_func(expected_sym_res)
        for assertion in expected_state_assertions:
            s.add_assertion(assertion)
        
        # 4. Assert the negation of the postulate's conclusion:
        #    Actual result is NOT avc_equiv to an intensity with the expected properties.
        s.add_assertion(Not(avc_equiv(actual_sym_res, expected_sym_res)))

        # 5. Check for satisfiability
        result = s.solve()
        if not result:
            print(f"Result: UNSAT. Postulate '{postulate_name}' is PROVED. ✅")
        else:
            print(f"Result: SAT. Postulate '{postulate_name}' FAILED. Counterexample model:")
            # Print model for inputs
            print(f"  Input1 ({op_arg1_repr['name']}): Z={s.get_value(op_arg1_repr['is_zero'])}, A={s.get_value(op_arg1_repr['is_areo'])}, F={s.get_value(op_arg1_repr['is_finite'])}, V={s.get_value(op_arg1_repr['val'])}")
            if op_arg1_repr['name'] != op_arg2_repr['name']: # Avoid double printing if same symbol
                 print(f"  Input2 ({op_arg2_repr['name']}): Z={s.get_value(op_arg2_repr['is_zero'])}, A={s.get_value(op_arg2_repr['is_areo'])}, F={s.get_value(op_arg2_repr['is_finite'])}, V={s.get_value(op_arg2_repr['val'])}")
            # Consider printing other relevant symbolic values from setup_formulas if they are not op_arg1/2
            # For example, if p_sym was used to define a value but wasn't an op_arg directly.
            # This requires passing those symbols to the print block or making it more context-aware.

            print(f"  Actual Result ({actual_sym_res['name']}): Z={s.get_value(actual_sym_res['is_zero'])}, A={s.get_value(actual_sym_res['is_areo'])}, F={s.get_value(actual_sym_res['is_finite'])}, V={s.get_value(actual_sym_res['val'])}")
            print(f"  Expected State ({expected_sym_res['name']}): Z={s.get_value(expected_sym_res['is_zero'])}, A={s.get_value(expected_sym_res['is_areo'])}, F={s.get_value(expected_sym_res['is_finite'])}, V={s.get_value(expected_sym_res['val'])}")
    print("-" * 60)


if __name__ == "__main__":
    print("====== AVC Phase 3: Testing Operation Postulates via Raw Operations ======\n")

    # --- Symbolic Intensities for general use in postulates ---
    i1_post = create_intensity_representation("i1_post")
    i2_post = create_intensity_representation("i2_post")
    # p_sym is used to represent a generic DFI(p) input.
    # Its 'val' will be constrained by specific tests if needed, or remain symbolic.
    p_sym = create_intensity_representation("p_sym_generic") 
    p1_sym = create_intensity_representation("p1_sym_for_DFIs") 
    p2_sym = create_intensity_representation("p2_sym_for_DFIs")

    # --- Postulates for smart_raw_add (conceptually addAVC) ---
    print("--- Testing Postulates for smart_raw_add (addAVC) ---")

    # Test Case 1: addAVC Unio_quot (DFI_AVC p) = DFI_AVC p  (Unio as ZeroState)
    prove_avc_postulate_v2(
        postulate_name="addAVC_Unio(ZS)_DFI(p) = DFI(p)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_zero"], 
            p_sym["constraints"], p_sym["is_finite"] # p_sym.val > 0 is in its constraints
        ],
        op_arg1_repr=i1_post,
        op_arg2_repr=p_sym,
        define_expected_state_func=lambda exp_res: [ # Expected is DFI(p)
            exp_res["is_finite"], 
            Equals(exp_res["val"], p_sym["val"])
        ]
    )

    # Test Case 2: addAVC Unio_quot (DFI_AVC p) = DFI_AVC p  (Unio as AreoState)
    # smart_raw_add for AreoState + Finite p -> Finite p
    prove_avc_postulate_v2(
        postulate_name="addAVC_Unio(AS)_DFI(p) = DFI(p)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_areo"], 
            p_sym["constraints"], p_sym["is_finite"]    
        ],
        op_arg1_repr=i1_post,
        op_arg2_repr=p_sym,
        define_expected_state_func=lambda exp_res: [ # Expected is DFI(p)
            exp_res["is_finite"], 
            Equals(exp_res["val"], p_sym["val"])
        ]
    )

    # Test Case 3: addAVC (DFI_AVC p) Unio_quot = DFI_AVC p (Unio as ZeroState)
    prove_avc_postulate_v2(
        postulate_name="addAVC_DFI(p)_Unio(ZS) = DFI(p)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            p_sym["constraints"], p_sym["is_finite"],    
            i1_post["constraints"], i1_post["is_zero"]   
        ],
        op_arg1_repr=p_sym,
        op_arg2_repr=i1_post,
        define_expected_state_func=lambda exp_res: [ # Expected is DFI(p)
            exp_res["is_finite"],
            Equals(exp_res["val"], p_sym["val"])
        ]
    )
    
    # Test Case 4: addAVC (DFI_AVC p) Unio_quot = DFI_AVC p (Unio as AreoState)
    # smart_raw_add for Finite p + AreoState -> Finite p
    prove_avc_postulate_v2(
        postulate_name="addAVC_DFI(p)_Unio(AS) = DFI(p)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            p_sym["constraints"], p_sym["is_finite"],    
            i1_post["constraints"], i1_post["is_areo"]   
        ],
        op_arg1_repr=p_sym,
        op_arg2_repr=i1_post,
        define_expected_state_func=lambda exp_res: [ # Expected is DFI(p)
            exp_res["is_finite"],
            Equals(exp_res["val"], p_sym["val"])
        ]
    )

    # Test Case 5: addAVC Unio_quot Unio_quot = Unio_quot (ZS + ZS -> ZS)
    prove_avc_postulate_v2(
        postulate_name="addAVC_Unio(ZS)_Unio(ZS) = Unio(ZS)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_zero"],
            i2_post["constraints"], i2_post["is_zero"]
        ],
        op_arg1_repr=i1_post,
        op_arg2_repr=i2_post,
        define_expected_state_func=lambda exp_res: [exp_res["is_zero"]] 
    )
    
    # Test Case 6: addAVC Unio_quot Unio_quot = Unio_quot (AS + AS -> AS)
    prove_avc_postulate_v2(
        postulate_name="addAVC_Unio(AS)_Unio(AS) = Unio(AS)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_areo"],
            i2_post["constraints"], i2_post["is_areo"]
        ],
        op_arg1_repr=i1_post,
        op_arg2_repr=i2_post,
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]] 
    )

    # Test Case 7: addAVC Unio_quot Unio_quot = Unio_quot (ZS + AS -> AS)
    prove_avc_postulate_v2(
        postulate_name="addAVC_Unio(ZS)_Unio(AS) = Unio(AS)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_zero"],
            i2_post["constraints"], i2_post["is_areo"]
        ],
        op_arg1_repr=i1_post,
        op_arg2_repr=i2_post,
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]] 
    )

    # Test Case 8: addAVC_DFIs_to_Unio
    #   p1.val + p2.val >= Omega => addAVC (DFI p1) (DFI p2) = Unio_quot (represented by AreoState)
    p1_val_add_ge = Symbol("p1_val_add_ge_sra", solver_INT_TYPE) # Unique names for symbols per test
    p2_val_add_ge = Symbol("p2_val_add_ge_sra", solver_INT_TYPE)
    prove_avc_postulate_v2(
        postulate_name="addAVC_DFIs_to_Unio (sum >= Omega)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            p1_sym["constraints"], p1_sym["is_finite"], Equals(p1_sym["val"], p1_val_add_ge), p1_val_add_ge > Int(0),
            p2_sym["constraints"], p2_sym["is_finite"], Equals(p2_sym["val"], p2_val_add_ge), p2_val_add_ge > Int(0),
            (p1_val_add_ge + p2_val_add_ge >= Omega_max_val_nat) 
        ],
        op_arg1_repr=p1_sym,
        op_arg2_repr=p2_sym,
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]] 
    )

    # Test Case 9: addAVC_DFIs_to_DFI
    #   p1.val + p2.val < Omega => addAVC (DFI p1) (DFI p2) = DFI (p1.val+p2.val)
    p1_val_add_lt = Symbol("p1_val_add_lt_sra", solver_INT_TYPE)
    p2_val_add_lt = Symbol("p2_val_add_lt_sra", solver_INT_TYPE)
    sum_val_lt = p1_val_add_lt + p2_val_add_lt # This is a PySMT expression
    prove_avc_postulate_v2(
        postulate_name="addAVC_DFIs_to_DFI (sum < Omega)",
        op_result_definer_func=define_smart_raw_add_result,
        setup_formulas=[
            p1_sym["constraints"], p1_sym["is_finite"], Equals(p1_sym["val"], p1_val_add_lt), p1_val_add_lt > Int(0),
            p2_sym["constraints"], p2_sym["is_finite"], Equals(p2_sym["val"], p2_val_add_lt), p2_val_add_lt > Int(0),
            (sum_val_lt < Omega_max_val_nat), 
            (sum_val_lt > Int(0)) # Ensure resulting sum is valid for DFI's PosNat
        ],
        op_arg1_repr=p1_sym,
        op_arg2_repr=p2_sym,
        define_expected_state_func=lambda exp_res: [
            exp_res["is_finite"],
            Equals(exp_res["val"], sum_val_lt) # Check value against the symbolic sum
        ]
    )
    
    # --- Postulates for raw_mul (conceptually mulAVC) ---
    print("\n--- Testing Postulates for raw_mul (mulAVC) ---")
    # Test Case 10: mulAVC Unio_quot (DFI_AVC p) = Unio_quot (Unio as ZS -> ZS)
    prove_avc_postulate_v2(
        postulate_name="mulAVC_Unio(ZS)_DFI(p) = Unio(ZS)",
        op_result_definer_func=define_raw_mul_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_zero"], 
            p_sym["constraints"], p_sym["is_finite"]    
        ],
        op_arg1_repr=i1_post,
        op_arg2_repr=p_sym,
        define_expected_state_func=lambda exp_res: [exp_res["is_zero"]] 
    )

    # Test Case 11: mulAVC Unio_quot (DFI_AVC p) = Unio_quot (Unio as AS, p.val > 0 -> AS)
    p_val_mul_gt0 = Symbol("p_val_mul_gt0_rm", solver_INT_TYPE)
    prove_avc_postulate_v2(
        postulate_name="mulAVC_Unio(AS)_DFI(p>0) = Unio(AS)",
        op_result_definer_func=define_raw_mul_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_areo"], 
            p_sym["constraints"], p_sym["is_finite"], Equals(p_sym["val"], p_val_mul_gt0), p_val_mul_gt0 > Int(0)
        ],
        op_arg1_repr=i1_post,
        op_arg2_repr=p_sym,
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]] 
    )
    
    # Test Case 11b: mulAVC Unio_quot (DFI_AVC p) = Unio_quot (Unio as AS, p.val is NOT > 0 -> ZS)
    # This case relies on p_sym.val being forced to something not > 0, which contradicts p_sym["is_finite"]'s PosNat constraint.
    # The raw_mul logic `if p.val > 0 then areoState else zeroState` combined with `p.val > 0` from `is_finite`
    # means the `else zeroState` branch for `areoState * finite p` should be unreachable if p is a valid DFI.
    # Let's test if the SMT solver can find an issue if we try to force p.val to be non-positive,
    # which should make the setup UNSAT if p_sym is also asserted to be finite.
    # This test is more about the consistency of raw_mul's definition with PosNat.
    print("  Testing consistency: mulAVC_Unio(AS)_DFI(p_not_gt_0) (should be hard to make valid)")
    with Solver(name="z3") as s_consistency_check:
        s_consistency_check.add_assertion(i1_post["constraints"])
        s_consistency_check.add_assertion(i1_post["is_areo"])
        s_consistency_check.add_assertion(p_sym["constraints"]) # Includes p_sym.val > 0 if p_sym.is_finite
        s_consistency_check.add_assertion(p_sym["is_finite"])   # Force p_sym to be finite
        s_consistency_check.add_assertion(Not(p_sym["val"] > Int(0))) # Try to force p_sym.val to be not > 0
        
        # If the above is SAT, it means our PosNat constraint isn't strong enough or there's a loophole.
        # It should be UNSAT because p_sym["constraints"] (via Implies(p_sym.is_finite, p_sym.val > 0))
        # and p_sym.is_finite and Not(p_sym.val > 0) is a contradiction.
        if not s_consistency_check.solve():
             print("    Consistency check for AS * F(p_not_gt_0) setup: Input setup is UNSAT as expected (good).")
        else:
             print("    Consistency check for AS * F(p_not_gt_0) setup: Input setup is SAT (potential issue with PosNat logic).")


    # Test Case 12: mulAVC (DFI_AVC p) Unio_quot = Unio_quot (Unio as ZS -> ZS)
    prove_avc_postulate_v2(
        postulate_name="mulAVC_DFI(p)_Unio(ZS) = Unio(ZS)",
        op_result_definer_func=define_raw_mul_result,
        setup_formulas=[
            p_sym["constraints"], p_sym["is_finite"],
            i1_post["constraints"], i1_post["is_zero"]
        ],
        op_arg1_repr=p_sym,
        op_arg2_repr=i1_post,
        define_expected_state_func=lambda exp_res: [exp_res["is_zero"]]
    )

    # Test Case 13: mulAVC Unio_quot Unio_quot = Unio_quot (ZS * ZS -> ZS)
    prove_avc_postulate_v2(
        postulate_name="mulAVC_Unio(ZS)_Unio(ZS) = Unio(ZS)",
        op_result_definer_func=define_raw_mul_result,
        setup_formulas=[i1_post["constraints"], i1_post["is_zero"], i2_post["constraints"], i2_post["is_zero"]],
        op_arg1_repr=i1_post, op_arg2_repr=i2_post,
        define_expected_state_func=lambda exp_res: [exp_res["is_zero"]]
    )
    
    # Test Case 14: mulAVC Unio_quot Unio_quot = Unio_quot (AS * AS -> AS)
    prove_avc_postulate_v2(
        postulate_name="mulAVC_Unio(AS)_Unio(AS) = Unio(AS)",
        op_result_definer_func=define_raw_mul_result,
        setup_formulas=[i1_post["constraints"], i1_post["is_areo"], i2_post["constraints"], i2_post["is_areo"]],
        op_arg1_repr=i1_post, op_arg2_repr=i2_post,
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]]
    )

    # Test Case 15: mulAVC_DFIs_to_Unio
    p1_val_mul_ge = Symbol("p1_val_mul_ge_rm", solver_INT_TYPE)
    p2_val_mul_ge = Symbol("p2_val_mul_ge_rm", solver_INT_TYPE)
    prove_avc_postulate_v2(
        postulate_name="mulAVC_DFIs_to_Unio (prod >= Omega)",
        op_result_definer_func=define_raw_mul_result,
        setup_formulas=[
            p1_sym["constraints"], p1_sym["is_finite"], Equals(p1_sym["val"], p1_val_mul_ge), p1_val_mul_ge > Int(0),
            p2_sym["constraints"], p2_sym["is_finite"], Equals(p2_sym["val"], p2_val_mul_ge), p2_val_mul_ge > Int(0),
            (p1_val_mul_ge * p2_val_mul_ge >= Omega_max_val_nat)
        ],
        op_arg1_repr=p1_sym, op_arg2_repr=p2_sym,
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]]
    )

    # Test Case 16: mulAVC_DFIs_to_DFI
    p1_val_mul_lt = Symbol("p1_val_mul_lt_rm", solver_INT_TYPE)
    p2_val_mul_lt = Symbol("p2_val_mul_lt_rm", solver_INT_TYPE)
    prod_val_lt = p1_val_mul_lt * p2_val_mul_lt
    prove_avc_postulate_v2(
        postulate_name="mulAVC_DFIs_to_DFI (prod < Omega and prod > 0)",
        op_result_definer_func=define_raw_mul_result,
        setup_formulas=[
            p1_sym["constraints"], p1_sym["is_finite"], Equals(p1_sym["val"], p1_val_mul_lt), p1_val_mul_lt > Int(0),
            p2_sym["constraints"], p2_sym["is_finite"], Equals(p2_sym["val"], p2_val_mul_lt), p2_val_mul_lt > Int(0),
            (prod_val_lt < Omega_max_val_nat),
            (prod_val_lt > Int(0)) # Explicitly assert resulting product is > 0 for DFI
        ],
        op_arg1_repr=p1_sym, op_arg2_repr=p2_sym,
        define_expected_state_func=lambda exp_res: [
            exp_res["is_finite"], Equals(exp_res["val"], prod_val_lt)
        ]
    )

    # --- Postulates for raw_sub_from_Unio_Areo_aspect (sub_from_Unio_Areo_aspect_AVC) ---
    print("\n--- Testing Postulates for raw_sub_from_Unio_Areo_aspect (subAVC) ---")
    # Test Case 17: subAVC Unio_quot (DFI_AVC p) = Unio_quot (Unio as ZS -> AS)
    prove_avc_postulate_v2(
        postulate_name="subAVC_Unio(ZS)_DFI(p) = Unio(AS)",
        op_result_definer_func=define_raw_sub_from_Unio_Areo_aspect_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_zero"], 
            p_sym["constraints"], p_sym["is_finite"]    
        ],
        op_arg1_repr=i1_post, op_arg2_repr=p_sym, # p_sym is the ignored second argument
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]] 
    )

    # Test Case 18: subAVC Unio_quot (DFI_AVC p) = Unio_quot (Unio as AS -> AS)
    prove_avc_postulate_v2(
        postulate_name="subAVC_Unio(AS)_DFI(p) = Unio(AS)",
        op_result_definer_func=define_raw_sub_from_Unio_Areo_aspect_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_areo"], 
            p_sym["constraints"], p_sym["is_finite"]    
        ],
        op_arg1_repr=i1_post, op_arg2_repr=p_sym,
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]] 
    )
    
    # Test Case 19: subAVC Unio_quot Unio_quot = Unio_quot (Unio as ZS, second Unio as ZS -> AS)
    prove_avc_postulate_v2(
        postulate_name="subAVC_Unio(ZS)_Unio(ZS) = Unio(AS)",
        op_result_definer_func=define_raw_sub_from_Unio_Areo_aspect_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_zero"], 
            i2_post["constraints"], i2_post["is_zero"] 
        ],
        op_arg1_repr=i1_post, op_arg2_repr=i2_post, # i2_post is ignored
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]] 
    )
    
    # Test Case 20: subAVC Unio_quot Unio_quot = Unio_quot (Unio as AS, second Unio as AS -> AS)
    prove_avc_postulate_v2(
        postulate_name="subAVC_Unio(AS)_Unio(AS) = Unio(AS)",
        op_result_definer_func=define_raw_sub_from_Unio_Areo_aspect_result,
        setup_formulas=[
            i1_post["constraints"], i1_post["is_areo"], 
            i2_post["constraints"], i2_post["is_areo"] 
        ],
        op_arg1_repr=i1_post, op_arg2_repr=i2_post, # i2_post is ignored
        define_expected_state_func=lambda exp_res: [exp_res["is_areo"]] 
    )

    print("\n====== All Phase 3 rigorous postulate tests complete. ======")
    print("If all results above show 'PROVED', the raw operations correctly implement")
    print("the conceptual postulates of the AVC model for lifted operations.")

"""

**Key Corrections and Refinements in this Version:**

1.  **`build_result_definition` Return**: Changed to return the single `And(formulas)` directly, as the `op_logic_builder` functions now correctly return a single `And` formula.
2.  **`smart_raw_add_logic_builder` for AreoState + Finite**:
    * The logic `AreoState + Finite p2 => Finite p2` and `Finite p1 + AreoState => Finite p1` is now correctly implemented as per the Lean `smart_raw_add` definition (Phase 4 V1 script). This means `smart_raw_add` does *not* have Areo absorption for these cases; it treats Areo/Zero (as Unio) as an identity for addition with Finites.
3.  **`raw_mul_logic_builder` Case Structure**:
    * The logic for `raw_mul` was refined to handle the ZeroState annihilator cases first and more explicitly, then the AreoState cases (ensuring inputs are not ZeroState), and finally the Finite * Finite case. This makes the mutually exclusive nature of the conceptual cases clearer in the PySMT `Implies` structure.
    * The condition `if p.val > 0` for `AreoState * finite p` is important. Since `p` comes from a `finite P` where `P` is `PosNat`, `p.val` is already guaranteed to be `> 0` by `p_sym["constraints"]`. The `Ite` might seem redundant for valid DFIs but correctly reflects the Lean `raw_mul` definition. The consistency check (Test Case 11b) is designed to probe this.
4.  **`prove_avc_postulate_v2` Refinements**:
    * The comments are clearer about what `setup_formulas` should contain.
    * The printing of the model in case of failure is slightly simplified but still aims to provide useful info.
5.  **Test Case Logic for `addAVC_Unio_DFI` (Cases 1-4)**:
    * The `define_expected_state_func` correctly asserts that the `exp_res` (expected symbolic result) `is_finite` and its `val` is equal to `p_sym["val"]`.
6.  **Test Case Logic for `addAVC_Unio_Unio` (Cases 5-7)**:
    * The expected result is Unio. If the inputs define Unio as ZS+ZS, expected is ZS. If AS+AS, expected is AS. If ZS+AS, `smart_raw_add` results in AS, so expected is AS.
7.  **Test Case Logic for `addAVC_DFIs_to_Unio/DFI` (Cases 8, 9)**:
    * Unique symbolic integers (`p1_val_add_ge`, `p2_val_add_ge_sra`, etc.) are used for the values of `p1_sym` and `p2_sym` in these tests to avoid clashes if the same `p1_sym`, `p2_sym` were reused with different value constraints.
    * The premise (e.g., `sum >= Omega_max_val_nat`) is explicitly added to `setup_formulas`.
    * For "to_DFI", the condition `sum_val_lt > Int(0)` is also added to the setup, as the resulting DFI must have a positive value. This is guaranteed by `PosNat.val_add_pos` in Lean, and here we assert it to ensure the SMT problem is well-constrained for the expected DFI outcome.
8.  **Test Case Logic for `raw_mul` Postulates (Cases 10-16)**:
    * Similar structure, carefully setting up Unio as ZS or AS.
    * **Test Case 11b (Consistency Check)**: This is a special test. `raw_mul` has `AreoState * finite p => if p.val > 0 then AreoState else ZeroState`. If `p` is a DFI, `p.val` *must* be `> 0`. This test tries to assert `p.val` is *not* `> 0` while `p` is also `is_finite`. This setup *should be UNSAT* because it contradicts the `PosNat` constraint inherent in `p_sym["is_finite"]`. If it were SAT, it would indicate a flaw in how `PosNat` is enforced.
    * For `mulAVC_DFIs_to_DFI` (Case 16), the condition `prod_val_lt > Int(0)` is added to the setup, as the product must be positive to form a DFI.
9.  **Test Case Logic for `raw_sub` Postulates (Cases 17-20)**:
    * The `raw_sub_from_Unio_Areo_aspect` operation always results in `AreoState` if the first argument represents Unio (either ZS or AS). The second argument is ignored. The tests reflect this.

This version is much more detailed in its case analysis for the operation logic builders and in the setup for each postulate test. It's ready for you to run. We'll be looking for "PROVED. ✅" on all tests. """