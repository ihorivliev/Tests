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
Omega_max_val_nat = Int(7) # Crucial for this example

def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder):
    core_logic_formula = op_logic_builder(i1_repr, i2_repr, res_repr)
    return core_logic_formula

# --- smart_raw_add (Copied from AVC3.py, matches Lean Phase 4 V1 smart_raw_add) ---
def smart_raw_add_logic_builder(i1, i2, res):
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])))))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # AS + ZS -> AS
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # AS + AS -> AS
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))))) # AS + F(p) -> F(p)
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) # F(p) + ZS -> F(p)
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) # F(p) + AS -> F(p)
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), Ite(val_sum >= Omega_max_val_nat,
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)))))
    return And(formulas)

def define_smart_raw_add_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder)
    return res_repr

# --- Helper to assert an intensity is a specific concrete Finite value ---
def assert_is_concrete_finite(solver, intensity_repr, value: int, name_for_debug=""):
    """Adds assertions to the solver that intensity_repr is Finite with the given value."""
    solver.add_assertion(intensity_repr["constraints"]) # Must be valid
    solver.add_assertion(intensity_repr["is_finite"])
    solver.add_assertion(Not(intensity_repr["is_zero"]))
    solver.add_assertion(Not(intensity_repr["is_areo"]))
    solver.add_assertion(Equals(intensity_repr["val"], Int(value)))
    if value <= 0:
        # This should ideally make the problem UNSAT if constraints are also asserted,
        # because a Finite intensity must have val > 0.
        print(f"WARNING for {name_for_debug if name_for_debug else intensity_repr['name']}: assert_is_concrete_finite called with non-positive value {value}. This will conflict with PosNat constraint.")

# --- Helper to assert an intensity is ZeroState ---
def assert_is_concrete_zerostate(solver, intensity_repr):
    solver.add_assertion(intensity_repr["constraints"])
    solver.add_assertion(intensity_repr["is_zero"])
    solver.add_assertion(Not(intensity_repr["is_areo"]))
    solver.add_assertion(Not(intensity_repr["is_finite"]))

# --- Helper to assert an intensity is AreoState ---
def assert_is_concrete_areostate(solver, intensity_repr):
    solver.add_assertion(intensity_repr["constraints"])
    solver.add_assertion(intensity_repr["is_areo"])
    solver.add_assertion(Not(intensity_repr["is_zero"]))
    solver.add_assertion(Not(intensity_repr["is_finite"]))


if __name__ == "__main__":
    print("====== AVC Phase 4: Proving Non-Associativity Example ======\n")

    # --- Define symbolic intensities for the example ---
    # These will be constrained to specific concrete values for this test.
    I1_sym = create_intensity_representation("I1_assoc_ex")
    I2_sym = create_intensity_representation("I2_assoc_ex")
    I3_sym = create_intensity_representation("I3_assoc_ex")

    # --- Values from the non-associativity example ---
    # (I1_val_assoc : Nat := 4)
    # (I2_val_assoc : Nat := 4)
    # (I3_val_assoc : Nat := 1)
    # Omega_max_val_nat is 7

    # --- Step 1: Calculate LHS = (I1 + I2) + I3 and prove its expected value ---
    print("--- Calculating and Verifying LHS: (F(4) + F(4)) + F(1) ---")
    # Expected: F(4)+F(4) = F(8) -> AreoState. AreoState + F(1) -> F(1).
    
    with Solver(name="z3") as s_lhs:
        # 1a. Assert concrete values for I1, I2, I3
        assert_is_concrete_finite(s_lhs, I1_sym, 4, "I1_sym_lhs")
        assert_is_concrete_finite(s_lhs, I2_sym, 4, "I2_sym_lhs")
        assert_is_concrete_finite(s_lhs, I3_sym, 1, "I3_sym_lhs")

        # 1b. Symbolically compute Intermediate1 = smart_raw_add(I1_sym, I2_sym)
        Intermediate1_lhs_sym = define_smart_raw_add_result(I1_sym, I2_sym, "Int1_lhs_res")
        s_lhs.add_assertion(Intermediate1_lhs_sym["definition"])
        s_lhs.add_assertion(Intermediate1_lhs_sym["constraints"]) # Result must be valid

        # 1c. Symbolically compute LHS_Result_sym = smart_raw_add(Intermediate1_lhs_sym, I3_sym)
        LHS_Result_sym = define_smart_raw_add_result(Intermediate1_lhs_sym, I3_sym, "LHS_final_res")
        s_lhs.add_assertion(LHS_Result_sym["definition"])
        s_lhs.add_assertion(LHS_Result_sym["constraints"]) # Final result must be valid

        # 1d. Define the expected result for LHS: Finite(1)
        Expected_LHS_sym = create_intensity_representation("Expected_LHS_is_F1")
        assert_is_concrete_finite(s_lhs, Expected_LHS_sym, 1, "Expected_LHS_sym")
        
        # 1e. Prove LHS_Result_sym is avc_equiv to Expected_LHS_sym
        #     by showing NOT avc_equiv(LHS_Result_sym, Expected_LHS_sym) is UNSAT
        s_lhs.add_assertion(Not(avc_equiv(LHS_Result_sym, Expected_LHS_sym)))

        result_lhs = s_lhs.solve()
        if not result_lhs:
            print("Result: UNSAT. LHS = (F(4)+F(4))+F(1) is PROVED to be avc_equiv to F(1). ✅")
        else:
            print("Result: SAT. LHS verification FAILED. Counterexample model:")
            print(f"  I1_sym: Z={s_lhs.get_value(I1_sym['is_zero'])}, A={s_lhs.get_value(I1_sym['is_areo'])}, F={s_lhs.get_value(I1_sym['is_finite'])}, V={s_lhs.get_value(I1_sym['val'])}")
            print(f"  I2_sym: Z={s_lhs.get_value(I2_sym['is_zero'])}, A={s_lhs.get_value(I2_sym['is_areo'])}, F={s_lhs.get_value(I2_sym['is_finite'])}, V={s_lhs.get_value(I2_sym['val'])}")
            print(f"  I3_sym: Z={s_lhs.get_value(I3_sym['is_zero'])}, A={s_lhs.get_value(I3_sym['is_areo'])}, F={s_lhs.get_value(I3_sym['is_finite'])}, V={s_lhs.get_value(I3_sym['val'])}")
            print(f"  Int1_lhs: Z={s_lhs.get_value(Intermediate1_lhs_sym['is_zero'])}, A={s_lhs.get_value(Intermediate1_lhs_sym['is_areo'])}, F={s_lhs.get_value(Intermediate1_lhs_sym['is_finite'])}, V={s_lhs.get_value(Intermediate1_lhs_sym['val'])}")
            print(f"  LHS_Result: Z={s_lhs.get_value(LHS_Result_sym['is_zero'])}, A={s_lhs.get_value(LHS_Result_sym['is_areo'])}, F={s_lhs.get_value(LHS_Result_sym['is_finite'])}, V={s_lhs.get_value(LHS_Result_sym['val'])}")
            print(f"  Expected_LHS: Z={s_lhs.get_value(Expected_LHS_sym['is_zero'])}, A={s_lhs.get_value(Expected_LHS_sym['is_areo'])}, F={s_lhs.get_value(Expected_LHS_sym['is_finite'])}, V={s_lhs.get_value(Expected_LHS_sym['val'])}")
    print("-" * 60)

    # --- Step 2: Calculate RHS = I1 + (I2 + I3) and prove its expected value ---
    print("--- Calculating and Verifying RHS: F(4) + (F(4) + F(1)) ---")
    # Expected: F(4)+F(1) = F(5). F(4)+F(5) = F(9) -> AreoState.
    
    with Solver(name="z3") as s_rhs:
        # 2a. Assert concrete values for I1, I2, I3
        assert_is_concrete_finite(s_rhs, I1_sym, 4, "I1_sym_rhs")
        assert_is_concrete_finite(s_rhs, I2_sym, 4, "I2_sym_rhs")
        assert_is_concrete_finite(s_rhs, I3_sym, 1, "I3_sym_rhs")

        # 2b. Symbolically compute Intermediate2 = smart_raw_add(I2_sym, I3_sym)
        Intermediate2_rhs_sym = define_smart_raw_add_result(I2_sym, I3_sym, "Int2_rhs_res")
        s_rhs.add_assertion(Intermediate2_rhs_sym["definition"])
        s_rhs.add_assertion(Intermediate2_rhs_sym["constraints"])

        # 2c. Symbolically compute RHS_Result_sym = smart_raw_add(I1_sym, Intermediate2_rhs_sym)
        RHS_Result_sym = define_smart_raw_add_result(I1_sym, Intermediate2_rhs_sym, "RHS_final_res")
        s_rhs.add_assertion(RHS_Result_sym["definition"])
        s_rhs.add_assertion(RHS_Result_sym["constraints"])

        # 2d. Define the expected result for RHS: AreoState (representing Unio)
        Expected_RHS_sym = create_intensity_representation("Expected_RHS_is_AS")
        assert_is_concrete_areostate(s_rhs, Expected_RHS_sym) # Expected is AreoState
        
        # 2e. Prove RHS_Result_sym is avc_equiv to Expected_RHS_sym
        s_rhs.add_assertion(Not(avc_equiv(RHS_Result_sym, Expected_RHS_sym)))

        result_rhs = s_rhs.solve()
        if not result_rhs:
            print("Result: UNSAT. RHS = F(4)+(F(4)+F(1)) is PROVED to be avc_equiv to AreoState (Unio). ✅")
        else:
            print("Result: SAT. RHS verification FAILED. Counterexample model:")
            print(f"  I1_sym: Z={s_rhs.get_value(I1_sym['is_zero'])}, A={s_rhs.get_value(I1_sym['is_areo'])}, F={s_rhs.get_value(I1_sym['is_finite'])}, V={s_rhs.get_value(I1_sym['val'])}")
            print(f"  I2_sym: Z={s_rhs.get_value(I2_sym['is_zero'])}, A={s_rhs.get_value(I2_sym['is_areo'])}, F={s_rhs.get_value(I2_sym['is_finite'])}, V={s_rhs.get_value(I2_sym['val'])}")
            print(f"  I3_sym: Z={s_rhs.get_value(I3_sym['is_zero'])}, A={s_rhs.get_value(I3_sym['is_areo'])}, F={s_rhs.get_value(I3_sym['is_finite'])}, V={s_rhs.get_value(I3_sym['val'])}")
            print(f"  Int2_rhs: Z={s_rhs.get_value(Intermediate2_rhs_sym['is_zero'])}, A={s_rhs.get_value(Intermediate2_rhs_sym['is_areo'])}, F={s_rhs.get_value(Intermediate2_rhs_sym['is_finite'])}, V={s_rhs.get_value(Intermediate2_rhs_sym['val'])}")
            print(f"  RHS_Result: Z={s_rhs.get_value(RHS_Result_sym['is_zero'])}, A={s_rhs.get_value(RHS_Result_sym['is_areo'])}, F={s_rhs.get_value(RHS_Result_sym['is_finite'])}, V={s_rhs.get_value(RHS_Result_sym['val'])}")
            print(f"  Expected_RHS: Z={s_rhs.get_value(Expected_RHS_sym['is_zero'])}, A={s_rhs.get_value(Expected_RHS_sym['is_areo'])}, F={s_rhs.get_value(Expected_RHS_sym['is_finite'])}, V={s_rhs.get_value(Expected_RHS_sym['val'])}")
    print("-" * 60)

    # --- Step 3: Prove Non-Associativity: LHS_Result is NOT avc_equiv to RHS_Result ---
    print("--- Proving Non-Associativity: LHS_Result is NOT avc_equiv to RHS_Result ---")
    # We need to show that asserting avc_equiv(LHS_Result_sym, RHS_Result_sym) is UNSAT
    # when LHS is F(1) and RHS is AreoState.
    
    with Solver(name="z3") as s_non_assoc:
        # 3a. Setup I1, I2, I3 as concrete values
        assert_is_concrete_finite(s_non_assoc, I1_sym, 4, "I1_sym_na")
        assert_is_concrete_finite(s_non_assoc, I2_sym, 4, "I2_sym_na")
        assert_is_concrete_finite(s_non_assoc, I3_sym, 1, "I3_sym_na")

        # 3b. Define LHS_Result_sym
        Intermediate1_na_sym = define_smart_raw_add_result(I1_sym, I2_sym, "Int1_na_res")
        s_non_assoc.add_assertion(Intermediate1_na_sym["definition"])
        s_non_assoc.add_assertion(Intermediate1_na_sym["constraints"])
        LHS_na_Result_sym = define_smart_raw_add_result(Intermediate1_na_sym, I3_sym, "LHS_na_final_res")
        s_non_assoc.add_assertion(LHS_na_Result_sym["definition"])
        s_non_assoc.add_assertion(LHS_na_Result_sym["constraints"])
        
        # For clarity in this specific proof, assert what LHS_na_Result_sym should be (F(1))
        # This is redundant if the previous LHS test passed, but makes this test self-contained for proving non-equivalence.
        # If we didn't do this, the solver would explore if there's *any* valid I1,I2,I3 that make LHS=RHS.
        # But we want to show for *these specific* I1,I2,I3, LHS != RHS.
        # The previous test already proved LHS is F(1). We can rely on that or re-assert for clarity.
        # Let's re-assert to be explicit for this proof block.
        s_non_assoc.add_assertion(LHS_na_Result_sym["is_finite"])
        s_non_assoc.add_assertion(Equals(LHS_na_Result_sym["val"], Int(1)))


        # 3c. Define RHS_Result_sym
        Intermediate2_na_sym = define_smart_raw_add_result(I2_sym, I3_sym, "Int2_na_res")
        s_non_assoc.add_assertion(Intermediate2_na_sym["definition"])
        s_non_assoc.add_assertion(Intermediate2_na_sym["constraints"])
        RHS_na_Result_sym = define_smart_raw_add_result(I1_sym, Intermediate2_na_sym, "RHS_na_final_res")
        s_non_assoc.add_assertion(RHS_na_Result_sym["definition"])
        s_non_assoc.add_assertion(RHS_na_Result_sym["constraints"])

        # Explicitly assert what RHS_na_Result_sym should be (AreoState)
        s_non_assoc.add_assertion(RHS_na_Result_sym["is_areo"])

        # 3d. Assert that LHS_Result_sym IS avc_equiv to RHS_Result_sym.
        #     If this is UNSAT, it means they can't be equivalent, proving non-associativity for this case.
        s_non_assoc.add_assertion(avc_equiv(LHS_na_Result_sym, RHS_na_Result_sym))

        result_non_assoc = s_non_assoc.solve()
        if not result_non_assoc:
            print("Result: UNSAT. Non-Associativity PROVED for the example. ✅")
            print("  (F(4)+F(4))+F(1) [which is F(1)] is NOT avc_equiv to F(4)+(F(4)+F(1)) [which is AreoState].")
        else:
            print("Result: SAT. Non-Associativity proof FAILED. This implies LHS and RHS might be equivalent for the example.")
            print(f"  LHS_na_Result: Z={s_non_assoc.get_value(LHS_na_Result_sym['is_zero'])}, A={s_non_assoc.get_value(LHS_na_Result_sym['is_areo'])}, F={s_non_assoc.get_value(LHS_na_Result_sym['is_finite'])}, V={s_non_assoc.get_value(LHS_na_Result_sym['val'])}")
            print(f"  RHS_na_Result: Z={s_non_assoc.get_value(RHS_na_Result_sym['is_zero'])}, A={s_non_assoc.get_value(RHS_na_Result_sym['is_areo'])}, F={s_non_assoc.get_value(RHS_na_Result_sym['is_finite'])}, V={s_non_assoc.get_value(RHS_na_Result_sym['val'])}")

    print("-" * 60)
    print("====== All Phase 4 (Non-Associativity) rigorous tests complete. ======")

"""

**Key elements in `AVC4.py`:**

1.  **Reused Foundations**: All necessary functions from `AVC1.py` and `AVC2.py` (`create_intensity_representation`, `avc_equiv`, `Omega_max_val_nat`, `smart_raw_add_logic_builder`, `define_smart_raw_add_result`) are copied over.
2.  **Concrete Value Assertion Helpers**:
    * `assert_is_concrete_finite(solver, intensity_repr, value, name_for_debug)`: A helper to constrain a symbolic `intensity_repr` to be a specific `Finite` intensity.
    * `assert_is_concrete_zerostate(solver, intensity_repr)`
    * `assert_is_concrete_areostate(solver, intensity_repr)`
3.  **Step 1: LHS Verification**:
    * Symbolic `I1_sym`, `I2_sym`, `I3_sym` are created.
    * They are asserted to be `Finite(4)`, `Finite(4)`, and `Finite(1)` respectively using the helpers.
    * The calculation `(I1_sym + I2_sym) + I3_sym` is performed symbolically, step-by-step, creating `Intermediate1_lhs_sym` and then `LHS_Result_sym`. The `definition` and `constraints` of these intermediate results are asserted.
    * An `Expected_LHS_sym` is created and asserted to be `Finite(1)`.
    * The SMT solver is asked if `Not(avc_equiv(LHS_Result_sym, Expected_LHS_sym))` can be true. An UNSAT result proves `LHS_Result_sym` is indeed `avc_equiv` to `Finite(1)`.
4.  **Step 2: RHS Verification**:
    * Similar process for `I1_sym + (I2_sym + I3_sym)`, resulting in `RHS_Result_sym`.
    * An `Expected_RHS_sym` is created and asserted to be `AreoState`.
    * The SMT solver proves `RHS_Result_sym` is `avc_equiv` to `AreoState`.
5.  **Step 3: Proof of Non-Associativity**:
    * The symbolic `I1_sym`, `I2_sym`, `I3_sym` are again set up with their concrete values.
    * `LHS_na_Result_sym` and `RHS_na_Result_sym` are re-computed (or could be reused if the solver context was managed differently, but re-computing within a fresh solver context for this final proof is cleaner).
    * To be absolutely explicit for this final proof, we also add assertions that `LHS_na_Result_sym` *is* `Finite(1)` and `RHS_na_Result_sym` *is* `AreoState`. This leverages the results from Step 1 and Step 2.
    * The SMT solver is then asked if `avc_equiv(LHS_na_Result_sym, RHS_na_Result_sym)` can be true.
    * An UNSAT result here means they *cannot* be equivalent, thus proving that for this specific example, `(I1+I2)+I3 ≠ I1+(I2+I3)` in terms of `avc_equiv`.

This script is structured to be very deliberate and to break down the proof into verifiable stages. """