from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE

# --- Phase 1: Foundational Definitions (Copied from AVC1.py / AVC4.py) ---
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

# --- Phase 2: Raw Operations Definitions (Copied & Verified from AVC2.py/AVC4.py) ---
Omega_max_val_nat = Int(7)

def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder):
    core_logic_formula = op_logic_builder(i1_repr, i2_repr, res_repr)
    return core_logic_formula

# --- smart_raw_add ---
def smart_raw_add_logic_builder(i1, i2, res):
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
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) 
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) 
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), Ite(val_sum >= Omega_max_val_nat,
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)))))
    return And(formulas)

def define_smart_raw_add_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder)
    return res_repr

# --- raw_mul ---
def raw_mul_logic_builder(i1, i2, res):
    formulas = []
    val_prod = i1["val"] * i2["val"] 
    formulas.append(Implies(i1["is_zero"], 
        And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), 
         And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), 
                                i1["is_areo"], i2["is_areo"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i1["is_areo"], i2["is_finite"]), 
        Ite(i2["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  
        )))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i2["is_areo"], i1["is_finite"]), 
        Ite(i1["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  
        )))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
        Ite(val_prod >= Omega_max_val_nat,
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_prod)) 
        )))
    return And(formulas)

def define_raw_mul_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_mul_logic_builder)
    return res_repr

# --- Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Phase 5: Commutativity & Distributivity Tests ======\n")

    # --- Symbolic Intensities for universal property testing ---
    i_a = create_intensity_representation("i_a_sym")
    i_b = create_intensity_representation("i_b_sym")
    i_c = create_intensity_representation("i_c_sym") # For distributivity

    # --- Test 1: Prove Commutativity of smart_raw_add ---
    # Property: ForAll a, b: smart_raw_add(a, b) ~ smart_raw_add(b, a)
    # Test: Is (valid_a & valid_b & NOT (smart_raw_add(a,b) ~ smart_raw_add(b,a))) SAT? Expect UNSAT.
    print("--- Test 1: Proving Commutativity of smart_raw_add ---")
    with Solver(name="z3") as s:
        s.add_assertion(i_a["constraints"])
        s.add_assertion(i_b["constraints"])

        res_ab = define_smart_raw_add_result(i_a, i_b, "res_ab_add")
        s.add_assertion(res_ab["definition"])
        s.add_assertion(res_ab["constraints"]) # Result must be valid

        res_ba = define_smart_raw_add_result(i_b, i_a, "res_ba_add")
        s.add_assertion(res_ba["definition"])
        s.add_assertion(res_ba["constraints"]) # Result must be valid

        s.add_assertion(Not(avc_equiv(res_ab, res_ba))) # Assert negation of commutativity

        result = s.solve()
        if not result:
            print("Result: UNSAT. Commutativity of smart_raw_add is PROVED. ✅")
        else:
            print("Result: SAT. Commutativity of smart_raw_add FAILED. Counterexample:")
            print(f"  i_a: Z={s.get_value(i_a['is_zero'])}, A={s.get_value(i_a['is_areo'])}, F={s.get_value(i_a['is_finite'])}, V={s.get_value(i_a['val'])}")
            print(f"  i_b: Z={s.get_value(i_b['is_zero'])}, A={s.get_value(i_b['is_areo'])}, F={s.get_value(i_b['is_finite'])}, V={s.get_value(i_b['val'])}")
            print(f"  res_ab: Z={s.get_value(res_ab['is_zero'])}, A={s.get_value(res_ab['is_areo'])}, F={s.get_value(res_ab['is_finite'])}, V={s.get_value(res_ab['val'])}")
            print(f"  res_ba: Z={s.get_value(res_ba['is_zero'])}, A={s.get_value(res_ba['is_areo'])}, F={s.get_value(res_ba['is_finite'])}, V={s.get_value(res_ba['val'])}")
    print("-" * 60)

    # --- Test 2: Prove Commutativity of raw_mul ---
    # Property: ForAll a, b: raw_mul(a, b) ~ raw_mul(b, a)
    # Test: Is (valid_a & valid_b & NOT (raw_mul(a,b) ~ raw_mul(b,a))) SAT? Expect UNSAT.
    print("--- Test 2: Proving Commutativity of raw_mul ---")
    with Solver(name="z3") as s:
        s.add_assertion(i_a["constraints"])
        s.add_assertion(i_b["constraints"])

        res_ab_mul = define_raw_mul_result(i_a, i_b, "res_ab_mul")
        s.add_assertion(res_ab_mul["definition"])
        s.add_assertion(res_ab_mul["constraints"])

        res_ba_mul = define_raw_mul_result(i_b, i_a, "res_ba_mul")
        s.add_assertion(res_ba_mul["definition"])
        s.add_assertion(res_ba_mul["constraints"])

        s.add_assertion(Not(avc_equiv(res_ab_mul, res_ba_mul)))

        result = s.solve()
        if not result:
            print("Result: UNSAT. Commutativity of raw_mul is PROVED. ✅")
        else:
            print("Result: SAT. Commutativity of raw_mul FAILED. Counterexample:")
            print(f"  i_a: Z={s.get_value(i_a['is_zero'])}, A={s.get_value(i_a['is_areo'])}, F={s.get_value(i_a['is_finite'])}, V={s.get_value(i_a['val'])}")
            print(f"  i_b: Z={s.get_value(i_b['is_zero'])}, A={s.get_value(i_b['is_areo'])}, F={s.get_value(i_b['is_finite'])}, V={s.get_value(i_b['val'])}")
            print(f"  res_ab_mul: Z={s.get_value(res_ab_mul['is_zero'])}, A={s.get_value(res_ab_mul['is_areo'])}, F={s.get_value(res_ab_mul['is_finite'])}, V={s.get_value(res_ab_mul['val'])}")
            print(f"  res_ba_mul: Z={s.get_value(res_ba_mul['is_zero'])}, A={s.get_value(res_ba_mul['is_areo'])}, F={s.get_value(res_ba_mul['is_finite'])}, V={s.get_value(res_ba_mul['val'])}")
    print("-" * 60)

    # --- Test 3: Investigate Distributivity of raw_mul over smart_raw_add ---
    # Property: raw_mul(a, smart_raw_add(b, c)) ~ smart_raw_add(raw_mul(a, b), raw_mul(a, c))
    # This is LIKELY TO FAIL (i.e., the negation is SAT, giving a counterexample).
    # Test: Is (valid_abc & NOT (LHS ~ RHS)) SAT? If SAT, distributivity fails, and model is counterexample.
    # If UNSAT, distributivity holds (less likely for this system).
    print("--- Test 3: Investigating Distributivity: a*(b+c) ~ (a*b) + (a*c) ---")
    with Solver(name="z3") as s:
        s.add_assertion(i_a["constraints"])
        s.add_assertion(i_b["constraints"])
        s.add_assertion(i_c["constraints"])

        # Calculate LHS: i_a * (i_b + i_c)
        sum_bc = define_smart_raw_add_result(i_b, i_c, "sum_bc_dist")
        s.add_assertion(sum_bc["definition"])
        s.add_assertion(sum_bc["constraints"])
        
        lhs_dist = define_raw_mul_result(i_a, sum_bc, "lhs_dist_res")
        s.add_assertion(lhs_dist["definition"])
        s.add_assertion(lhs_dist["constraints"])

        # Calculate RHS: (i_a * i_b) + (i_a * i_c)
        prod_ab = define_raw_mul_result(i_a, i_b, "prod_ab_dist")
        s.add_assertion(prod_ab["definition"])
        s.add_assertion(prod_ab["constraints"])

        prod_ac = define_raw_mul_result(i_a, i_c, "prod_ac_dist")
        s.add_assertion(prod_ac["definition"])
        s.add_assertion(prod_ac["constraints"])

        rhs_dist = define_smart_raw_add_result(prod_ab, prod_ac, "rhs_dist_res")
        s.add_assertion(rhs_dist["definition"])
        s.add_assertion(rhs_dist["constraints"])

        # Assert that LHS is NOT equivalent to RHS (to find a counterexample)
        s.add_assertion(Not(avc_equiv(lhs_dist, rhs_dist)))

        result = s.solve()
        if result: # SAT means we found a counterexample where distributivity FAILS
            print("Result: SAT. Distributivity does NOT hold universally. Counterexample found: ❌")
            print(f"  i_a: Z={s.get_value(i_a['is_zero'])}, A={s.get_value(i_a['is_areo'])}, F={s.get_value(i_a['is_finite'])}, V={s.get_value(i_a['val'])}")
            print(f"  i_b: Z={s.get_value(i_b['is_zero'])}, A={s.get_value(i_b['is_areo'])}, F={s.get_value(i_b['is_finite'])}, V={s.get_value(i_b['val'])}")
            print(f"  i_c: Z={s.get_value(i_c['is_zero'])}, A={s.get_value(i_c['is_areo'])}, F={s.get_value(i_c['is_finite'])}, V={s.get_value(i_c['val'])}")
            print(f"    sum_bc (b+c): Z={s.get_value(sum_bc['is_zero'])}, A={s.get_value(sum_bc['is_areo'])}, F={s.get_value(sum_bc['is_finite'])}, V={s.get_value(sum_bc['val'])}")
            print(f"    LHS (a*(b+c)): Z={s.get_value(lhs_dist['is_zero'])}, A={s.get_value(lhs_dist['is_areo'])}, F={s.get_value(lhs_dist['is_finite'])}, V={s.get_value(lhs_dist['val'])}")
            print(f"    prod_ab (a*b): Z={s.get_value(prod_ab['is_zero'])}, A={s.get_value(prod_ab['is_areo'])}, F={s.get_value(prod_ab['is_finite'])}, V={s.get_value(prod_ab['val'])}")
            print(f"    prod_ac (a*c): Z={s.get_value(prod_ac['is_zero'])}, A={s.get_value(prod_ac['is_areo'])}, F={s.get_value(prod_ac['is_finite'])}, V={s.get_value(prod_ac['val'])}")
            print(f"    RHS ((a*b)+(a*c)): Z={s.get_value(rhs_dist['is_zero'])}, A={s.get_value(rhs_dist['is_areo'])}, F={s.get_value(rhs_dist['is_finite'])}, V={s.get_value(rhs_dist['val'])}")
        else: # UNSAT means NOT (LHS ~ RHS) is false, which means LHS ~ RHS holds universally.
            print("Result: UNSAT. Distributivity (a*(b+c) ~ (a*b)+(a*c)) appears to HOLD universally. ✅ (This would be surprising)")
    print("-" * 60)

    # --- Test 4: More detailed tests around Omega_max_val_nat for smart_raw_add ---
    # We'll use concrete values for two finite numbers that sum to Omega-1, Omega, Omega+1
    print("--- Test 4: smart_raw_add behavior around Omega_max_val_nat ---")
    
    # Case 4a: F(3) + F(3) = F(6) (since Omega = 7, 6 < 7)
    val_a_o = create_intensity_representation("val_a_omega_add")
    val_b_o = create_intensity_representation("val_b_omega_add")
    expected_res_o = create_intensity_representation("exp_res_omega_add")

    with Solver(name="z3") as s:
        # Setup inputs: F(3) and F(3)
        s.add_assertion(val_a_o["constraints"]); s.add_assertion(val_a_o["is_finite"]); s.add_assertion(Equals(val_a_o["val"], Int(3)))
        s.add_assertion(val_b_o["constraints"]); s.add_assertion(val_b_o["is_finite"]); s.add_assertion(Equals(val_b_o["val"], Int(3)))
        # Define actual result
        actual_res_o = define_smart_raw_add_result(val_a_o, val_b_o, "actual_o_add1")
        s.add_assertion(actual_res_o["definition"]); s.add_assertion(actual_res_o["constraints"])
        # Define expected result: F(6)
        s.add_assertion(expected_res_o["constraints"]); s.add_assertion(expected_res_o["is_finite"]); s.add_assertion(Equals(expected_res_o["val"], Int(6)))
        # Check if NOT (actual ~ expected) is SAT
        s.add_assertion(Not(avc_equiv(actual_res_o, expected_res_o)))
        if not s.solve(): print("  Test F(3)+F(3)=F(6): PROVED. ✅")
        else: print("  Test F(3)+F(3)=F(6): FAILED. ❌")

    # Case 4b: F(3) + F(4) = AreoState (since Omega = 7, 3+4=7)
    with Solver(name="z3") as s:
        s.add_assertion(val_a_o["constraints"]); s.add_assertion(val_a_o["is_finite"]); s.add_assertion(Equals(val_a_o["val"], Int(3)))
        s.add_assertion(val_b_o["constraints"]); s.add_assertion(val_b_o["is_finite"]); s.add_assertion(Equals(val_b_o["val"], Int(4)))
        actual_res_o = define_smart_raw_add_result(val_a_o, val_b_o, "actual_o_add2")
        s.add_assertion(actual_res_o["definition"]); s.add_assertion(actual_res_o["constraints"])
        s.add_assertion(expected_res_o["constraints"]); s.add_assertion(expected_res_o["is_areo"]) # Expected is Areo
        s.add_assertion(Not(avc_equiv(actual_res_o, expected_res_o)))
        if not s.solve(): print("  Test F(3)+F(4)=AreoState: PROVED. ✅")
        else: print("  Test F(3)+F(4)=AreoState: FAILED. ❌")

    # Case 4c: F(4) + F(4) = AreoState (since Omega = 7, 4+4=8 > 7)
    with Solver(name="z3") as s:
        s.add_assertion(val_a_o["constraints"]); s.add_assertion(val_a_o["is_finite"]); s.add_assertion(Equals(val_a_o["val"], Int(4)))
        s.add_assertion(val_b_o["constraints"]); s.add_assertion(val_b_o["is_finite"]); s.add_assertion(Equals(val_b_o["val"], Int(4)))
        actual_res_o = define_smart_raw_add_result(val_a_o, val_b_o, "actual_o_add3")
        s.add_assertion(actual_res_o["definition"]); s.add_assertion(actual_res_o["constraints"])
        s.add_assertion(expected_res_o["constraints"]); s.add_assertion(expected_res_o["is_areo"]) # Expected is Areo
        s.add_assertion(Not(avc_equiv(actual_res_o, expected_res_o)))
        if not s.solve(): print("  Test F(4)+F(4)=AreoState: PROVED. ✅")
        else: print("  Test F(4)+F(4)=AreoState: FAILED. ❌")
    print("-" * 60)
    
    print("====== All Phase 5 (Commutativity, Distributivity, Omega Threshold) tests complete. ======")

"""

**Key Features of `AVC5.py` for "No-Mercy" Testing:**

1.  **Commutativity Tests (Test 1 & 2)**:
    * Uses symbolic `i_a` and `i_b`.
    * Asserts their validity.
    * Symbolically computes `op(i_a, i_b)` into `res_ab` and `op(i_b, i_a)` into `res_ba`.
    * Asserts validity of `res_ab` and `res_ba`.
    * Asserts `Not(avc_equiv(res_ab, res_ba))`.
    * An **UNSAT** result proves commutativity for all valid inputs.

2.  **Distributivity Investigation (Test 3)**:
    * Uses symbolic `i_a`, `i_b`, `i_c`.
    * Symbolically computes LHS: `LHS = raw_mul(i_a, smart_raw_add(i_b, i_c))`.
    * Symbolically computes RHS: `RHS = smart_raw_add(raw_mul(i_a, i_b), raw_mul(i_a, i_c))`.
    * Asserts validity of all intermediate and final results.
    * Asserts `Not(avc_equiv(LHS, RHS))`.
    * If **SAT**, the SMT solver has found a specific counterexample (values for `i_a`, `i_b`, `i_c`) where distributivity *fails*. The model will be printed. This is the more likely outcome for systems like AVC.
    * If **UNSAT** (less likely), it would suggest distributivity holds universally.

3.  **Omega Threshold Tests for `smart_raw_add` (Test 4)**:
    * Uses *concrete* finite values that sum to `Omega_max_val_nat - 1`, `Omega_max_val_nat`, and `Omega_max_val_nat + 1`.
    * For each case, it asserts the inputs, defines the symbolic result of the addition, defines the expected symbolic result (e.g., `Finite(6)` or `AreoState`), and then proves that the actual result is `avc_equiv` to the expected result by showing their non-equivalence is UNSAT.
    * This meticulously checks the boundary conditions of the thresholding logic.

**Important Notes on `smart_raw_add` Logic (again for clarity):**
The `smart_raw_add_logic_builder` in this script continues to reflect the Lean Phase 4 V1 `smart_raw_add` behavior:
* `ZeroState + X -> X` (if X is ZS, then ZS; if X is AS, then AS; if X is F(p), then F(p))
* `AreoState + X -> X` (if X is ZS, then AS; if X is AS, then AS; if X is F(p), then F(p))
* `Finite(p) + ZeroState -> Finite(p)`
* `Finite(p) + AreoState -> Finite(p)`
This means `ZeroState` and `AreoState` (as representatives of `Unio_quot`) act as identities for addition with `Finite` values in `smart_raw_add`. This is consistent with "Emergence from Unio" Postulate 6.1 (`U + X_DFI = X_DFI` where U's Zero-potential is engaged). The commutativity proof will test if this symmetry holds (e.g., `X_DFI + U` also yields `X_DFI`).

This script is a significant step up in complexity, especially the distributivity test. """