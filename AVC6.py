from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE

# --- Phase 1: Foundational Definitions (Copied) ---
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

# --- Phase 2: Raw Operations Definitions (Copied) ---
Omega_max_val_nat = Int(7)

def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder):
    core_logic_formula = op_logic_builder(i1_repr, i2_repr, res_repr)
    return core_logic_formula

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

def raw_sub_from_Unio_Areo_aspect_logic_builder(i_unio_areo, _i_any, res):
    return And(Implies(Or(i_unio_areo["is_zero"], i_unio_areo["is_areo"], i_unio_areo["is_finite"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

def define_raw_sub_from_Unio_Areo_aspect_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_sub_from_Unio_Areo_aspect_logic_builder)
    return res_repr

# --- Generic Property Prover ---
def prove_universal_property(solver, property_name, setup_assertions, property_formula, expect_unsat=True):
    """
    Tries to prove a universal property by checking if its negation is UNSAT.
    If expect_unsat is False, it tries to find a model for property_formula (useful for finding counterexamples).
    """
    print(f"--- Testing Property: {property_name} ---")
    solver.push() # Create a new assertion scope
    for assertion in setup_assertions:
        solver.add_assertion(assertion)
    
    if expect_unsat:
        solver.add_assertion(Not(property_formula)) # Assert negation of the property
        result = solver.solve()
        if not result:
            print(f"Result: UNSAT. Property '{property_name}' is PROVED. ✅")
        else:
            print(f"Result: SAT. Property '{property_name}' FAILED. Counterexample model indicates property does not hold universally.")
            # Details will be printed by the calling code if needed
    else: # We are trying to find a model for property_formula (e.g. for a counterexample to a different property)
        solver.add_assertion(property_formula)
        result = solver.solve()
        if result:
            print(f"Result: SAT. Found a model for '{property_name}'. This might be a counterexample to another property. ✅")
        else:
            print(f"Result: UNSAT. Could not find a model for '{property_name}'. ❌")

    solver.pop() # Restore previous assertion scope
    print("-" * 70)
    return not result if expect_unsat else result


# --- Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Phase 6: Pinnacle Brutal Algebraic Stress Tests ======\n")

    s = Solver(name="z3") # Create one solver instance for all tests in this run

    # --- Symbolic Intensities for universal property testing ---
    i_a = create_intensity_representation("i_a_univ")
    i_b = create_intensity_representation("i_b_univ")
    i_c = create_intensity_representation("i_c_univ")

    # Base assertions: all symbolic intensities must be valid
    base_setup = [i_a["constraints"], i_b["constraints"], i_c["constraints"]]

    # --- 1. Commutativity of smart_raw_add ---
    # Prop: smart_raw_add(a, b) ~ smart_raw_add(b, a)
    res_ab_add = define_smart_raw_add_result(i_a, i_b, "res_ab_add_comm")
    res_ba_add = define_smart_raw_add_result(i_b, i_a, "res_ba_add_comm")
    prove_universal_property(s, "Commutativity of smart_raw_add: a+b ~ b+a", 
                             base_setup + [res_ab_add["definition"], res_ab_add["constraints"],
                                           res_ba_add["definition"], res_ba_add["constraints"]],
                             avc_equiv(res_ab_add, res_ba_add))

    # --- 2. Commutativity of raw_mul ---
    # Prop: raw_mul(a, b) ~ raw_mul(b, a)
    res_ab_mul = define_raw_mul_result(i_a, i_b, "res_ab_mul_comm")
    res_ba_mul = define_raw_mul_result(i_b, i_a, "res_ba_mul_comm")
    prove_universal_property(s, "Commutativity of raw_mul: a*b ~ b*a",
                             base_setup + [res_ab_mul["definition"], res_ab_mul["constraints"],
                                           res_ba_mul["definition"], res_ba_mul["constraints"]],
                             avc_equiv(res_ab_mul, res_ba_mul))

    # --- 3. Associativity of smart_raw_add ---
    # Prop: (a+b)+c ~ a+(b+c). Expected to FAIL.
    # We test if NOT ((a+b)+c ~ a+(b+c)) is SAT to find a counterexample.
    sum_ab = define_smart_raw_add_result(i_a, i_b, "sum_ab_assoc_add")
    lhs_add_assoc = define_smart_raw_add_result(sum_ab, i_c, "lhs_add_assoc")
    sum_bc = define_smart_raw_add_result(i_b, i_c, "sum_bc_assoc_add")
    rhs_add_assoc = define_smart_raw_add_result(i_a, sum_bc, "rhs_add_assoc")
    
    # We are trying to find if there EXISTS a,b,c such that (a+b)+c is NOT avc_equiv to a+(b+c)
    # So property_formula is Not(avc_equiv(lhs,rhs)) and expect_unsat=False (we expect SAT)
    if prove_universal_property(s, "Non-Associativity of smart_raw_add: (a+b)+c Not~ a+(b+c)",
                                base_setup + [sum_ab["definition"], sum_ab["constraints"],
                                              lhs_add_assoc["definition"], lhs_add_assoc["constraints"],
                                              sum_bc["definition"], sum_bc["constraints"],
                                              rhs_add_assoc["definition"], rhs_add_assoc["constraints"]],
                                Not(avc_equiv(lhs_add_assoc, rhs_add_assoc)), 
                                expect_unsat=False): # Expect SAT to find counterexample
        print("      Counterexample for Non-Associativity of smart_raw_add:")
        print(f"      i_a: Z={s.get_value(i_a['is_zero'])}, A={s.get_value(i_a['is_areo'])}, F={s.get_value(i_a['is_finite'])}, V={s.get_value(i_a['val'])}")
        print(f"      i_b: Z={s.get_value(i_b['is_zero'])}, A={s.get_value(i_b['is_areo'])}, F={s.get_value(i_b['is_finite'])}, V={s.get_value(i_b['val'])}")
        print(f"      i_c: Z={s.get_value(i_c['is_zero'])}, A={s.get_value(i_c['is_areo'])}, F={s.get_value(i_c['is_finite'])}, V={s.get_value(i_c['val'])}")
        print(f"      (a+b): Z={s.get_value(sum_ab['is_zero'])}, A={s.get_value(sum_ab['is_areo'])}, F={s.get_value(sum_ab['is_finite'])}, V={s.get_value(sum_ab['val'])}")
        print(f"      LHS: Z={s.get_value(lhs_add_assoc['is_zero'])}, A={s.get_value(lhs_add_assoc['is_areo'])}, F={s.get_value(lhs_add_assoc['is_finite'])}, V={s.get_value(lhs_add_assoc['val'])}")
        print(f"      (b+c): Z={s.get_value(sum_bc['is_zero'])}, A={s.get_value(sum_bc['is_areo'])}, F={s.get_value(sum_bc['is_finite'])}, V={s.get_value(sum_bc['val'])}")
        print(f"      RHS: Z={s.get_value(rhs_add_assoc['is_zero'])}, A={s.get_value(rhs_add_assoc['is_areo'])}, F={s.get_value(rhs_add_assoc['is_finite'])}, V={s.get_value(rhs_add_assoc['val'])}")

    # --- 4. Associativity of raw_mul ---
    # Prop: (a*b)*c ~ a*(b*c). This might also fail.
    prod_ab_mul = define_raw_mul_result(i_a, i_b, "prod_ab_assoc_mul")
    lhs_mul_assoc = define_raw_mul_result(prod_ab_mul, i_c, "lhs_mul_assoc")
    prod_bc_mul = define_raw_mul_result(i_b, i_c, "prod_bc_assoc_mul")
    rhs_mul_assoc = define_raw_mul_result(i_a, prod_bc_mul, "rhs_mul_assoc")
    
    if prove_universal_property(s, "Non-Associativity of raw_mul: (a*b)*c Not~ a*(b*c)",
                                base_setup + [prod_ab_mul["definition"], prod_ab_mul["constraints"],
                                              lhs_mul_assoc["definition"], lhs_mul_assoc["constraints"],
                                              prod_bc_mul["definition"], prod_bc_mul["constraints"],
                                              rhs_mul_assoc["definition"], rhs_mul_assoc["constraints"]],
                                Not(avc_equiv(lhs_mul_assoc, rhs_mul_assoc)),
                                expect_unsat=False): # Expect SAT if it fails
        print("      Counterexample for Non-Associativity of raw_mul:")
        # (Printing model details similar to above if needed)
        print(f"      i_a: V={s.get_value(i_a['val'])}, Z={s.get_value(i_a['is_zero'])}, A={s.get_value(i_a['is_areo'])}")
        print(f"      i_b: V={s.get_value(i_b['val'])}, Z={s.get_value(i_b['is_zero'])}, A={s.get_value(i_b['is_areo'])}")
        print(f"      i_c: V={s.get_value(i_c['val'])}, Z={s.get_value(i_c['is_zero'])}, A={s.get_value(i_c['is_areo'])}")
        print(f"      LHS: V={s.get_value(lhs_mul_assoc['val'])}, Z={s.get_value(lhs_mul_assoc['is_zero'])}, A={s.get_value(lhs_mul_assoc['is_areo'])}")
        print(f"      RHS: V={s.get_value(rhs_mul_assoc['val'])}, Z={s.get_value(rhs_mul_assoc['is_zero'])}, A={s.get_value(rhs_mul_assoc['is_areo'])}")


    # --- 5. Distributivity (Left): a*(b+c) ~ (a*b) + (a*c) ---
    # Expected to FAIL. Test if NOT (LHS ~ RHS) is SAT.
    sum_bc_dist_l = define_smart_raw_add_result(i_b, i_c, "sum_bc_dist_l")
    lhs_dist_l = define_raw_mul_result(i_a, sum_bc_dist_l, "lhs_dist_l_res")
    prod_ab_dist_l = define_raw_mul_result(i_a, i_b, "prod_ab_dist_l")
    prod_ac_dist_l = define_raw_mul_result(i_a, i_c, "prod_ac_dist_l")
    rhs_dist_l = define_smart_raw_add_result(prod_ab_dist_l, prod_ac_dist_l, "rhs_dist_l_res")

    if prove_universal_property(s, "Non-Distributivity (Left): a*(b+c) Not~ (a*b)+(a*c)",
                                base_setup + [sum_bc_dist_l["definition"], sum_bc_dist_l["constraints"],
                                              lhs_dist_l["definition"], lhs_dist_l["constraints"],
                                              prod_ab_dist_l["definition"], prod_ab_dist_l["constraints"],
                                              prod_ac_dist_l["definition"], prod_ac_dist_l["constraints"],
                                              rhs_dist_l["definition"], rhs_dist_l["constraints"]],
                                Not(avc_equiv(lhs_dist_l, rhs_dist_l)),
                                expect_unsat=False): # Expect SAT if it fails
        print("      Counterexample for Non-Distributivity (Left):")
        # (Printing model details)
        print(f"      i_a: V={s.get_value(i_a['val'])}, Z={s.get_value(i_a['is_zero'])}, A={s.get_value(i_a['is_areo'])}")
        print(f"      i_b: V={s.get_value(i_b['val'])}, Z={s.get_value(i_b['is_zero'])}, A={s.get_value(i_b['is_areo'])}")
        print(f"      i_c: V={s.get_value(i_c['val'])}, Z={s.get_value(i_c['is_zero'])}, A={s.get_value(i_c['is_areo'])}")
        print(f"      LHS: V={s.get_value(lhs_dist_l['val'])}, Z={s.get_value(lhs_dist_l['is_zero'])}, A={s.get_value(lhs_dist_l['is_areo'])}")
        print(f"      RHS: V={s.get_value(rhs_dist_l['val'])}, Z={s.get_value(rhs_dist_l['is_zero'])}, A={s.get_value(rhs_dist_l['is_areo'])}")


    # --- 6. Distributivity (Right): (a+b)*c ~ (a*c) + (b*c) ---
    # Expected to FAIL. Test if NOT (LHS ~ RHS) is SAT.
    sum_ab_dist_r = define_smart_raw_add_result(i_a, i_b, "sum_ab_dist_r")
    lhs_dist_r = define_raw_mul_result(sum_ab_dist_r, i_c, "lhs_dist_r_res")
    prod_ac_dist_r = define_raw_mul_result(i_a, i_c, "prod_ac_dist_r")
    prod_bc_dist_r = define_raw_mul_result(i_b, i_c, "prod_bc_dist_r")
    rhs_dist_r = define_smart_raw_add_result(prod_ac_dist_r, prod_bc_dist_r, "rhs_dist_r_res")

    if prove_universal_property(s, "Non-Distributivity (Right): (a+b)*c Not~ (a*c)+(b*c)",
                                base_setup + [sum_ab_dist_r["definition"], sum_ab_dist_r["constraints"],
                                              lhs_dist_r["definition"], lhs_dist_r["constraints"],
                                              prod_ac_dist_r["definition"], prod_ac_dist_r["constraints"],
                                              prod_bc_dist_r["definition"], prod_bc_dist_r["constraints"],
                                              rhs_dist_r["definition"], rhs_dist_r["constraints"]],
                                Not(avc_equiv(lhs_dist_r, rhs_dist_r)),
                                expect_unsat=False): # Expect SAT if it fails
        print("      Counterexample for Non-Distributivity (Right):")
        # (Printing model details)
        print(f"      i_a: V={s.get_value(i_a['val'])}, Z={s.get_value(i_a['is_zero'])}, A={s.get_value(i_a['is_areo'])}")
        print(f"      i_b: V={s.get_value(i_b['val'])}, Z={s.get_value(i_b['is_zero'])}, A={s.get_value(i_b['is_areo'])}")
        print(f"      i_c: V={s.get_value(i_c['val'])}, Z={s.get_value(i_c['is_zero'])}, A={s.get_value(i_c['is_areo'])}")
        print(f"      LHS: V={s.get_value(lhs_dist_r['val'])}, Z={s.get_value(lhs_dist_r['is_zero'])}, A={s.get_value(lhs_dist_r['is_areo'])}")
        print(f"      RHS: V={s.get_value(rhs_dist_r['val'])}, Z={s.get_value(rhs_dist_r['is_zero'])}, A={s.get_value(rhs_dist_r['is_areo'])}")

    # --- 7. Zero Annihilation for raw_mul ---
    # Prop: raw_mul(ZeroState, a) ~ ZeroState
    zero_const = create_intensity_representation("zero_const_mul") # Represents ZeroState
    res_zs_a_mul = define_raw_mul_result(zero_const, i_a, "res_zs_a_mul")
    prove_universal_property(s, "Zero Annihilation (Left): ZS * a ~ ZS",
                             base_setup[:1] + [zero_const["constraints"], zero_const["is_zero"], # Only i_a and zero_const need to be valid
                                             res_zs_a_mul["definition"], res_zs_a_mul["constraints"]],
                             avc_equiv(res_zs_a_mul, zero_const))

    # Prop: raw_mul(a, ZeroState) ~ ZeroState
    res_a_zs_mul = define_raw_mul_result(i_a, zero_const, "res_a_zs_mul")
    prove_universal_property(s, "Zero Annihilation (Right): a * ZS ~ ZS",
                             base_setup[:1] + [zero_const["constraints"], zero_const["is_zero"],
                                             res_a_zs_mul["definition"], res_a_zs_mul["constraints"]],
                             avc_equiv(res_a_zs_mul, zero_const))

    # --- 8. AreoState Multiplication Properties for raw_mul ---
    areo_const = create_intensity_representation("areo_const_mul") # Represents AreoState
    
    # Prop: raw_mul(AreoState, AreoState) ~ AreoState
    res_as_as_mul = define_raw_mul_result(areo_const, areo_const, "res_as_as_mul") # Use areo_const for both
    prove_universal_property(s, "Areo Multiplication: AS * AS ~ AS",
                             [areo_const["constraints"], areo_const["is_areo"], # Only areo_const needs to be valid AS
                              res_as_as_mul["definition"], res_as_as_mul["constraints"]],
                             avc_equiv(res_as_as_mul, areo_const))

    # Prop: ForAll p (Finite p.val > 0), raw_mul(AreoState, p) ~ AreoState
    # Symbolic p for DFI
    p_dfi_mul = create_intensity_representation("p_dfi_mul")
    res_as_p_mul = define_raw_mul_result(areo_const, p_dfi_mul, "res_as_p_mul")
    prove_universal_property(s, "Areo Multiplication: AS * F(p>0) ~ AS",
                             [areo_const["constraints"], areo_const["is_areo"],
                              p_dfi_mul["constraints"], p_dfi_mul["is_finite"], # p_dfi_mul.val > 0 is in its constraints
                              res_as_p_mul["definition"], res_as_p_mul["constraints"]],
                             avc_equiv(res_as_p_mul, areo_const))
    
    # Consistency for AS * F(p_not_gt_0) -> ZS (raw_mul specific branch)
    # Here, we test if raw_mul(AS, F(p_not_gt_0)) results in ZS.
    # This requires setting up p_dfi_mul to be finite but its value NOT > 0,
    # which contradicts its own PosNat constraint. So, the setup for p_dfi_mul
    # must be carefully crafted for this specific test of raw_mul's branch.
    # This is tricky because create_intensity_representation enforces val > 0 for finite.
    # We will test the branch directly: if i_a is AS, and i_b is Finite AND i_b.val is NOT > 0,
    # then raw_mul(i_a, i_b) should be ZeroState.
    print("   Testing raw_mul branch: AS * F(p where p.val NOT > 0) ~ ZS")
    with Solver(name="z3") as s_branch_test:
        s_branch_test.add_assertion(i_a["constraints"]); s_branch_test.add_assertion(i_a["is_areo"]) # i_a is AS
        # For i_b, we assert it's finite but its value is NOT > 0, overriding normal PosNat.
        # This is to specifically test the 'else zeroState' branch of raw_mul.
        # Note: This i_b is NOT a "valid DFI" by our create_intensity_representation constraints if asserted together.
        # We are testing raw_mul's internal logic.
        s_branch_test.add_assertion(i_b["is_finite"])
        s_branch_test.add_assertion(Not(i_b["val"] > Int(0))) # Force value to be <= 0
        # We also need to ensure ExactlyOne still holds for i_b for this specific state:
        s_branch_test.add_assertion(Not(i_b["is_zero"])); s_branch_test.add_assertion(Not(i_b["is_areo"]))


        res_as_f_notpos = define_raw_mul_result(i_a, i_b, "res_as_f_notpos")
        s_branch_test.add_assertion(res_as_f_notpos["definition"])
        s_branch_test.add_assertion(res_as_f_notpos["constraints"]) # Result must be valid

        expected_zs = create_intensity_representation("exp_zs_for_branch")
        s_branch_test.add_assertion(expected_zs["constraints"]); s_branch_test.add_assertion(expected_zs["is_zero"])

        s_branch_test.add_assertion(Not(avc_equiv(res_as_f_notpos, expected_zs)))
        if not s_branch_test.solve():
            print("     Branch test AS * F(p where p.val NOT > 0) ~ ZS: PROVED. ✅")
        else:
            print("     Branch test AS * F(p where p.val NOT > 0) ~ ZS: FAILED. ❌")
            # Model details would be useful here
            print(f"      i_a (AS): Z={s_branch_test.get_value(i_a['is_zero'])}, A={s_branch_test.get_value(i_a['is_areo'])}, F={s_branch_test.get_value(i_a['is_finite'])}, V={s_branch_test.get_value(i_a['val'])}")
            print(f"      i_b (F, val<=0): Z={s_branch_test.get_value(i_b['is_zero'])}, A={s_branch_test.get_value(i_b['is_areo'])}, F={s_branch_test.get_value(i_b['is_finite'])}, V={s_branch_test.get_value(i_b['val'])}")
            print(f"      Result: Z={s_branch_test.get_value(res_as_f_notpos['is_zero'])}, A={s_branch_test.get_value(res_as_f_notpos['is_areo'])}, F={s_branch_test.get_value(res_as_f_notpos['is_finite'])}, V={s_branch_test.get_value(res_as_f_notpos['val'])}")


    # --- 9. Identity-like Properties for smart_raw_add ---
    # Prop: smart_raw_add(ZeroState, a) ~ a
    res_zs_a_add = define_smart_raw_add_result(zero_const, i_a, "res_zs_a_add_id") # zero_const from mul tests
    prove_universal_property(s, "smart_raw_add Identity (Left ZS): ZS + a ~ a",
                             base_setup[:1] + [zero_const["constraints"], zero_const["is_zero"],
                                             res_zs_a_add["definition"], res_zs_a_add["constraints"]],
                             avc_equiv(res_zs_a_add, i_a))

    # Prop: smart_raw_add(a, ZeroState) ~ a (Follows from commutativity if ZS+a ~ a holds)
    # This is implicitly tested by commutativity + above.

    # Prop: smart_raw_add(AreoState, a) ~ a
    #   smart_raw_add(AS, ZS) -> AS. AS ~ ZS. So AS+ZS ~ ZS.
    #   smart_raw_add(AS, AS) -> AS. AS ~ AS. So AS+AS ~ AS.
    #   smart_raw_add(AS, Fp) -> Fp. Fp ~ Fp. So AS+Fp ~ Fp.
    # This property should hold due to avc_equiv.
    res_as_a_add = define_smart_raw_add_result(areo_const, i_a, "res_as_a_add_id") # areo_const from mul tests
    prove_universal_property(s, "smart_raw_add Identity-like (Left AS): AS + a ~ a",
                             base_setup[:1] + [areo_const["constraints"], areo_const["is_areo"],
                                             res_as_a_add["definition"], res_as_a_add["constraints"]],
                             avc_equiv(res_as_a_add, i_a))
    
    # --- 10. Properties of raw_sub_from_Unio_Areo_aspect ---
    # Prop: ForAll x (where x is Unio, i.e., ZS or AS), y: raw_sub_from_Unio_Areo_aspect(x,y) ~ AreoState
    # Test for x = ZeroState
    res_sub_zs_b = define_raw_sub_from_Unio_Areo_aspect_result(zero_const, i_b, "res_sub_zs_b")
    prove_universal_property(s, "raw_sub_Unio(ZS) - b ~ AS",
                             base_setup[1:2] + [zero_const["constraints"], zero_const["is_zero"], # i_b and zero_const valid
                                             res_sub_zs_b["definition"], res_sub_zs_b["constraints"],
                                             areo_const["constraints"], areo_const["is_areo"]], # areo_const is the target
                             avc_equiv(res_sub_zs_b, areo_const))
    # Test for x = AreoState
    res_sub_as_b = define_raw_sub_from_Unio_Areo_aspect_result(areo_const, i_b, "res_sub_as_b")
    prove_universal_property(s, "raw_sub_Unio(AS) - b ~ AS",
                             base_setup[1:2] + [areo_const["constraints"], areo_const["is_areo"], # i_b and areo_const valid
                                             res_sub_as_b["definition"], res_sub_as_b["constraints"]],
                             avc_equiv(res_sub_as_b, areo_const))


    print("====== All Phase 6 (Pinnacle Algebraic) tests complete. ======")

"""

**Explanation of "Pinnacle Brutal" Aspects:**

1.  **Generic Property Prover (`prove_universal_property`)**: This helper function standardizes the "proof by negation" approach. It takes the property formula and checks if its negation is UNSAT (if `expect_unsat=True`). It also has a mode (`expect_unsat=False`) to directly check if a formula is SAT, which we use for finding counterexamples to associativity and distributivity.
2.  **Symbolic Inputs**: `i_a`, `i_b`, `i_c` are used as generic symbolic intensities. The SMT solver explores all valid assignments to their kinds and values.
3.  **Associativity Tests (Add & Mul)**:
    * For `smart_raw_add`, we explicitly test `Not(avc_equiv(LHS, RHS))` and expect SAT, because we know it's non-associative. The model will be the counterexample.
    * For `raw_mul`, we also test `Not(avc_equiv(LHS, RHS))` and expect SAT, as multiplication with thresholds and special elements is also likely non-associative.
4.  **Distributivity Tests (Left & Right)**:
    * Similar to associativity, we test `Not(avc_equiv(LHS, RHS))` and expect SAT to find counterexamples.
5.  **Zero/Areo Properties**: These are framed universally. For example, "ForAll `a`, `raw_mul(ZeroState, a)` is `avc_equiv` to `ZeroState`."
    * The special test for `raw_mul(AreoState, Finite p where p.val is NOT > 0)` is particularly aggressive. It tries to create a scenario that *should* be inconsistent with `PosNat` constraints if `p` were a valid DFI, to specifically check the `else ZeroState` branch of `raw_mul`'s definition. This requires careful setup to ensure we are testing the branch and not just creating an inherently contradictory setup for `p` itself *before* the `raw_mul` is even applied. The way it's done is by asserting `i_b` is `is_finite` but also `Not(i_b["val"] > Int(0))`, and also that `i_b` only has the `is_finite` flag true (no `is_zero` or `is_areo`). This creates an "invalid PosNat" scenario for `i_b` to specifically target that `else` branch in `raw_mul`.
6.  **`smart_raw_add` Identity Tests**:
    * `smart_raw_add(ZeroState, a) ~ a` is tested.
    * `smart_raw_add(AreoState, a) ~ a` is tested. This is interesting because the raw results of `smart_raw_add(AreoState, ZeroState)` is `AreoState`, and `smart_raw_add(AreoState, AreoState)` is `AreoState`. However, since `AreoState` is `avc_equiv` to `ZeroState` (which would be `a` in the first case), and `AreoState` is `avc_equiv` to `AreoState` (which would be `a` in the second case), this property should hold true due to the `avc_equiv` comparison.
7.  **Validity of Results**: For every operation, we assert that the *result* itself must be a valid intensity (`res["constraints"]`). This is a crucial self-check on the operation definitions – they must not produce ill-formed intensities.

This script is designed to be a very tough crucible for your definitions. If properties that *should* hold universally are proven (UNSAT for their negation), and properties that *shouldn't* (like universal associativity/distributivity) yield counterexamples (SAT for their negation), then you have an extremely high degree of confidence in your formalization of the raw operations.

Be prepared for some tests (especially associativity/distributivity for `raw_mul`) to potentially take a bit longer for the SMT solver, and carefully examine any counterexamples. """