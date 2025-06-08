from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from typing import Callable, List, Dict, Any

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [3, 5, 7, 10] # Kept for potential future use, but this script focuses on DEFAULT_OMEGA
DEFAULT_OMEGA_MAX_VAL_NAT_PY = 7 
DEFAULT_OMEGA_MAX_VAL_NAT_SMT = Int(DEFAULT_OMEGA_MAX_VAL_NAT_PY)

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
def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder, current_omega_smt):
    core_logic_formula = op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)
    return core_logic_formula 

def smart_raw_add_logic_builder(i1, i2, res, current_omega_smt):
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
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), Ite(val_sum >= current_omega_smt, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)))))
    return And(formulas)

def define_smart_raw_add_result(i1_repr, i2_repr, result_name_prefix: str, current_omega_smt):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder, current_omega_smt)
    return res_repr

def raw_mul_logic_builder(i1, i2, res, current_omega_smt):
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
        Ite(val_prod >= current_omega_smt, 
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_prod)) 
        )))
    return And(formulas)

def define_raw_mul_result(i1_repr, i2_repr, result_name_prefix: str, current_omega_smt):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_mul_logic_builder, current_omega_smt)
    return res_repr

def raw_sub_from_Unio_Areo_aspect_logic_builder(i_unio_areo, _i_any, res, _current_omega_smt): 
    return And(Implies(Or(i_unio_areo["is_zero"], i_unio_areo["is_areo"], i_unio_areo["is_finite"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

def define_raw_sub_from_Unio_Areo_aspect_result(i1_repr, i2_repr, result_name_prefix: str, current_omega_smt):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_sub_from_Unio_Areo_aspect_logic_builder, current_omega_smt)
    return res_repr

# --- Generic Property Prover (Copied) ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[Any], 
                                 property_to_prove_true: Any, 
                                 model_vars_to_print: List[Dict[str, Any]] = [],
                                 print_model_on_fail: bool = True 
                                 ):
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions:
        solver.add_assertion(assertion)
    
    solver.add_assertion(Not(property_to_prove_true))
        
    result = solver.solve() 
    proved = False

    if not result: 
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved = True
    else: 
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_fail:
            for var_repr in model_vars_to_print:
                val_str = f"V={solver.get_value(var_repr['val'])}" if var_repr['val'] in solver.get_model() else "V=?"
                is_z_str = f"Z={solver.get_value(var_repr['is_zero'])}" if var_repr['is_zero'] in solver.get_model() else "Z=?"
                is_a_str = f"A={solver.get_value(var_repr['is_areo'])}" if var_repr['is_areo'] in solver.get_model() else "A=?"
                is_f_str = f"F={solver.get_value(var_repr['is_finite'])}" if var_repr['is_finite'] in solver.get_model() else "F=?"
                print(f"  {var_repr['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
            
    solver.pop() 
    print("-" * 70)
    return proved

# --- A. Defining Order Relations ---
def is_less_than(i1_repr, i2_repr, current_omega_smt): # current_omega_smt needed for DFI range, though not strictly for this basic order
    """Defines i1 < i2. Note: This is a strict 'less than' on representatives."""
    # ZS < F(any_p)
    case_zs_lt_f = And(i1_repr["is_zero"], i2_repr["is_finite"])
    # ZS < AS
    case_zs_lt_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    # F(any_p) < AS
    case_f_lt_as = And(i1_repr["is_finite"], i2_repr["is_areo"])
    # F(p1) < F(p2) if p1.val < p2.val
    case_f_lt_f = And(i1_repr["is_finite"], i2_repr["is_finite"], i1_repr["val"] < i2_repr["val"])
    
    return Or(case_zs_lt_f, case_zs_lt_as, case_f_lt_as, case_f_lt_f)

def is_le(i1_repr, i2_repr, current_omega_smt):
    """Defines i1 <= i2 as (i1 < i2) OR (i1 ~ i2)."""
    return Or(is_less_than(i1_repr, i2_repr, current_omega_smt), avc_equiv(i1_repr, i2_repr))

# --- Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Ultra Stress Test (Order, Zero Divisors, Monotonicity) ======\n")
    
    s = Solver(name="z3") 

    # Symbolic Intensities for tests
    i_a = create_intensity_representation("i_a_ultra")
    i_b = create_intensity_representation("i_b_ultra")
    i_c = create_intensity_representation("i_c_ultra") 
    
    base_setup_abc = [i_a["constraints"], i_b["constraints"], i_c["constraints"]]
    base_setup_ab = [i_a["constraints"], i_b["constraints"]]
    base_setup_a = [i_a["constraints"]]

    current_omega = DEFAULT_OMEGA_MAX_VAL_NAT_SMT # Using default Omega for these tests

    # --- A. Test Properties of the Order Relation ---
    print("--- Testing Properties of Order Relation 'is_le' ---")
    # A1. Reflexivity of is_le: a <= a
    prove_or_find_counterexample(s, "Reflexivity of is_le: a <= a",
                                 base_setup_a,
                                 is_le(i_a, i_a, current_omega))

    # A2. Antisymmetry of is_le (conceptual): (a <= b AND b <= a) => a ~ b
    #    This is key for it to be a partial order on equivalence classes.
    premise_antisym = And(is_le(i_a, i_b, current_omega), is_le(i_b, i_a, current_omega))
    conclusion_antisym = avc_equiv(i_a, i_b)
    prove_or_find_counterexample(s, "Antisymmetry of is_le: (a<=b ^ b<=a) => a~b",
                                 base_setup_ab + [premise_antisym],
                                 conclusion_antisym,
                                 model_vars_to_print=[i_a, i_b], print_model_on_fail=True)

    # A3. Transitivity of is_le: (a <= b AND b <= c) => a <= c
    premise_trans_le = And(is_le(i_a, i_b, current_omega), is_le(i_b, i_c, current_omega))
    conclusion_trans_le = is_le(i_a, i_c, current_omega)
    prove_or_find_counterexample(s, "Transitivity of is_le: (a<=b ^ b<=c) => a<=c",
                                 base_setup_abc + [premise_trans_le],
                                 conclusion_trans_le,
                                 model_vars_to_print=[i_a, i_b, i_c], print_model_on_fail=True)

    # --- C. Testing "No Zero Divisors" (for valid DFI, ZS, AS) ---
    # Property: raw_mul(a, b) ~ ZeroState => (a ~ ZeroState OR b ~ ZeroState)
    # Assuming a and b are valid DFI, ZS, or AS.
    print("\n--- Testing 'No Zero Divisors' for raw_mul ---")
    mul_ab_is_zs = define_raw_mul_result(i_a, i_b, "mul_ab_is_zs", current_omega)
    
    # Define ZeroState constant for avc_equiv comparison
    zs_const_zd = create_intensity_representation("zs_const_zd")
    
    premise_no_zero_div = And(mul_ab_is_zs["definition"], mul_ab_is_zs["constraints"],
                              zs_const_zd["constraints"], zs_const_zd["is_zero"], # Define ZS const
                              avc_equiv(mul_ab_is_zs, zs_const_zd)) # mul(a,b) ~ ZeroState
    conclusion_no_zero_div = Or(avc_equiv(i_a, zs_const_zd), avc_equiv(i_b, zs_const_zd))

    prove_or_find_counterexample(s, "No Zero Divisors: (a*b ~ ZS) => (a~ZS or b~ZS)",
                                 base_setup_ab + [premise_no_zero_div], # a and b are valid intensities
                                 conclusion_no_zero_div,
                                 model_vars_to_print=[i_a, i_b, mul_ab_is_zs], print_model_on_fail=True)

    # --- B. Testing Monotonicity of Operations ---
    print("\n--- Testing Monotonicity of Operations (Expect Failures) ---")
    # B1. Monotonicity of smart_raw_add: a <= b => a + c <= b + c
    add_ac_mono = define_smart_raw_add_result(i_a, i_c, "add_ac_mono", current_omega)
    add_bc_mono = define_smart_raw_add_result(i_b, i_c, "add_bc_mono", current_omega)
    premise_mono_add = is_le(i_a, i_b, current_omega)
    conclusion_mono_add = is_le(add_ac_mono, add_bc_mono, current_omega)
    
    prove_or_find_counterexample(s, "Monotonicity of smart_raw_add: (a<=b) => (a+c <= b+c)",
                                 base_setup_abc + [premise_mono_add, 
                                                   add_ac_mono["definition"], add_ac_mono["constraints"],
                                                   add_bc_mono["definition"], add_bc_mono["constraints"]],
                                 conclusion_mono_add,
                                 model_vars_to_print=[i_a, i_b, i_c, add_ac_mono, add_bc_mono], print_model_on_fail=True)

    # B2. Monotonicity of raw_mul: a <= b AND c > ZS_equiv => a * c <= b * c
    # (c > ZS_equiv means c is not ZS and not AS if we interpret ZS~AS as the smallest element class)
    # More simply: c is Finite or c is AreoState (which is ~ ZS, so this condition is tricky)
    # Let's test with c being strictly Finite and positive for a clearer multiplicative context.
    c_is_pos_finite = And(i_c["is_finite"], i_c["val"] > Int(0)) # c is a DFI

    mul_ac_mono = define_raw_mul_result(i_a, i_c, "mul_ac_mono", current_omega)
    mul_bc_mono = define_raw_mul_result(i_b, i_c, "mul_bc_mono", current_omega)
    premise_mono_mul = And(is_le(i_a, i_b, current_omega), c_is_pos_finite)
    conclusion_mono_mul = is_le(mul_ac_mono, mul_bc_mono, current_omega)

    prove_or_find_counterexample(s, "Monotonicity of raw_mul: (a<=b ^ c is DFI) => (a*c <= b*c)",
                                 base_setup_abc + [premise_mono_mul,
                                                   mul_ac_mono["definition"], mul_ac_mono["constraints"],
                                                   mul_bc_mono["definition"], mul_bc_mono["constraints"]],
                                 conclusion_mono_mul,
                                 model_vars_to_print=[i_a, i_b, i_c, mul_ac_mono, mul_bc_mono], print_model_on_fail=True)

    # --- D. Testing raw_sub_from_Unio_Areo_aspect with Non-Unio First Argument ---
    print("\n--- Testing raw_sub behavior with Non-Unio first argument ---")
    # Property: raw_sub(Finite(p), b) ~ AreoState
    # This should be PROVED based on the current definition of raw_sub_from_Unio_Areo_aspect_logic_builder
    p_finite_sub = create_intensity_representation("p_finite_sub")
    actual_sub_fp_b = define_raw_sub_from_Unio_Areo_aspect_result(p_finite_sub, i_b, "actual_sub_fp_b", current_omega)
    
    as_const_sub = create_intensity_representation("as_const_sub") # Expected AreoState

    prove_or_find_counterexample(s, "raw_sub(Finite(p), b) ~ AreoState",
                                 [p_finite_sub["constraints"], p_finite_sub["is_finite"], # p_finite_sub is a DFI
                                  i_b["constraints"], # b is any valid intensity
                                  as_const_sub["constraints"], as_const_sub["is_areo"], # Define AS const
                                  actual_sub_fp_b["definition"], actual_sub_fp_b["constraints"]],
                                 avc_equiv(actual_sub_fp_b, as_const_sub))


    print("\n====== AVC Ultra Stress Test (Order, Zero Divisors, Monotonicity) Complete ======")

"""

**Key Features of this `AVC_UltraStressTest.py`:**

1.  **Order Relations (`is_less_than`, `is_le`)**:
    * Defined based on the conceptual hierarchy: `ZeroState < Finite(p) < AreoState`, and `Finite(p1) < Finite(p2)` if `p1.val < p2.val`.
    * `is_le` incorporates `avc_equiv` for non-strict inequality.
    * Basic properties of `is_le` (reflexivity, antisymmetry w.r.t `avc_equiv`, transitivity) are tested to ensure it forms a valid partial order on the equivalence classes.

2.  **"No Zero Divisors" Test**:
    * Tests the property: `raw_mul(a, b) ~ ZeroState => (a ~ ZeroState OR b ~ ZeroState)`.
    * The inputs `a` and `b` are constrained to be valid intensities (which includes DFI having `val > 0`).
    * Given the `raw_mul` logic (especially `AreoState * Finite(p where p.val not > 0) -> ZeroState`), this test is crucial. If `a` and `b` are *valid* DFI, ZS, or AS, this property *should* hold. A failure would indicate an unexpected way to get Zero by multiplication.

3.  **Monotonicity Tests**:
    * These are classic algebraic properties. We test if `smart_raw_add` and `raw_mul` preserve the order `is_le`.
    * `a <= b => a + c <= b + c`
    * `a <= b AND c is DFI => a * c <= b * c` (using `c` as a DFI for a more standard multiplicative context).
    * **Expectation**: These are very likely to **FAIL** (i.e., the SMT solver will find counterexamples where the property does not hold universally) due to the `Omega_max_val_nat` threshold causing "wrap-around" or absorption to `AreoState`, which can invert or disrupt expected ordered outcomes. The counterexamples will be highly informative.

4.  **`raw_sub_from_Unio_Areo_aspect` with Non-Unio First Argument**:
    * The current definition of `raw_sub_from_Unio_Areo_aspect_logic_builder` implies that if the first argument is `Finite(p)`, the result is still `AreoState`. This test explicitly verifies this behavior.

5.  **Rigorous Testing Framework**:
    * Uses the refined `prove_or_find_counterexample` helper.
    * Symbolic variables `i_a, i_b, i_c` are used for universal properties.
    * All inputs are always asserted to be valid intensities via their `constraints`.
    * Results of operations are also asserted to be valid intensities.

**What to Expect from the Output:**

* **Order Properties (A)**: Reflexivity and Transitivity of `is_le` should ideally be PROVED. Antisymmetry (meaning if `a<=b` and `b<=a` then `a~b`) is crucial for `is_le` to be a partial order on the `avc_equiv` classes and should also be PROVED.
* **No Zero Divisors (C)**: This is a critical one. If your `raw_mul` is well-behaved for valid ZS, AS, and DFI inputs, this should be PROVED. A failure here would be a significant finding.
* **Monotonicity (B)**: Most likely, these will **FAIL** (Result: SAT, counterexample found). The interest lies in the *kind* of counterexamples the SMT solver finds – they will likely involve operations near the `Omega_max_val_nat` threshold or interactions with `AreoState`.
* **`raw_sub` with Finite (D)**: This should be PROVED based on the current definition in the script.

This script pushes into new territory by defining and testing order, which interacts in complex ways with your threshold arithmetic and special Unio state. Let the SMT solver do its work – the results will be very illuminative. """