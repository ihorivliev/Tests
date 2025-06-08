from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from typing import Callable, List, Dict, Any

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [3, 5, 7, 10] 
DEFAULT_OMEGA_MAX_VAL_NAT = Int(7) 

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

# --- Helper to assert an intensity is a specific concrete Finite value ---
# MOVED HERE - START
def assert_is_concrete_finite(solver, intensity_repr, value: int, current_omega_val_for_posnat_check: int): # Parameter current_omega_val_for_posnat_check not strictly needed here but kept for consistency
    solver.add_assertion(intensity_repr["constraints"]) 
    solver.add_assertion(intensity_repr["is_finite"])
    solver.add_assertion(Not(intensity_repr["is_zero"]))
    solver.add_assertion(Not(intensity_repr["is_areo"]))
    solver.add_assertion(Equals(intensity_repr["val"], Int(value)))
    # The check `0 < value < current_omega_val_for_posnat_check` is more for test setup sanity,
    # as `intensity_repr["constraints"]` already enforces `val > 0`.
    if not (value > 0): # Explicit check for PosNat part of concrete assertion
        print(f"WARNING for {intensity_repr['name']}: assert_is_concrete_finite called with non-positive value {value}. This will conflict with PosNat constraint if constraints are also asserted directly on this value.")


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
# MOVED HERE - END


# --- Phase 2: Raw Operations Definitions (Copied) ---
def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder, current_omega):
    core_logic_formula = op_logic_builder(i1_repr, i2_repr, res_repr, current_omega)
    return core_logic_formula 

def smart_raw_add_logic_builder(i1, i2, res, current_omega):
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
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), Ite(val_sum >= current_omega, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)))))
    return And(formulas)

def define_smart_raw_add_result(i1_repr, i2_repr, result_name_prefix: str, current_omega):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder, current_omega)
    return res_repr

def raw_mul_logic_builder(i1, i2, res, current_omega):
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
        Ite(val_prod >= current_omega, 
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_prod)) 
        )))
    return And(formulas)

def define_raw_mul_result(i1_repr, i2_repr, result_name_prefix: str, current_omega):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_mul_logic_builder, current_omega)
    return res_repr

# --- Generic Property Prover (copied and slightly enhanced) ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[Any], 
                                 property_to_prove_true: Any, 
                                 model_vars_to_print: List[Dict[str, Any]] = [],
                                 print_model_on_fail: bool = True 
                                 ):
    # This function tries to prove 'property_to_prove_true' holds given 'setup_assertions'.
    # It does this by checking if (setup_assertions AND NOT property_to_prove_true) is UNSAT.
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions:
        solver.add_assertion(assertion)
    
    solver.add_assertion(Not(property_to_prove_true)) # Assert negation of the property
        
    result = solver.solve() # Check if "NOT Property" is SAT
    proved = False

    if not result: # If "NOT Property" is UNSAT
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved = True
    else: # If "NOT Property" is SAT, then "Property" does not hold universally
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


# --- Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Brutal Stress Test Part 2: Cancellation & Idempotence ======\n")
    
    s = Solver(name="z3") 

    i_a = create_intensity_representation("i_a_cxl") 
    i_b = create_intensity_representation("i_b_cxl")
    i_c = create_intensity_representation("i_c_cxl")
    
    base_setup_abc = [i_a["constraints"], i_b["constraints"], i_c["constraints"]]
    base_setup_a = [i_a["constraints"]]

    current_omega_for_tests = DEFAULT_OMEGA_MAX_VAL_NAT 

    print("--- Testing Additive Cancellation for smart_raw_add ---")
    add_ab = define_smart_raw_add_result(i_a, i_b, "add_ab_cxl", current_omega_for_tests)
    add_ac = define_smart_raw_add_result(i_a, i_c, "add_ac_cxl", current_omega_for_tests)
    
    premise_add_cxl = And(add_ab["definition"], add_ab["constraints"],
                          add_ac["definition"], add_ac["constraints"],
                          avc_equiv(add_ab, add_ac))
    conclusion_add_cxl = avc_equiv(i_b, i_c)
    
    prove_or_find_counterexample(s, "Additive Cancellation: (a+b ~ a+c) => (b ~ c)",
                                 base_setup_abc + [premise_add_cxl], 
                                 conclusion_add_cxl, 
                                 model_vars_to_print=[i_a, i_b, i_c, add_ab, add_ac],
                                 print_model_on_fail=True)


    print("--- Testing Multiplicative Cancellation for raw_mul ---")
    mul_ab = define_raw_mul_result(i_a, i_b, "mul_ab_cxl", current_omega_for_tests)
    mul_ac = define_raw_mul_result(i_a, i_c, "mul_ac_cxl", current_omega_for_tests)
    
    zs_const_cxl = create_intensity_representation("zs_const_cxl")
    
    premise_mul_cxl = And(mul_ab["definition"], mul_ab["constraints"],
                          mul_ac["definition"], mul_ac["constraints"],
                          zs_const_cxl["constraints"], zs_const_cxl["is_zero"], 
                          avc_equiv(mul_ab, mul_ac),
                          Not(avc_equiv(i_a, zs_const_cxl))) 
    conclusion_mul_cxl = avc_equiv(i_b, i_c)

    prove_or_find_counterexample(s, "Multiplicative Cancellation: (a*b ~ a*c ^ a!~ZS) => (b ~ c)",
                                 base_setup_abc + [premise_mul_cxl],
                                 conclusion_mul_cxl,
                                 model_vars_to_print=[i_a, i_b, i_c, mul_ab, mul_ac],
                                 print_model_on_fail=True)

    print("--- Testing Idempotence ---")
    add_aa = define_smart_raw_add_result(i_a, i_a, "add_aa_idem", current_omega_for_tests)
    prove_or_find_counterexample(s, "Idempotence for smart_raw_add: a+a ~ a",
                                 base_setup_a + [add_aa["definition"], add_aa["constraints"]],
                                 avc_equiv(add_aa, i_a),
                                 model_vars_to_print=[i_a, add_aa],
                                 print_model_on_fail=True)

    mul_aa = define_raw_mul_result(i_a, i_a, "mul_aa_idem", current_omega_for_tests)
    prove_or_find_counterexample(s, "Idempotence for raw_mul: a*a ~ a",
                                 base_setup_a + [mul_aa["definition"], mul_aa["constraints"]],
                                 avc_equiv(mul_aa, i_a),
                                 model_vars_to_print=[i_a, mul_aa],
                                 print_model_on_fail=True)

    print("\n--- Part E (cont.): Systematic Omega Threshold Tests for raw_mul ---")
    i1_omega_mul = create_intensity_representation("i1_omega_mul_param")
    i2_omega_mul = create_intensity_representation("i2_omega_mul_param")
    exp_omega_mul = create_intensity_representation("exp_omega_mul_param")

    for omega_val_py in OMEGA_VARIANTS_TO_TEST:
        current_omega_smt_val = Int(omega_val_py)
        print(f"--- Testing raw_mul thresholds with Omega_max_val_nat = {omega_val_py} ---")
        
        s_omega_mul = Solver(name="z3") 

        # Test Case 4a: F(k1) * F(k2) = F(k1*k2) where product < Omega and product > 0
        if omega_val_py > 1: 
            k1_lt = 1 if omega_val_py <= 2 else 2 
            k2_lt = 1 if omega_val_py <= 2 else 2 
            if k1_lt * k2_lt < omega_val_py and k1_lt*k2_lt > 0 :
                s_omega_mul.push()
                # Setup inputs within the solver context for this specific test
                current_setup = [
                    i1_omega_mul["constraints"], i1_omega_mul["is_finite"], Equals(i1_omega_mul["val"], Int(k1_lt)),
                    i2_omega_mul["constraints"], i2_omega_mul["is_finite"], Equals(i2_omega_mul["val"], Int(k2_lt)),
                    exp_omega_mul["constraints"], exp_omega_mul["is_finite"], Equals(exp_omega_mul["val"], Int(k1_lt * k2_lt))
                ]
                actual_mul_lt = define_raw_mul_result(i1_omega_mul, i2_omega_mul, f"act_mul_lt_o{omega_val_py}", current_omega_smt_val)
                current_setup.extend([actual_mul_lt["definition"], actual_mul_lt["constraints"]])
                
                prove_or_find_counterexample(s_omega_mul, f"Threshold Mul: F({k1_lt})*F({k2_lt})=F({k1_lt*k2_lt}) (Omega={omega_val_py})",
                                         current_setup, avc_equiv(actual_mul_lt, exp_omega_mul))
                s_omega_mul.pop()
        
        if omega_val_py > 0 : 
            k1_eq = omega_val_py 
            k2_eq = 1
            if k1_eq * k2_eq == omega_val_py: 
                s_omega_mul.push()
                current_setup = [
                    i1_omega_mul["constraints"], i1_omega_mul["is_finite"], Equals(i1_omega_mul["val"], Int(k1_eq)),
                    i2_omega_mul["constraints"], i2_omega_mul["is_finite"], Equals(i2_omega_mul["val"], Int(k2_eq)),
                    exp_omega_mul["constraints"], exp_omega_mul["is_areo"] # Expected is Areo
                ]
                actual_mul_eq = define_raw_mul_result(i1_omega_mul, i2_omega_mul, f"act_mul_eq_o{omega_val_py}", current_omega_smt_val)
                current_setup.extend([actual_mul_eq["definition"], actual_mul_eq["constraints"]])

                prove_or_find_counterexample(s_omega_mul, f"Threshold Mul: F({k1_eq})*F({k2_eq})=Areo (Omega={omega_val_py})",
                                         current_setup, avc_equiv(actual_mul_eq, exp_omega_mul))
                s_omega_mul.pop()

        if omega_val_py > 2: 
            k1_gt = omega_val_py - 1
            k2_gt = 2
            if k1_gt > 0 and k1_gt * k2_gt > omega_val_py : # Ensure k1_gt is valid PosNat
                s_omega_mul.push()
                current_setup = [
                    i1_omega_mul["constraints"], i1_omega_mul["is_finite"], Equals(i1_omega_mul["val"], Int(k1_gt)),
                    i2_omega_mul["constraints"], i2_omega_mul["is_finite"], Equals(i2_omega_mul["val"], Int(k2_gt)),
                    exp_omega_mul["constraints"], exp_omega_mul["is_areo"] # Expected is Areo
                ]
                actual_mul_gt = define_raw_mul_result(i1_omega_mul, i2_omega_mul, f"act_mul_gt_o{omega_val_py}", current_omega_smt_val)
                current_setup.extend([actual_mul_gt["definition"], actual_mul_gt["constraints"]])
                prove_or_find_counterexample(s_omega_mul, f"Threshold Mul: F({k1_gt})*F({k2_gt})=Areo (Omega={omega_val_py})",
                                         current_setup, avc_equiv(actual_mul_gt, exp_omega_mul))
                s_omega_mul.pop()
        del s_omega_mul 
        print("-" * 50)

    print("\n====== AVC Brutal Stress Test Part 2 Complete ======")

"""

**Summary of Fixes and Changes:**

1.  **Import `FALSE`**: Added `FALSE` to the import from `pysmt.shortcuts`.
2.  **Copied Helper Functions**: The definitions for `assert_is_concrete_finite`, `assert_is_concrete_zerostate`, and `assert_is_concrete_areostate` are now included in this script.
3.  **Refined `prove_or_find_counterexample`**:
    * The logic for `expect_unsat` was inverted. It now correctly tries to prove `property_to_prove_true` by checking if `Not(property_to_prove_true)` is UNSAT.
    * The model printing is slightly improved to check if variables are in the model before trying to get their value, which can prevent errors if the solver doesn't assign values to all variables (especially if a contradiction is found early).
4.  **Corrected `prove_universal_property` calls in Part E (Omega Threshold Tests for `raw_mul`)**:
    * The `setup_assertions` for these concrete tests were missing. I've added a `current_setup` list within each specific test case (4a, 4b, 4c) that includes the constraints for `i1_omega_mul`, `i2_omega_mul` (making them specific finite values) and `exp_omega_mul` (making it the expected finite or AreoState). This `current_setup` is then passed to `prove_or_find_counterexample`.
    * The `prove_or_find_counterexample` expects the `setup_assertions` to fully define the context. The property itself (`avc_equiv(actual, expected)`) is then tested within that context.
    * Ensured `k1_gt > 0` before using `assert_is_concrete_finite` for it.
    * Used `s_omega_mul.push()` and `s_omega_mul.pop()` to isolate assertions for each sub-test within the Omega loop, ensuring a clean state for the next sub-test.

With these corrections, the script should now run through the "Part E" Omega variant tests correctly. The failures you observed for Cancellation and Idempotence are significant findings about your AVC system's algebraic properties. """ 