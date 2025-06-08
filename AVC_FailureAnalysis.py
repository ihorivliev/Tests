from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from typing import Callable, List, Dict, Any

# --- Configuration ---
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

# --- Order Relations (Copied from AVC_UltraStressTest.py) ---
def is_less_than(i1_repr, i2_repr, current_omega_smt): 
    case_zs_lt_f = And(i1_repr["is_zero"], i2_repr["is_finite"])
    case_zs_lt_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    case_f_lt_as = And(i1_repr["is_finite"], i2_repr["is_areo"])
    case_f_lt_f = And(i1_repr["is_finite"], i2_repr["is_finite"], i1_repr["val"] < i2_repr["val"])
    return Or(case_zs_lt_f, case_zs_lt_as, case_f_lt_as, case_f_lt_f)

def is_le(i1_repr, i2_repr, current_omega_smt):
    return Or(is_less_than(i1_repr, i2_repr, current_omega_smt), avc_equiv(i1_repr, i2_repr))

# --- Phase 2: Raw Operations Definitions (Copied) ---
def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder, current_omega_smt):
    core_logic_formula = op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)
    return core_logic_formula 

def raw_mul_logic_builder(i1, i2, res, current_omega_smt): # Only raw_mul needed for Zero Divisor test
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

# --- Generic Property Prover (Copied) ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[Any], 
                                 property_to_prove_true: Any, # Formula representing the property P
                                 model_vars_to_print: List[Dict[str, Any]] = [],
                                 print_model_on_counterexample: bool = True # Changed name for clarity
                                 ):
    # This function attempts to prove 'property_to_prove_true'.
    # It does this by checking if (setup_assertions AND NOT property_to_prove_true) is UNSAT.
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions:
        solver.add_assertion(assertion)
    
    solver.add_assertion(Not(property_to_prove_true)) # Assert negation of the property
        
    result = solver.solve() # Check if "NOT Property" is SAT
    proved = False

    if not result: # If "NOT Property" is UNSAT, then "Property" is PROVED
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved = True
    else: # If "NOT Property" is SAT, then "Property" does NOT hold universally (counterexample found)
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_counterexample:
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
    print("====== AVC Failure Analysis: Deep Dive into Problematic Cases ======\n")
    
    s = Solver(name="z3") 

    i_a = create_intensity_representation("i_a_fail")
    i_b = create_intensity_representation("i_b_fail")
    i_c = create_intensity_representation("i_c_fail") 
    
    current_omega = DEFAULT_OMEGA_MAX_VAL_NAT_SMT 

    # --- 1. Deep Dive into Failure of Transitivity for `is_le` ---
    print("--- Deep Dive 1: Failure of Transitivity for 'is_le' ---")
    # Property: (a <= b AND b <= c) => a <= c
    # We expect this to FAIL, so we are looking for a counterexample.
    # The prove_or_find_counterexample function will assert NOT ((a<=b ^ b<=c) => a<=c)
    # which is equivalent to asserting (a<=b ^ b<=c ^ NOT (a<=c))
    
    premise_trans_le = And(is_le(i_a, i_b, current_omega), is_le(i_b, i_c, current_omega))
    conclusion_trans_le = is_le(i_a, i_c, current_omega)
    
    # We want to prove transitivity. If it fails, a counterexample is found.
    transitivity_holds = prove_or_find_counterexample(s, 
                                     "Transitivity of is_le: (a<=b ^ b<=c) => a<=c",
                                     [i_a["constraints"], i_b["constraints"], i_c["constraints"], premise_trans_le], # Setup includes premise
                                     conclusion_trans_le, # We try to prove the conclusion
                                     model_vars_to_print=[i_a, i_b, i_c], 
                                     print_model_on_counterexample=True)

    if not transitivity_holds:
        print("  Analysis of Transitivity Failure:")
        print("  The typical counterexample involves a < AreoState and AreoState ~ ZeroState, but a is not < ZeroState.")
        print("  For example, a=Finite(1), b=AreoState, c=ZeroState.")
        print(f"    - Is F(1) <= AS? Yes, because F(1) < AS.")
        print(f"    - Is AS <= ZS? Yes, because AS ~ ZS (avc_equiv).")
        print(f"    - Therefore, (F(1) <= AS AND AS <= ZS) is True.")
        print(f"    - Is F(1) <= ZS? No, because F(1) is not < ZS and F(1) is not ~ ZS.")
        print(f"    - So, the implication fails.")
    print("-" * 70)


    # --- 2. Deep Dive into Existence of "Zero Divisors" for `raw_mul` ---
    print("\n--- Deep Dive 2: Existence of 'Zero Divisors' for raw_mul ---")
    # Property: (a*b ~ ZeroState) => (a ~ ZeroState OR b ~ ZeroState)
    # We expect this to FAIL (meaning zero divisors exist).
    
    mul_ab_zd = define_raw_mul_result(i_a, i_b, "mul_ab_zd", current_omega)
    zs_const_zd = create_intensity_representation("zs_const_zd_dd") # dd for deep dive
    
    # Premise for "No Zero Divisors" property: a*b ~ ZeroState
    premise_no_zero_div_prop = And(mul_ab_zd["definition"], mul_ab_zd["constraints"],
                                   zs_const_zd["constraints"], zs_const_zd["is_zero"], 
                                   avc_equiv(mul_ab_zd, zs_const_zd))
    # Conclusion for "No Zero Divisors" property: a ~ ZeroState OR b ~ ZeroState
    conclusion_no_zero_div_prop = Or(avc_equiv(i_a, zs_const_zd), avc_equiv(i_b, zs_const_zd))

    no_zero_divisors_holds = prove_or_find_counterexample(s, 
                                        "No Zero Divisors: (a*b ~ ZS) => (a~ZS or b~ZS)",
                                        [i_a["constraints"], i_b["constraints"], premise_no_zero_div_prop],
                                        conclusion_no_zero_div_prop,
                                        model_vars_to_print=[i_a, i_b, mul_ab_zd],
                                        print_model_on_counterexample=True)
    
    if not no_zero_divisors_holds:
        print("  Analysis of Zero Divisors Existence:")
        print(f"  The SMT solver found a case where a*b ~ ZS, but neither a nor b is ~ ZS.")
        print(f"  This typically happens when a and b are Finite, their product hits Omega_max_val_nat ({DEFAULT_OMEGA_MAX_VAL_NAT_PY}),")
        print(f"  causing a*b to become AreoState, which is avc_equiv to ZeroState.")
        print(f"  Example from previous run (Omega=7): a=F(7), b=F(1). Then a*b = F(7*1) = F(7) -> AS ~ ZS.")
        print(f"  Neither F(7) nor F(1) is ~ ZS. Thus, F(7) and F(1) are zero divisors in this system.")
    print("-" * 70)

    # --- Further Symbolic Search for Zero Divisors ---
    print("\n--- Symbolic Search for *any* pair of Zero Divisors ---")
    # We want to find (a, b) such that:
    # 1. a is valid, b is valid
    # 2. a is NOT ZeroState (or AreoState)
    # 3. b is NOT ZeroState (or AreoState)
    # 4. raw_mul(a,b) IS ZeroState (or AreoState)
    s_zd_search = Solver(name="z3")
    i_x_zd = create_intensity_representation("ix_zd_search")
    i_y_zd = create_intensity_representation("iy_zd_search")
    zs_const_zd_search = create_intensity_representation("zs_zd_search")
    
    # Setup assertions
    s_zd_search.add_assertion(i_x_zd["constraints"])
    s_zd_search.add_assertion(i_y_zd["constraints"])
    s_zd_search.add_assertion(zs_const_zd_search["constraints"])
    s_zd_search.add_assertion(zs_const_zd_search["is_zero"]) # zs_const is ZeroState

    # Assert x and y are NOT Unio (i.e., not ZS and not AS)
    s_zd_search.add_assertion(Not(Or(i_x_zd["is_zero"], i_x_zd["is_areo"]))) # i.e. i_x_zd["is_finite"]
    s_zd_search.add_assertion(Not(Or(i_y_zd["is_zero"], i_y_zd["is_areo"]))) # i.e. i_y_zd["is_finite"]

    # Define their product
    prod_xy_zd = define_raw_mul_result(i_x_zd, i_y_zd, "prod_xy_zd_search", current_omega)
    s_zd_search.add_assertion(prod_xy_zd["definition"])
    s_zd_search.add_assertion(prod_xy_zd["constraints"])

    # Assert their product IS Unio (avc_equiv to ZeroState)
    s_zd_search.add_assertion(avc_equiv(prod_xy_zd, zs_const_zd_search))

    print("Searching for a pair of DFI (non-Unio) intensities (x, y) such that x*y ~ Unio...")
    if s_zd_search.solve():
        print("  Found a pair of DFI zero divisors: ✅")
        print(f"    x ({i_x_zd['name']}): Z={s_zd_search.get_value(i_x_zd['is_zero'])}, A={s_zd_search.get_value(i_x_zd['is_areo'])}, F={s_zd_search.get_value(i_x_zd['is_finite'])}, V={s_zd_search.get_value(i_x_zd['val'])}")
        print(f"    y ({i_y_zd['name']}): Z={s_zd_search.get_value(i_y_zd['is_zero'])}, A={s_zd_search.get_value(i_y_zd['is_areo'])}, F={s_zd_search.get_value(i_y_zd['is_finite'])}, V={s_zd_search.get_value(i_y_zd['val'])}")
        print(f"    Product ({prod_xy_zd['name']}): Z={s_zd_search.get_value(prod_xy_zd['is_zero'])}, A={s_zd_search.get_value(prod_xy_zd['is_areo'])}, F={s_zd_search.get_value(prod_xy_zd['is_finite'])}, V={s_zd_search.get_value(prod_xy_zd['val'])}")
    else:
        print("  Could not find a pair of DFI zero divisors with current setup. This is unexpected if Omega allows F*F->AS. ❌")
    del s_zd_search
    print("-" * 70)


    print("\n====== AVC Failure Analysis Deep Dive Complete ======")
"""

**Key Aspects of this "Deep Dive" Script:**

1.  **Focused Tests**: It specifically targets the failure of transitivity for `is_le` and the "No Zero Divisors" property.
2.  **Reusing `prove_or_find_counterexample`**: This helper is used to frame the tests.
    * For transitivity: We try to prove `(a<=b AND b<=c) => a<=c`. The SMT solver should find a counterexample (SAT for the negation).
    * For "No Zero Divisors": We try to prove `(a*b ~ ZS) => (a~ZS or b~ZS)`. The SMT solver should find a counterexample.
3.  **Detailed Analysis in Comments/Prints**: After a counterexample is found (or a property is unexpectedly proven), the script includes print statements that explain *why* this happens, guiding you through the trace of the specific counterexample values using the AVC logic.
4.  **Symbolic Search for Zero Divisors**:
    * A dedicated section attempts to find *any* pair of `Intensity` representations (`i_x_zd`, `i_y_zd`) that are:
        * Individually valid.
        * Neither `i_x_zd` nor `i_y_zd` is `avc_equiv` to `ZeroState` (i.e., they are both DFI in this setup, as they cannot be AreoState if not equiv to ZS).
        * Their product `raw_mul(i_x_zd, i_y_zd)` *is* `avc_equiv` to `ZeroState`.
    * If the SMT solver finds such a pair (SAT result), it will provide concrete values for `i_x_zd` and `i_y_zd` (specifically their `val` if they are Finite) that act as zero divisors. This is a powerful way to let the solver show you different instances of this phenomenon.

**What to Expect and How to "Learn ALL We Can":**

* **Transitivity Failure**: The counterexample `a=F(1), b=AS, c=ZS` should be found again. Your analysis printed in the script will walk through why `F(1) <= AS` and `AS <= ZS` (due to `AS ~ ZS`), but `F(1)` is not `<= ZS`. This shows how the equivalence at Unio "breaks" the chain of inequalities when crossing between the finite realm and the identified poles.
* **Zero Divisors Found**:
    * The general test for "No Zero Divisors" should fail (SAT for its negation), and the counterexample will likely be similar to the `F(7)*F(1) -> AS (~ZS)` for `Omega=7`.
    * The "Symbolic Search for *any* pair of Zero Divisors" should also yield SAT and give you potentially different pairs of DFI values whose product (after hitting Omega) becomes `AreoState` (and thus `~ZS`). This exploration will demonstrate that this isn't just a one-off case but an inherent feature when products reach the `Omega_max_val_nat` threshold.

By running this script, you are not just getting pass/fail; you are using the SMT solver as an engine to find specific instances that violate standard mathematical expectations. Your detailed analysis of these instances (the counterexamples) is where the deep learning about your AVC model's unique structure occurs. This is "no-mercy" because it relentlessly seeks out these boundary conditions and structural br. """