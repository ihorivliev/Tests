from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
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

# --- Phase 2: Raw Operations Definitions (raw_div only for this script) ---
def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder, current_omega_smt):
    return op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)

def raw_div_logic_builder(i1, i2, res, current_omega_smt): 
    formulas = []
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE) 
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE)
    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])
    formulas.append(Implies(divisor_is_unio, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), 
        Or(
            And(i1["is_zero"], 
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            And(i1["is_areo"],  
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i1["is_finite"], 
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), 
                    rem_sym >= Int(0), rem_sym < i2["val"]), 
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)),
                    Ite(q_sym >= current_omega_smt, 
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))),
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))))); return And(formulas)

def define_raw_div_result(i1_repr, i2_repr, result_name_prefix: str, current_omega_smt):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_div_logic_builder, current_omega_smt)
    return res_repr

# --- Generic Property Prover (Copied) ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[Any], 
                                 # Formula representing the property we want to prove true universally
                                 # e.g., for commutativity: avc_equiv(op(a,b), op(b,a))
                                 property_to_prove_true: Any, 
                                 model_vars_to_print: List[Dict[str, Any]] = [],
                                 print_model_on_fail: bool = True 
                                 ):
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions: solver.add_assertion(assertion)
    
    # To prove "Property" holds universally, we check if "NOT Property" is UNSAT.
    # If "NOT Property" is SAT, then "Property" does NOT hold universally, and we found a counterexample.
    solver.add_assertion(Not(property_to_prove_true))
        
    result = solver.solve() 
    proved_universally = False # Assume it does not hold universally by default

    if not result: # If "NOT Property" is UNSAT
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved_universally = True
    else: # If "NOT Property" is SAT, then "Property" does NOT hold universally
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_fail:
            for var_repr in model_vars_to_print:
                # Check if value exists in model before trying to get it
                val_str = f"V={solver.get_value(var_repr['val'])}" if var_repr['val'] in solver.get_model() else "V=?"
                is_z_str = f"Z={solver.get_value(var_repr['is_zero'])}" if var_repr['is_zero'] in solver.get_model() else "Z=?"
                is_a_str = f"A={solver.get_value(var_repr['is_areo'])}" if var_repr['is_areo'] in solver.get_model() else "A=?"
                is_f_str = f"F={solver.get_value(var_repr['is_finite'])}" if var_repr['is_finite'] in solver.get_model() else "F=?"
                print(f"  {var_repr['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
            
    solver.pop() 
    print("-" * 70)
    return proved_universally


# --- Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Division Algebra: Associativity Test ======\n")
    
    s = Solver(name="z3") 
    current_omega = DEFAULT_OMEGA_MAX_VAL_NAT_SMT

    # Symbolic Intensities for the associativity test a/(b/c) vs (a/b)/c
    a_div_assoc = create_intensity_representation("a_div_assoc")
    b_div_assoc = create_intensity_representation("b_div_assoc")
    c_div_assoc = create_intensity_representation("c_div_assoc")
    
    # Base assertions: all symbolic intensities must be valid
    base_setup_abc_div = [
        a_div_assoc["constraints"], 
        b_div_assoc["constraints"], 
        c_div_assoc["constraints"]
    ]

    # --- Test Associativity of raw_div ---
    # Property: (a/b)/c ~ a/(b/c)
    # We expect this to FAIL (i.e., its negation to be SAT, providing a counterexample)

    # LHS = (a/b)/c
    res_ab_div = define_raw_div_result(a_div_assoc, b_div_assoc, "res_ab_div_assoc", current_omega)
    lhs_final_div = define_raw_div_result(res_ab_div, c_div_assoc, "lhs_final_div_assoc", current_omega)

    # RHS = a/(b/c)
    res_bc_div = define_raw_div_result(b_div_assoc, c_div_assoc, "res_bc_div_assoc", current_omega)
    rhs_final_div = define_raw_div_result(a_div_assoc, res_bc_div, "rhs_final_div_assoc", current_omega)

    # Assertions for the setup, including definitions and constraints of intermediate results
    associativity_setup = base_setup_abc_div + [
        res_ab_div["definition"], res_ab_div["constraints"],
        lhs_final_div["definition"], lhs_final_div["constraints"],
        res_bc_div["definition"], res_bc_div["constraints"],
        rhs_final_div["definition"], rhs_final_div["constraints"]
    ]

    # The property we are testing if it holds universally is: avc_equiv(lhs_final_div, rhs_final_div)
    # prove_or_find_counterexample will assert NOT(this_property)
    # If that is SAT, it means associativity fails, and we get a counterexample.
    # If that is UNSAT, it means associativity holds universally (less likely for division).
    
    associativity_holds = prove_or_find_counterexample(s, 
                                        "Associativity of raw_div: (a/b)/c ~ a/(b/c)",
                                        associativity_setup,
                                        avc_equiv(lhs_final_div, rhs_final_div),
                                        model_vars_to_print=[a_div_assoc, b_div_assoc, c_div_assoc, 
                                                             res_ab_div, lhs_final_div, 
                                                             res_bc_div, rhs_final_div],
                                        print_model_on_fail=True)

    if not associativity_holds:
        print("  Analysis: As expected, raw_div is NOT universally associative.")
        print("  The counterexample above shows specific values of a, b, c for which the law fails.")
        print("  This is typically due to division by Unio (ZS/AS) or Finite/Finite cases hitting Omega threshold differently.")
    else:
        print("  Analysis: Surprisingly, raw_div was found to be associative. This warrants very close inspection of the proof or definitions.")

    print("\n====== AVC Division Algebra Test Complete ======")

"""

**Key Features of this `AVC_DivisionAlgebra.py`:**

1.  **Focused Test**: The primary goal is to test the associativity of `raw_div`.
2.  **Symbolic Inputs**: `a_div_assoc`, `b_div_assoc`, `c_div_assoc` are fully symbolic, allowing the SMT solver to explore all valid `Intensity` combinations.
3.  **Step-by-Step Symbolic Computation**:
    * LHS: `temp_lhs = raw_div(a,b)`, then `final_lhs = raw_div(temp_lhs, c)`.
    * RHS: `temp_rhs = raw_div(b,c)`, then `final_rhs = raw_div(a, temp_rhs)`.
    * For each intermediate and final result, its `definition` (how it's computed by `raw_div_logic_builder`) and its `constraints` (ensuring it's a valid `Intensity`) are asserted to the solver. This is crucial for rigor.
4.  **Testing the Associativity Property**:
    * The `property_to_prove_true` passed to `prove_or_find_counterexample` is `avc_equiv(final_lhs, final_rhs)`.
    * The helper function will assert `Not(avc_equiv(final_lhs, final_rhs))`.
    * If this assertion (along with all setup assertions) is **SATISFIABLE**, it means the SMT solver has found a counterexample: specific `a, b, c` (and their kinds/values) for which `(a/b)/c` is *not* `avc_equiv` to `a/(b/c)`. The script is set up to print these model values. This is the **expected outcome** for a "break."
    * If it were UNSAT (highly unlikely for division associativity in this system), it would mean `raw_div` is associative.
5.  **Clarity in `prove_or_find_counterexample`**: The helper function's logic is now very clear: it tries to prove `property_to_prove_true` by checking if `Not(property_to_prove_true)` is UNSAT. If `Not(property_to_prove_true)` is SAT, then the original property does not hold universally, and a counterexample has been found.

**What to Expect from the Output:**

* **`Associativity of raw_div: (a/b)/c ~ a/(b/c)` --- Result: SAT. Property ... does NOT hold universally. Counterexample found: ❌**
    * This is the most likely and most insightful outcome.
    * The printed model for `a_div_assoc`, `b_div_assoc`, `c_div_assoc`, and the intermediate and final LHS/RHS results will be the key. You'll need to manually trace these values through your `raw_div_logic_builder` (as we did for non-associativity of addition) to understand *why* the law breaks for that specific instance. It will likely involve division by Unio or thresholding in the `Finite/Finite` case.

This script is designed to give `raw_div` a very tough algebraic challenge. Let's see what the SMT solver uncove..."""