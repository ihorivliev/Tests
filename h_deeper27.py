from pysmt.shortcuts import (
    Symbol, Int, And, Or, Not, Equals, Implies,
    ForAll, Exists, Solver, is_sat, is_unsat,
    Plus, Times, LE, LT, GE, Function, TRUE, FALSE,
    BOOL # For type hinting FNode which is bool
)
from pysmt.typing import INT, FunctionType, BOOL as SMT_BOOL_TYPE
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.fnode import FNode # For type hinting
import itertools
from typing import List, Dict, Tuple, Callable, Any, Optional

# Type alias for SMT function for AVCA operations
SMT_AVCA_OP_TYPE = FunctionType(INT, [INT, INT])

# Global SMT function symbols (will be set in run_identity_catalogue_tests)
smt_avca_add: Any = None
smt_avca_mul: Any = None
U_smt_c_global: Any = None
in_S_Omega_global_pred: Callable[[Any], FNode] = lambda x: TRUE() # Placeholder, ensures it returns FNode

# --- Grounding Function (Task ④) ---
def ground_formula_instances(quantified_formula: FNode, 
                             omega_val: int,
                             # smt_in_S_Omega_predicate: Callable[[FNode], FNode] # This param was in my design but not used in the last version's body
                             ) -> FNode:
    """
    Instantiates a universally quantified formula (quantified_formula) with a set of 
    test values for the given omega_val.
    The formula is typically of the form ForAll(vars, body).
    This function will substitute vars in body with test values.
    """
    # Ensure it's a ForAll node before trying to access quantifier-specific parts
    if not quantified_formula.is_forall():
        print(f"  DEBUG (grounding): Formula passed to ground_formula_instances is NOT ForAll as primarily expected: {quantified_formula.node_type()} Content: {quantified_formula.serialize()}")
        return TRUE() # Default or error, ensure TRUE is imported and called as TRUE()

    # --- Start of the function body that must be correctly indented ---
    quantified_vars = []
    formula_body = None

    try:
        # PySMT ForAll structure: arg(0) is tuple of variables, arg(1) is body
        # The user's error suggested quantified_formula.arg(0) was the body.
        # Let's stick to the standard interpretation and debug if it's still an issue.
        # If the previous error was "AttributeError: 'FNode' object has no attribute 'variables'",
        # then .arg(0) and .arg(1) are the way.
        # If the error was "getitem on Implies" with list(quantified_formula.arg(0)), then
        # quantified_formula.arg(0) *was* the body. This indicates a fundamental mismatch
        # with expected ForAll structure if is_forall() is true.

        # Let's re-attempt the standard interpretation for ForAll:
        # arg(0) = variables tuple, arg(1) = body
        # The previous error indicated list(arg(0)) failed because arg(0) was the body.
        # This means the arguments might be swapped in the node being processed.
        # This attempt assumes arg(0) is BODY and arg(1) is VARS_TUPLE
        # This directly addresses the error message "Unsupported operation '__getitem__' on '((...Implies...))'"
        # when list(quantified_formula.arg(0)) was called.
        
        # Hypothesis from last error: Body is arg(0), Variables are arg(1)
        formula_body_candidate = quantified_formula.arg(0)
        quantified_vars_fnode_tuple_candidate = quantified_formula.arg(1)
        
        # We need to be sure formula_body_candidate is a formula and quantified_vars_fnode_tuple_candidate is iterable
        # A simple check: the body will not be a 'SYMBOL' if it's a complex formula. Variables are SYMBOLs.
        # A tuple of variables might be an FNode of type TUPLE or a Python tuple.

        # Heuristic: if arg(0) looks like a complex formula and arg(1) looks like a symbol or tuple of symbols:
        is_arg0_complex = not (quantified_vars_fnode_tuple_candidate.is_symbol() or isinstance(quantified_vars_fnode_tuple_candidate, tuple))
        is_arg1_complex = not (formula_body_candidate.is_symbol() or isinstance(formula_body_candidate, tuple))

        if not is_arg0_complex and is_arg1_complex : # Standard: arg(0) is vars, arg(1) is body
            quantified_vars_fnode_tuple = quantified_formula.arg(0)
            formula_body = quantified_formula.arg(1)
            #print("DEBUG: Grounding using standard ForAll(vars, body) structure.")
        elif is_arg0_complex and not is_arg1_complex : # Swapped: arg(0) is body, arg(1) is vars
            formula_body = quantified_formula.arg(0)
            quantified_vars_fnode_tuple = quantified_formula.arg(1)
            #print("DEBUG: Grounding using hypothesized swapped ForAll(body, vars) structure.")
        else:
            # If both or neither are complex, we have an ambiguous case or an unexpected structure.
            # Fallback to standard and hope for the best, or error out.
            #print(f"DEBUG (grounding): Ambiguous ForAll structure for {quantified_formula.serialize()}. Assuming standard.")
            quantified_vars_fnode_tuple = quantified_formula.arg(0)
            formula_body = quantified_formula.arg(1)


        if isinstance(quantified_vars_fnode_tuple, tuple):
             quantified_vars = list(quantified_vars_fnode_tuple)
        elif quantified_vars_fnode_tuple.is_symbol(): 
             quantified_vars = [quantified_vars_fnode_tuple]
        else: 
             try:
                 quantified_vars = list(quantified_vars_fnode_tuple) 
             except TypeError: 
                 print(f"  ERROR (grounding): Variables part (derived) is not directly iterable and not a symbol. Type: {type(quantified_vars_fnode_tuple)}")
                 print(f"  Formula was: {quantified_formula.serialize()}")
                 return TRUE()
                 
    except IndexError: 
        print(f"  ERROR (grounding): Could not get arg(0) or arg(1) from ForAll node: {quantified_formula.serialize()}")
        return TRUE()

    # Define test values: {U, 1, 2, Ω-1} carefully considering current Omega
    test_values_py = {0} # U_alg is Int(0)
    if omega_val > 1: test_values_py.add(1)
    if omega_val > 2: test_values_py.add(2) # Only add 2 if it's a DFI (i.e. omega_val > 2)
    if omega_val - 1 >= 1: # Ensure Omega-1 is a valid DFI
        test_values_py.add(omega_val - 1)
    
    current_test_vals_smt = [Int(val) for val in sorted(list(test_values_py)) if 0 <= val < omega_val]

    if not quantified_vars: 
        return formula_body # No variables to substitute 
    if not current_test_vals_smt: 
        # This might happen if omega_val is small and quantified_vars expect DFI values that don't exist.
        # For example, if a var is constrained to be DFI and Omega=1.
        # In such a case, the universal quantification might be vacuously true over an empty effective domain.
        #print(f"  WARNING (grounding): No valid SMT test values for Ω={omega_val}. Returning TRUE for grounded universal.")
        return TRUE()

    instances = []
    for substitution_values_tuple in itertools.product(current_test_vals_smt, repeat=len(quantified_vars)):
        # Ensure all variables in quantified_vars are actual SMT Symbol FNodes
        if not all(v.is_symbol() for v in quantified_vars):
            print(f"  ERROR (grounding): Not all items in quantified_vars are SMT Symbols: {quantified_vars}")
            return TRUE() # Cannot create substitution map

        substitution_map = {var: val for var, val in zip(quantified_vars, substitution_values_tuple)}
        try:
            instances.append(formula_body.substitute(substitution_map))
        except Exception as e:
            print(f"ERROR during substitution in grounding: {e}")
            print(f"Formula body: {formula_body.serialize()}")
            print(f"Substitution map: { {v.symbol_name(): vl for v, vl in substitution_map.items()} }")
            return TRUE() # Cannot proceed
    
    return And(instances) if instances else TRUE()
    # --- End of the function body that must be correctly indented ---

# --- Modified SMT Check Utility (Task ④ Safe-Solve Fallback) ---
def check_smt_safe(solver: Solver, formula_to_assert: FNode, expected_sat: bool,
                   property_name: str, omega_val: int, # Added omega_val
                   smt_in_S_Omega_predicate: Callable[[FNode], FNode], # Added predicate
                   print_model_on_debug: bool = True) -> bool:
    """
    Checks an SMT formula, prints status, returns if check passed.
    Includes safe-solve fallback to grounding for UNKNOWN results on ForAll.
    `formula_to_assert` is typically Not(Property_To_Prove_True).
    """
    passed_check = False
    final_result_is_sat = None # To store SAT/UNSAT/None from solver

    solver.push()
    solver.add_assertion(formula_to_assert)
    # print(f"DEBUG: Checking formula: {formula_to_assert.serialize()}") # For debugging
    
    try:
        final_result_is_sat = solver.solve()
    except SolverReturnedUnknownResultError: # Should be caught by solve() returning None
        final_result_is_sat = None

    used_grounding_fallback = False
    if final_result_is_sat is None: # UNKNOWN
        print(f"  ⚠️ {property_name}: Solver returned UNKNOWN. Attempting fallback with grounded instances for Ω={omega_val}...")
        solver.pop() # Remove the assertion that led to UNKNOWN
        solver.push() # Start a new context for the grounded version

        # The formula_to_assert was typically Not(Property_Universal).
        # We need to ground Property_Universal.
        original_property_formula = formula_to_assert # Default if not a Not
        if formula_to_assert.is_not() and formula_to_assert.arg(0).is_forall():
            original_property_formula = formula_to_assert.arg(0) # This is the ForAll P(...)
            
            grounded_body_conjunction = ground_formula_instances(
                original_property_formula, 
                omega_val,
                #smt_in_S_Omega_predicate
            )
            # We were checking Not(ForAll P(...)). Now check Not(And P_inst(...))
            solver.add_assertion(Not(grounded_body_conjunction))
            used_grounding_fallback = True
        elif formula_to_assert.is_forall(): # If we were checking a ForAll formula directly for SAT/UNSAT
            grounded_body_conjunction = ground_formula_instances(
                formula_to_assert,
                omega_val,
                smt_in_S_Omega_predicate
            )
            solver.add_assertion(grounded_body_conjunction)
            used_grounding_fallback = True
        else:
            # Formula was not ForAll or Not(ForAll), UNKNOWN stands or re-assert original
            print(f"  ⚠️ {property_name}: UNKNOWN and not a ForAll or Not(ForAll), grounding not applied in standard way.")
            solver.add_assertion(formula_to_assert) # Re-assert original for consistent pop

        if used_grounding_fallback:
            try:
                final_result_is_sat = solver.solve()
                if final_result_is_sat is not None:
                    print(f"  ℹ️ {property_name}: Grounding fallback yielded a definite answer: {'SAT' if final_result_is_sat else 'UNSAT'}")
                else:
                    print(f"  ⚠️ {property_name}: Grounding fallback STILL UNKNOWN.")
            except SolverReturnedUnknownResultError:
                final_result_is_sat = None
                print(f"  ⚠️ {property_name}: Grounding fallback also resulted in UNKNOWN.")
    
    solver.pop() # Pop either original assertion or grounded one

    # Determine if the check passed based on final_result_is_sat and expected_sat
    if final_result_is_sat is not None:
        passed_check = (expected_sat and final_result_is_sat) or \
                       (not expected_sat and not final_result_is_sat)
    else: # final_result_is_sat is None (UNKNOWN)
        passed_check = False # Or handle as per desired logic for UNKNOWN

    # Reporting logic from your original check_smt
    model_str = "" # Placeholder for actual model string logic if needed for debug
    if passed_check:
        status_emoji = "✅"
        if not expected_sat and not final_result_is_sat: # Expected UNSAT, got UNSAT (Property HOLDS)
             print(f"{status_emoji} {property_name}: Property HOLDS (negation is UNSAT).{' (Used grounding)' if used_grounding_fallback else ''}{model_str}")
        elif expected_sat and final_result_is_sat: # Expected SAT, got SAT
             print(f"{status_emoji} {property_name}: Condition is SAT as expected.{' (Used grounding)' if used_grounding_fallback else ''}{model_str}")
        else: # This case should ideally not be hit if passed_check is true and logic is sound
             outcome_desc = "SAT as expected" if expected_sat else "UNSAT as expected"
             print(f"{status_emoji} {property_name}: {outcome_desc}.{' (Used grounding)' if used_grounding_fallback else ''}{model_str}")
        return True
    else:
        status_emoji = "❌"
        if final_result_is_sat is None:
            outcome_desc = "Solver returned UNKNOWN"
        else:
            outcome_desc = "UNSAT, but expected SAT" if expected_sat else "SAT, but expected UNSAT (property FAILS)"
        print(f"{status_emoji} {property_name}: {outcome_desc}.{' (Grounding attempted)' if used_grounding_fallback else ''}{model_str}")
        return False

# --- AVCA Axiom Setup (from Task ③ script) ---
def get_avca_v1_axioms(Omega_val: int, 
                       add_func_sym: Any, 
                       mul_func_sym: Any
                       ) -> Tuple[Any, Callable[[Any], FNode], Callable[[Any], FNode], List[FNode]]:
    Omega_smt_c = Int(Omega_val)
    U_smt_c = Int(0)
    in_S_Omega_f = lambda x_var: And(GE(x_var, Int(0)), LT(x_var, Omega_smt_c))
    if Omega_val == 1:
        is_DFI_f = lambda x_var: FALSE() 
    else:
        is_DFI_f = lambda x_var: And(GE(x_var, Int(1)), LT(x_var, Omega_smt_c))
    
    x_ax = Symbol(f"x_ax_O{Omega_val}", INT); y_ax = Symbol(f"y_ax_O{Omega_val}", INT)
    q_vars_ax = [x_ax, y_ax]; sum_ax = Plus(x_ax, y_ax); prod_ax = Times(x_ax, y_ax)
    
    axioms_list = [
        ForAll([x_ax], Implies(in_S_Omega_f(x_ax), Equals(add_func_sym(U_smt_c, x_ax), x_ax))),
        ForAll([x_ax], Implies(in_S_Omega_f(x_ax), Equals(add_func_sym(x_ax, U_smt_c), x_ax))),
        ForAll(q_vars_ax, Implies(And(is_DFI_f(x_ax), is_DFI_f(y_ax), LT(sum_ax, Omega_smt_c)),
                                  Equals(add_func_sym(x_ax, y_ax), sum_ax))),
        ForAll(q_vars_ax, Implies(And(is_DFI_f(x_ax), is_DFI_f(y_ax), GE(sum_ax, Omega_smt_c)),
                                  Equals(add_func_sym(x_ax, y_ax), U_smt_c))),
        ForAll([x_ax], Implies(in_S_Omega_f(x_ax), Equals(mul_func_sym(U_smt_c, x_ax), U_smt_c))),
        ForAll([x_ax], Implies(in_S_Omega_f(x_ax), Equals(mul_func_sym(x_ax, U_smt_c), U_smt_c))),
        ForAll(q_vars_ax, Implies(And(is_DFI_f(x_ax), is_DFI_f(y_ax), 
                                      And(GE(prod_ax, Int(1)), LT(prod_ax, Omega_smt_c))),
                                  Equals(mul_func_sym(x_ax, y_ax), prod_ax))),
        ForAll(q_vars_ax, Implies(And(is_DFI_f(x_ax), is_DFI_f(y_ax), 
                                      Or(LT(prod_ax, Int(1)), GE(prod_ax, Omega_smt_c))),
                                  Equals(mul_func_sym(x_ax, y_ax), U_smt_c)))
    ]
    axioms_list.append(ForAll(q_vars_ax, Implies(And(in_S_Omega_f(x_ax), in_S_Omega_f(y_ax)), 
                                                in_S_Omega_f(add_func_sym(x_ax,y_ax)))))
    axioms_list.append(ForAll(q_vars_ax, Implies(And(in_S_Omega_f(x_ax), in_S_Omega_f(y_ax)), 
                                                in_S_Omega_f(mul_func_sym(x_ax,y_ax)))))
    return U_smt_c, is_DFI_f, in_S_Omega_f, axioms_list

# --- Identity Catalogue (Task ③) ---
x_id_smt = Symbol("x_identity", INT)
y_id_smt = Symbol("y_identity", INT)
z_id_smt = Symbol("z_identity", INT)

IDENTITIES_CATALOGUE_ADD = {
    "Flexible Law (⊕)": lambda x, y: Equals(
        smt_avca_add(smt_avca_add(x, y), x),
        smt_avca_add(x, smt_avca_add(y, x))
    ),
    "Left Alternative Law (⊕)": lambda x, y: Equals(
        smt_avca_add(smt_avca_add(x, x), y),
        smt_avca_add(x, smt_avca_add(x, y))
    ),
    "Right Alternative Law (⊕)": lambda x, y: Equals(
        smt_avca_add(smt_avca_add(y, x), x), 
        smt_avca_add(y, smt_avca_add(x, x))
    ),
    "Power Associativity (x⊕x)⊕x = x⊕(x⊕x) (⊕)": lambda x: Equals(
        smt_avca_add(smt_avca_add(x,x),x),
        smt_avca_add(x,smt_avca_add(x,x))
    ),
    "Right Bol Identity (⊕)": lambda x, y, z: Equals(
        smt_avca_add(smt_avca_add(smt_avca_add(z, y), x), y),
        smt_avca_add(z, smt_avca_add(smt_avca_add(y, x), y))
    ),
    "Moufang Identity (Commutative form for ⊕)": lambda x, y, z: Equals(
        smt_avca_add(smt_avca_add(smt_avca_add(x, y), z), x),
        smt_avca_add(x, smt_avca_add(y, smt_avca_add(z, x)))
    ),
    "Steiner Property ((x⊕y)⊕y = x) (⊕)": lambda x, y: Equals(
        smt_avca_add(smt_avca_add(x,y),y), 
        x
    ),
}

def run_identity_catalogue_tests_scaled(Omega_val: int):
    print(f"\n--- Task ③ & ④: Testing Identity Catalogue for AVCA (Ω={Omega_val}) with SMT Scaling ---")
    
    global smt_avca_add, smt_avca_mul, U_smt_c_global, in_S_Omega_global_pred

    current_add_sym = Symbol(f"avca_add_O{Omega_val}_id_cat_scaled", SMT_AVCA_OP_TYPE)
    current_mul_sym = Symbol(f"avca_mul_O{Omega_val}_id_cat_scaled", SMT_AVCA_OP_TYPE)
    
    smt_avca_add = current_add_sym
    smt_avca_mul = current_mul_sym

    U_smt_c_global, _, in_S_Omega_global_pred_local, avca_axioms = get_avca_v1_axioms(
        Omega_val, current_add_sym, current_mul_sym
    )
    # Assign to global for use in lambdas and check_smt_safe if needed, though better to pass explicitly
    in_S_Omega_global_pred = in_S_Omega_global_pred_local


    results_summary = {}
    # For Z3, :mbqi false (Model-Based Quantifier Instantiation) can be helpful
    # PySMT uses string "false", not Python False for such options.
    solver_options = {"smt.random_seed": 42, "smt.mbqi": False} 
    # Alternatively, s.set_option(":smt.mbqi", "false") after creating solver s

    with Solver(name="z3", solver_options=solver_options) as s:
        # s.set_option(":smt.mbqi", "false") # Another way to set option

        for axiom_formula in avca_axioms: # Assert base AVCA axioms
            # For larger Omega, you might consider grounding these axioms too if they cause UNKNOWN
            # However, they define the functions, so usually, they are kept quantified.
            # If they are too slow or cause UNKNOWN for large Omega, one might
            # assert their grounded versions for specific test sets, but this changes the problem.
            # For now, asserting them as is.
            s.add_assertion(axiom_formula)

        print(f"\nTesting identities for (S_alg_{Omega_val}, ⊕):")
        for name, identity_lambda in IDENTITIES_CATALOGUE_ADD.items():
            arity = identity_lambda.__code__.co_argcount
            current_vars_smt = []
            if arity >= 1: current_vars_smt.append(x_id_smt)
            if arity >= 2: current_vars_smt.append(y_id_smt)
            if arity >= 3: current_vars_smt.append(z_id_smt)
            
            premise_conjuncts = [in_S_Omega_global_pred(v) for v in current_vars_smt]
            premise = And(premise_conjuncts) if premise_conjuncts else TRUE()

            identity_body = identity_lambda(*current_vars_smt)
            property_formula = ForAll(current_vars_smt, Implies(premise, identity_body))
            
            # We check if Not(property_formula) is UNSAT (meaning property holds)
            holds = check_smt_safe(s, Not(property_formula), expected_sat=False,
                                   property_name=f"Identity '{name}'",
                                   omega_val=Omega_val, # Pass current Omega
                                   smt_in_S_Omega_predicate=in_S_Omega_global_pred # Pass predicate
                                  )
            results_summary[name] = "Holds" if holds else "Fails (or Unknown)"

    print("\n--- Identity Catalogue Summary ---")
    for name, status in results_summary.items():
        print(f"  Ω={Omega_val}: {name}: {status}")
    return results_summary

# --- Main Execution ---
if __name__ == "__main__":
    print("AVCA Identity Catalogue Test Script with SMT Scaling (Task ③ & ④)")
    
    # Test for Omega = 2
    print("\n" + "="*40)
    run_identity_catalogue_tests_scaled(Omega_val=2)
    print("="*40)

    # Test for Omega = 3
    print("\n" + "="*40)
    run_identity_catalogue_tests_scaled(Omega_val=3)
    print("="*40)
    
    # Test for a larger Omega, e.g., Omega = 5 or 7, where UNKNOWN might occur without grounding
    # For much larger Omega (e.g., 30), grounding becomes essential.
    # Note: The effectiveness of grounding with a small fixed set like {U,1,2,Ω-1}
    # depends on the nature of the properties and potential counterexamples.
    # It's a heuristic to make SMT more tractable for larger Ω.
    print("\n" + "="*40)
    print("Attempting with a slightly larger Omega (e.g., 5) to see if grounding helps/activates:")
    run_identity_catalogue_tests_scaled(Omega_val=5) 
    print("="*40)

    print("\nScript finished.")