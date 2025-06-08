from pysmt.shortcuts import (
    Symbol, Int, And, Or, Not, Equals, Implies,
    ForAll, Exists, Solver, is_sat, is_unsat,
    Plus, Times, LE, LT, GE, Function, TRUE, FALSE,
    BOOL 
)
from pysmt.typing import INT, FunctionType, BOOL as SMT_BOOL_TYPE
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.fnode import FNode 
import itertools
from typing import List, Dict, Tuple, Callable, Any, Optional
# import pysmt.op # Not needed with this version of ground_forall

# Type alias for SMT function for AVCA operations
SMT_AVCA_OP_TYPE = FunctionType(INT, [INT, INT])

# Global SMT function symbols (will be set in run_identity_catalogue_tests_scaled)
smt_avca_add: Any = None
smt_avca_mul: Any = None 
U_smt_c_global: Any = None
in_S_Omega_global_pred: Callable[[FNode], FNode] = lambda x: TRUE() 

# --- Grounding Function (With Math LLM's Patch 1 for error reporting) ---
def ground_forall(quantified_formula: FNode, omega_val: int) -> FNode: 
    """
    Ground a ∀-formula by instantiating its body over S_Ω = {0,1,…,Ω-1}.
    - Uses .quantifier_vars() to get a list of Symbol nodes.
    - Pulls the single body out of .args()[0].
    - If that body is an implication, drops the guard and works on the consequent.
    (Implements Math LLM's "Final Patch" structure with improved error re-raising)
    """
    if not quantified_formula.is_forall():
        raise ValueError(f"Expected a ForAll node, got {quantified_formula.node_type()} for formula: {quantified_formula.serialize()}")
    
    vars_list: List[FNode] = []
    body_to_substitute: Optional[FNode] = None

    try:
        # 1) Get the bound variables (as per Math LLM: formula.quantifier_vars() returns iterable of symbols)
        vars_iterable = quantified_formula.quantifier_vars()
        vars_list = list(vars_iterable) 
        
        # 2) Get the single body child (as per Math LLM: formula.args()[0] is the body)
        node_args = quantified_formula.args()
        if len(node_args) == 1:
            body_to_substitute = node_args[0]
        else:
            raise ValueError(f"ForAll node {quantified_formula.serialize()} had {len(node_args)} args via .args(), expected 1 (the body).")

        # Sanity check (optional, but good)
        if not all(v.is_symbol() for v in vars_list):
             raise ValueError(f"Extracted variables via quantifier_vars() are not all symbols: {vars_list}")
        if body_to_substitute is None or not isinstance(body_to_substitute, FNode):
             raise ValueError(f"Body extracted via .args()[0] is not a valid FNode or is None.")

    except AttributeError as e_attr:
        raise ValueError(f"AttributeError during ForAll decomposition (likely .quantifier_vars() or .args()). Formula: {quantified_formula.serialize()}. Original Error: {e_attr!r}")
    except TypeError as e_type:
        raise ValueError(f"TypeError during ForAll decomposition (likely processing .quantifier_vars()). Formula: {quantified_formula.serialize()}. Original Error: {e_type!r}")
    except IndexError as e_idx:
        raise ValueError(f"IndexError during ForAll decomposition (accessing .args()[0]). Formula: {quantified_formula.serialize()}. Original Error: {e_idx!r}")
    except Exception as e_generic: # Catch any other unexpected error during decomposition
        raise ValueError(f"Unexpected error decomposing ForAll {quantified_formula.serialize()}: {e_generic!r}")

    # 3) If the body is an implication (guard → eq), strip off the guard.
    if body_to_substitute.is_implies():
        impl_args = body_to_substitute.args()
        if len(impl_args) == 2:
            body_to_substitute = impl_args[1] # Take the consequent
        else: # Should not happen for a valid Implies node
            raise ValueError(f"Body of ForAll was Implies, but did not have 2 args: {body_to_substitute.serialize()}")
            
    # 4) No vars ⇒ just return the (possibly-unwrapped) body
    if not vars_list:
        return body_to_substitute

    # 5) Instantiate over S_Ω^n
    s_alg_omega_py_values = range(omega_val)
    value_tuples = itertools.product(s_alg_omega_py_values, repeat=len(vars_list))
    
    conjuncts = []
    for current_value_tuple in value_tuples:
        try:
            substitution = {var_fnode: Int(py_val) for var_fnode, py_val in zip(vars_list, current_value_tuple)}
            conjuncts.append(body_to_substitute.substitute(substitution))
        except Exception as e_subst: # Patch 1: Re-raise substitution error with more context
            raise ValueError(f"ground_forall substitution failed for tuple {current_value_tuple} on body {body_to_substitute.serialize()}: {e_subst!r}")
    
    return And(conjuncts) if conjuncts else TRUE()


# --- Modified SMT Check Utility (With Math LLM's Patch 2 for error splitting) ---
def check_smt_safe_fixed(solver: Solver, formula_to_assert: FNode, expected_sat: bool,
                         property_name: str, omega_val: int,
                         print_model_on_debug: bool = True) -> bool:
    final_result_is_sat: Optional[bool] = None
    used_grounding_fallback = False
    passed_check = False
    grounding_exception_details = ""

    solver.push()
    solver.add_assertion(formula_to_assert)
    
    try:
        final_result_is_sat = solver.solve()
    except SolverReturnedUnknownResultError: # Should be caught by solve() returning None in PySMT
        final_result_is_sat = None
    except Exception as e_initial_solve: # Catch other potential errors from initial solve
        print(f"  ❌ {property_name}: Initial solver.solve() FAILED with: {e_initial_solve!r}")
        final_result_is_sat = None # Treat as UNKNOWN / failure to solve

    if final_result_is_sat is None: 
        print(f"  ⚠️ {property_name}: Solver returned UNKNOWN. Attempting fallback with grounded instances for Ω={omega_val}...")
        solver.pop() 
        solver.push() 

        original_property_formula_to_ground = None
        if formula_to_assert.is_not() and formula_to_assert.arg(0).is_forall():
            original_property_formula_to_ground = formula_to_assert.arg(0) 
        elif formula_to_assert.is_forall():
            original_property_formula_to_ground = formula_to_assert
        
        if original_property_formula_to_ground:
            grounded_conjunction = None
            try: # Patch 2: Separate try for ground_forall
                grounded_conjunction = ground_forall(original_property_formula_to_ground, omega_val)
                used_grounding_fallback = True # Mark attempt even if solve below fails

                assertion_for_grounded = None
                if formula_to_assert.is_not():
                    assertion_for_grounded = Not(grounded_conjunction)
                else:
                    assertion_for_grounded = grounded_conjunction
                
                solver.add_assertion(assertion_for_grounded)
                
                try: # Patch 2: Separate try for solver.solve() on grounded formula
                    current_solve_result = solver.solve()
                    if current_solve_result is not None:
                        final_result_is_sat = current_solve_result
                        print(f"  ℹ️ {property_name}: Grounding fallback yielded: {'SAT' if final_result_is_sat else 'UNSAT'}")
                    else:
                        final_result_is_sat = None 
                        print(f"  ⚠️ {property_name}: Grounding fallback STILL UNKNOWN.")
                except SolverReturnedUnknownResultError: # Should be caught by solve() returning None
                    print(f"  ❌ {property_name}: solver.solve() on grounded formula returned UNKNOWN (explicit exception).")
                    final_result_is_sat = None
                except Exception as e_solve_grounded:
                    print(f"  ❌ {property_name}: solver.solve() on grounded formula FAILED with: {e_solve_grounded!r}")
                    final_result_is_sat = None
            
            except Exception as e_ground: # Catch exceptions from ground_forall
                grounding_exception_details = f"Grounding function error: {e_ground!r}"
                print(f"  ❌ {property_name}: ground_forall() FAILED with: {e_ground!r}")
                final_result_is_sat = None 
                # used_grounding_fallback is already true if we entered this block
        else:
            print(f"  ⚠️ {property_name}: UNKNOWN, but formula was not ForAll or Not(ForAll) for grounding.")
            # final_result_is_sat remains None
            
    solver.pop() 

    if final_result_is_sat is not None:
        passed_check = (expected_sat and final_result_is_sat) or \
                       (not expected_sat and not final_result_is_sat)

    model_str = "" 
    if passed_check:
        status_emoji = "✅"
        if not expected_sat: 
             print(f"{status_emoji} {property_name}: Property HOLDS (negation is UNSAT).{' (Resolved via grounding)' if used_grounding_fallback and final_result_is_sat is not None else ''}{model_str}")
        else: 
             print(f"{status_emoji} {property_name}: Condition is SAT as expected.{' (Resolved via grounding)' if used_grounding_fallback and final_result_is_sat is not None else ''}{model_str}")
        return True
    else:
        status_emoji = "❌"
        if final_result_is_sat is None: 
            outcome_desc = "Solver returned UNKNOWN"
            if used_grounding_fallback: 
                if grounding_exception_details:
                    outcome_desc += f" (grounding attempt FAILED: {grounding_exception_details})"
                else:
                    outcome_desc += " (grounding attempt made, but solver still UNKNOWN or other error)"
        else: 
            outcome_desc = "UNSAT, but expected SAT" if expected_sat else "SAT, but expected UNSAT (property FAILS)"
        print(f"{status_emoji} {property_name}: {outcome_desc}.{' (After grounding attempt)' if used_grounding_fallback else ''}{model_str}")
        return False

# --- AVCA Axiom Setup (unchanged) ---
def get_avca_v1_axioms(Omega_val: int, add_func_sym: Any, mul_func_sym: Any) -> Tuple[Any, Callable[[Any], FNode], Callable[[Any], FNode], List[FNode]]:
    Omega_smt_c = Int(Omega_val); U_smt_c = Int(0)
    in_S_Omega_f = lambda x_var: And(GE(x_var, Int(0)), LT(x_var, Omega_smt_c))
    is_DFI_f = (lambda x_var: FALSE()) if Omega_val == 1 else (lambda x_var: And(GE(x_var, Int(1)), LT(x_var, Omega_smt_c)))
    x_ax, y_ax = Symbol(f"x_ax_O{Omega_val}", INT), Symbol(f"y_ax_O{Omega_val}", INT)
    q_vars_ax, sum_ax, prod_ax = [x_ax, y_ax], Plus(x_ax, y_ax), Times(x_ax, y_ax)
    axioms_list = [
        ForAll([x_ax], Implies(in_S_Omega_f(x_ax), Equals(add_func_sym(U_smt_c, x_ax), x_ax))),
        ForAll([x_ax], Implies(in_S_Omega_f(x_ax), Equals(add_func_sym(x_ax, U_smt_c), x_ax))),
        ForAll(q_vars_ax, Implies(And(is_DFI_f(x_ax), is_DFI_f(y_ax), LT(sum_ax, Omega_smt_c)), Equals(add_func_sym(x_ax, y_ax), sum_ax))),
        ForAll(q_vars_ax, Implies(And(is_DFI_f(x_ax), is_DFI_f(y_ax), GE(sum_ax, Omega_smt_c)), Equals(add_func_sym(x_ax, y_ax), U_smt_c))),
        ForAll([x_ax], Implies(in_S_Omega_f(x_ax), Equals(mul_func_sym(U_smt_c, x_ax), U_smt_c))),
        ForAll([x_ax], Implies(in_S_Omega_f(x_ax), Equals(mul_func_sym(x_ax, U_smt_c), U_smt_c))),
        ForAll(q_vars_ax, Implies(And(is_DFI_f(x_ax), is_DFI_f(y_ax), And(GE(prod_ax, Int(1)), LT(prod_ax, Omega_smt_c))), Equals(mul_func_sym(x_ax, y_ax), prod_ax))),
        ForAll(q_vars_ax, Implies(And(is_DFI_f(x_ax), is_DFI_f(y_ax), Or(LT(prod_ax, Int(1)), GE(prod_ax, Omega_smt_c))), Equals(mul_func_sym(x_ax, y_ax), U_smt_c)))
    ]
    axioms_list.append(ForAll(q_vars_ax, Implies(And(in_S_Omega_f(x_ax), in_S_Omega_f(y_ax)), in_S_Omega_f(add_func_sym(x_ax,y_ax)))))
    axioms_list.append(ForAll(q_vars_ax, Implies(And(in_S_Omega_f(x_ax), in_S_Omega_f(y_ax)), in_S_Omega_f(mul_func_sym(x_ax,y_ax)))))
    return U_smt_c, is_DFI_f, in_S_Omega_f, axioms_list

# --- Identity Catalogue (unchanged) ---
x_id_smt = Symbol("x_identity", INT); y_id_smt = Symbol("y_identity", INT); z_id_smt = Symbol("z_identity", INT)
IDENTITIES_CATALOGUE_ADD = {
    "Flexible Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x, y), x), smt_avca_add(x, smt_avca_add(y, x))),
    "Left Alternative Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x, x), y), smt_avca_add(x, smt_avca_add(x, y))),
    "Right Alternative Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(y, x), x), smt_avca_add(y, smt_avca_add(x, x))),
    "Power Associativity (x⊕x)⊕x = x⊕(x⊕x) (⊕)": lambda x: Equals(smt_avca_add(smt_avca_add(x,x),x), smt_avca_add(x,smt_avca_add(x,x))),
    "Right Bol Identity (⊕)": lambda x, y, z: Equals(smt_avca_add(smt_avca_add(smt_avca_add(z, y), x), y), smt_avca_add(z, smt_avca_add(smt_avca_add(y, x), y))),
    "Moufang Identity (Commutative form for ⊕)": lambda x, y, z: Equals(smt_avca_add(smt_avca_add(smt_avca_add(x, y), z), x), smt_avca_add(x, smt_avca_add(y, smt_avca_add(z, x)))),
    "Steiner Property ((x⊕y)⊕y = x) (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x,y),y), x),
}

# --- Main Test Runner (run_identity_catalogue_tests_scaled - unchanged from last version) ---
def run_identity_catalogue_tests_scaled(Omega_val: int):
    print(f"\n--- Task ③ & ④: Testing Identity Catalogue for AVCA (Ω={Omega_val}) with SMT Scaling (LLM Final Patch v2) ---")
    global smt_avca_add, smt_avca_mul, U_smt_c_global, in_S_Omega_global_pred
    current_add_sym = Symbol(f"avca_add_O{Omega_val}_id_cat_sclFP2", SMT_AVCA_OP_TYPE) 
    current_mul_sym = Symbol(f"avca_mul_O{Omega_val}_id_cat_sclFP2", SMT_AVCA_OP_TYPE) 
    smt_avca_add, smt_avca_mul = current_add_sym, current_mul_sym
    U_smt_c_global, _, in_S_Omega_global_pred_local, avca_axioms = get_avca_v1_axioms(Omega_val, current_add_sym, current_mul_sym)
    in_S_Omega_global_pred = in_S_Omega_global_pred_local
    results_summary = {}
    solver_options = {"smt.random_seed": 42, "smt.mbqi": False} 
    with Solver(name="z3", solver_options=solver_options, logic="QF_UFLIA") as s: 
        for axiom_formula in avca_axioms: s.add_assertion(axiom_formula)
        print(f"\nTesting identities for (S_alg_{Omega_val}, ⊕):")
        for name, identity_lambda in IDENTITIES_CATALOGUE_ADD.items():
            arity = identity_lambda.__code__.co_argcount
            current_vars_smt = [var for var_idx, var in enumerate([x_id_smt, y_id_smt, z_id_smt]) if var_idx < arity]
            premise = And([in_S_Omega_global_pred(v) for v in current_vars_smt]) if current_vars_smt else TRUE()
            identity_body = identity_lambda(*current_vars_smt)
            property_formula = ForAll(current_vars_smt, Implies(premise, identity_body)) if current_vars_smt else Implies(premise, identity_body)
            
            holds = check_smt_safe_fixed(s, Not(property_formula), expected_sat=False,
                                         property_name=f"Identity '{name}'",
                                         omega_val=Omega_val) 
            results_summary[name] = "Holds" if holds else "Fails (or Unknown/GroundingFailed)"
    print("\n--- Identity Catalogue Summary ---")
    for name, status in results_summary.items(): print(f"  Ω={Omega_val}: {name}: {status}")
    return results_summary

# --- Main Execution (Same as before) ---
if __name__ == "__main__":
    print("AVCA Identity Catalogue Test Script with SMT Scaling (Task ③ & ④) - LLM Final Patch for Grounding v2")
    
    print("\n" + "="*70)
    run_identity_catalogue_tests_scaled(Omega_val=2)
    print("="*70)

    print("\n" + "="*70)
    run_identity_catalogue_tests_scaled(Omega_val=3)
    print("="*70)
    
    print("\n" + "="*70)
    print("Attempting with a slightly larger Omega (e.g., 5) to see if grounding helps/activates:")
    run_identity_catalogue_tests_scaled(Omega_val=5) 
    print("="*70)

    print("\nScript finished.")
    print("\nExpected outcomes based on previous validated runs and Math LLM analysis:")
    # ... (expected outcomes printout as before) ...
    print("Ω=2: All listed identities for ⊕ should HOLD.")
    print("Ω=3 and Ω=5:")
    print("  Flexible Law (⊕): Holds")
    print("  Left Alternative Law (⊕): Fails")
    print("  Right Alternative Law (⊕): Fails")
    print("  Power Associativity (⊕): Holds")
    print("  Right Bol Identity (⊕): Fails")
    print("  Moufang Identity (⊕): Fails")
    print("  Steiner Property ((x⊕y)⊕y = x) (⊕): Fails (Holds only for Ω=2 in this set)")