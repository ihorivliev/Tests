from pysmt.shortcuts import (
    Symbol, Int, And, Or, Not, Equals, Implies,
    ForAll, Exists, Solver, is_sat, is_unsat,
    Plus, Times, LE, LT, GE, Function, TRUE, FALSE,
    BOOL 
)
import re

from pysmt.typing import INT, FunctionType, BOOL as SMT_BOOL_TYPE
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.fnode import FNode 
import itertools
from typing import List, Dict, Tuple, Callable, Any, Optional
# Type alias for SMT function for AVCA operations
SMT_AVCA_OP_TYPE = FunctionType(INT, [INT, INT])


# --- Python AVCA Kernel (from previous script) ---
_Omega_py: Optional[int] = None
_ZERO_UNIO_py_repr = "Unio('zero')" 
_AREO_UNIO_py_repr = "Unio('areo')"   
PyAVCVal = Any 

def set_py_avca_omega(omega_val: int):
    global _Omega_py
    if not isinstance(omega_val, int) or omega_val < 1:
        raise ValueError("Python AVCA Omega must be an integer >= 1.")
    _Omega_py = omega_val

def _check_py_val(x: PyAVCVal, omega: int, op_name: str = "py_op", arg_name: str = "input"):
    if x == _ZERO_UNIO_py_repr or x == _AREO_UNIO_py_repr: return
    if not isinstance(x, int):
        raise TypeError(f"Py AVCA val for {op_name}/{arg_name} must be int or Unio sentinel string: got {x} (type {type(x)})")
    if omega == 1 and isinstance(x, int):
        raise ValueError(f"DFI value {x} is invalid for {op_name}/{arg_name} when Python AVCA Omega is 1.")
    if omega > 1 and not (1 <= x < omega):
        raise ValueError(f"DFI value {x} is out of range [1, {omega-1}] for {op_name}/{arg_name} for Python AVCA Omega={omega}.")

def py_avca_add(a: PyAVCVal, b: PyAVCVal) -> PyAVCVal:
    if _Omega_py is None: raise ValueError("Python AVCA Omega not set.")
    _check_py_val(a, _Omega_py, "py_avca_add", "a"); _check_py_val(b, _Omega_py, "py_avca_add", "b")
    if a == _ZERO_UNIO_py_repr or a == _AREO_UNIO_py_repr: return b
    if b == _ZERO_UNIO_py_repr or b == _AREO_UNIO_py_repr: return a
    val_a: int = a; val_b: int = b
    dfi_sum = val_a + val_b
    return dfi_sum if dfi_sum < _Omega_py else _AREO_UNIO_py_repr

# --- Python Identity Definitions (for brute-force fallback) ---
# These functions take Python integer representations (0 for U_alg) and the py_avca_add operation

def py_identity_flexible(x: int, y: int, add_op: Callable[[PyAVCVal, PyAVCVal], PyAVCVal]) -> bool:
    # (x⊕y)⊕x = x⊕(y⊕x)
    lhs = add_op(add_op(x, y), x)
    rhs = add_op(x, add_op(y, x))
    # Algebraic comparison for Unio
    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)
    if lhs_is_unio and rhs_is_unio: return True
    return lhs == rhs

def py_identity_left_alternative(x: int, y: int, add_op: Callable[[PyAVCVal, PyAVCVal], PyAVCVal]) -> bool:
    # (x⊕x)⊕y = x⊕(x⊕y)
    lhs = add_op(add_op(x, x), y)
    rhs = add_op(x, add_op(x, y))
    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)
    if lhs_is_unio and rhs_is_unio: return True
    return lhs == rhs
    
def py_identity_right_alternative(x: int, y: int, add_op: Callable[[PyAVCVal, PyAVCVal], PyAVCVal]) -> bool:
    # (y⊕x)⊕x = y⊕(x⊕x)  (using y,x to match SMT lambda)
    lhs = add_op(add_op(y, x), x)
    rhs = add_op(y, add_op(x, x))
    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)
    if lhs_is_unio and rhs_is_unio: return True
    return lhs == rhs

def py_identity_power_associativity(x: int, add_op: Callable[[PyAVCVal, PyAVCVal], PyAVCVal]) -> bool:
    # (x⊕x)⊕x = x⊕(x⊕x)
    lhs = add_op(add_op(x,x),x)
    rhs = add_op(x,add_op(x,x))
    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)
    if lhs_is_unio and rhs_is_unio: return True
    return lhs == rhs

def py_identity_right_bol(x: int, y: int, z: int, add_op: Callable[[PyAVCVal, PyAVCVal], PyAVCVal]) -> bool:
    # ((z⊕y)⊕x)⊕y = z⊕((y⊕x)⊕y)
    lhs = add_op(add_op(add_op(z, y), x), y)
    rhs = add_op(z, add_op(add_op(y, x), y))
    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)
    if lhs_is_unio and rhs_is_unio: return True
    return lhs == rhs

def py_identity_moufang_commutative(x: int, y: int, z: int, add_op: Callable[[PyAVCVal, PyAVCVal], PyAVCVal]) -> bool:
    # ((x⊕y)⊕z)⊕x = x⊕(y⊕(z⊕x))
    lhs = add_op(add_op(add_op(x, y), z), x)
    rhs = add_op(x, add_op(y, add_op(z, x)))
    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)
    if lhs_is_unio and rhs_is_unio: return True
    return lhs == rhs

def py_identity_steiner(x: int, y: int, add_op: Callable[[PyAVCVal, PyAVCVal], PyAVCVal]) -> bool:
    # (x⊕y)⊕y = x
    lhs = add_op(add_op(x,y),y)
    rhs = x
    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr) # rhs can be U if x is U
    if lhs_is_unio and rhs_is_unio: return True
    return lhs == rhs

PYTHON_IDENTITY_CHECKERS = {
    "Flexible Law (⊕)": (py_identity_flexible, 2),
    "Left Alternative Law (⊕)": (py_identity_left_alternative, 2),
    "Right Alternative Law (⊕)": (py_identity_right_alternative, 2),
    "Power Associativity (x⊕x)⊕x = x⊕(x⊕x) (⊕)": (py_identity_power_associativity, 1),
    "Right Bol Identity (⊕)": (py_identity_right_bol, 3),
    "Moufang Identity (Commutative form for ⊕)": (py_identity_moufang_commutative, 3),
    "Steiner Property ((x⊕y)⊕y = x) (⊕)": (py_identity_steiner, 2),
}

def python_brute_force_identity_check(identity_key_name: str, omega_val: int) -> bool:
    """
    Checks a named identity using Python brute-force.
    Returns True if the identity holds, False if a counterexample is found.
    """
    if identity_key_name not in PYTHON_IDENTITY_CHECKERS:
        print(f"  WARNING (Python brute-force): No Python checker for identity '{identity_key_name}'.")
        return False # Cannot verify

    identity_checker_func, arity = PYTHON_IDENTITY_CHECKERS[identity_key_name]
    
    # S_alg_Omega elements for Python: 0 for U_alg, 1 to omega_val-1 for DFIs
    s_alg_py_elements = list(range(omega_val)) 
    # Map 0 to Unio sentinel for py_avca_add compatibility if needed, 
    # or ensure py_avca_add handles integer 0 as U_alg.
    # The current py_avca_add expects string sentinels for Unio.
    
    py_elements_for_product = []
    for i in s_alg_py_elements:
        if i == 0:
            py_elements_for_product.append(_ZERO_UNIO_py_repr) # Represent U_alg
        else:
            py_elements_for_product.append(i)

    # Call set_py_avca_omega for the Python AVCA operation
    set_py_avca_omega(omega_val)

    for value_tuple_py in itertools.product(py_elements_for_product, repeat=arity):
        if not identity_checker_func(*value_tuple_py, py_avca_add):
            # print(f"    Brute-force counterexample for '{identity_key_name}' at Ω={omega_val}: {value_tuple_py}")
            return False # Counterexample found
    return True # No counterexamples found

# --- Grounding Function (Math LLM's Final Patch from previous turn) ---
def ground_forall(quantified_formula: FNode, omega_val: int) -> FNode: 
    if not quantified_formula.is_forall():
        raise ValueError(f"Expected ForAll, got {quantified_formula.node_type()} for formula: {quantified_formula.serialize()}")
    vars_list: List[FNode] = []; body: Optional[FNode] = None
    try:
        vars_iterable = quantified_formula.quantifier_vars()
        vars_list = list(vars_iterable) 
        node_args = quantified_formula.args()
        if len(node_args) == 1: body = node_args[0]
        else: raise ValueError(f"ForAll had {len(node_args)} args, expected 1 (body)")
        if not all(v.is_symbol() for v in vars_list): raise ValueError(f"Vars not all symbols: {vars_list}")
        if body is None or not isinstance(body, FNode): raise ValueError(f"Body invalid: {body}")
    except AttributeError as e_attr: raise ValueError(f"AttrErr decomposing ForAll {quantified_formula.serialize()}: {e_attr!r}")
    except TypeError as e_type: raise ValueError(f"TypeErr decomposing ForAll {quantified_formula.serialize()}: {e_type!r}")
    except IndexError as e_idx: raise ValueError(f"IdxErr decomposing ForAll {quantified_formula.serialize()}: {e_idx!r}")
    except Exception as e_gen: raise ValueError(f"GenericErr decomposing ForAll {quantified_formula.serialize()}: {e_gen!r}")
    if body.is_implies():
        impl_args = body.args()
        if len(impl_args) == 2: body = impl_args[1] 
        else: raise ValueError(f"Implies body did not have 2 args: {body.serialize()}")
    if not vars_list: return body
    s_alg_omega_py_values = range(omega_val)
    value_tuples = itertools.product(s_alg_omega_py_values, repeat=len(vars_list))
    conjuncts = []
    for current_value_tuple in value_tuples:
        try:
            substitution = {var_fnode: Int(py_val) for var_fnode, py_val in zip(vars_list, current_value_tuple)}
            conjuncts.append(body.substitute(substitution))
        except Exception as e_subst: 
            raise ValueError(f"ground_forall substitution failed for tuple {current_value_tuple} on body {body.serialize()}: {e_subst!r}")
    return And(conjuncts) if conjuncts else TRUE()

# --- SMT Check Utility (Integrates Python Brute-Force Fallback) ---
def check_smt_safe_fixed(solver: Solver, formula_to_assert: FNode, expected_sat: bool,
                         property_name_full: str, # e.g. "Identity 'Flexible Law (⊕)'"
                         omega_val: int,
                         smt_identity_lambda_for_py_fallback: Optional[Callable] = None, # SMT lambda of the property
                         print_model_on_debug: bool = True) -> bool:
    global _Omega_py # <<--- ADD THIS LINE
    final_result_is_sat: Optional[bool] = None
    used_grounding_fallback = False
    used_python_brute_fallback = False
    passed_check = False
    grounding_exception_details = ""

    solver.push()
    solver.add_assertion(formula_to_assert)
    
    try:
        final_result_is_sat = solver.solve()
    except SolverReturnedUnknownResultError: final_result_is_sat = None
    except Exception as e_initial_solve:
        print(f"  ❌ {property_name_full}: Initial solver.solve() FAILED with: {e_initial_solve!r}")
        final_result_is_sat = None

    if final_result_is_sat is None: 
        print(f"  ⚠️ {property_name_full}: SMT solver returned UNKNOWN. Attempting SMT grounding fallback for Ω={omega_val}...")
        solver.pop(); solver.push() 
        original_property_formula_to_ground = None
        assertion_for_grounded = None

        if formula_to_assert.is_not() and formula_to_assert.arg(0).is_forall():
            original_property_formula_to_ground = formula_to_assert.arg(0) 
        elif formula_to_assert.is_forall():
            original_property_formula_to_ground = formula_to_assert
        
        if original_property_formula_to_ground:
            try:
                grounded_conjunction = ground_forall(original_property_formula_to_ground, omega_val)
                if formula_to_assert.is_not(): assertion_for_grounded = Not(grounded_conjunction)
                else: assertion_for_grounded = grounded_conjunction
                
                solver.add_assertion(assertion_for_grounded)
                used_grounding_fallback = True
                current_solve_result = solver.solve()

                if current_solve_result is not None:
                    final_result_is_sat = current_solve_result
                    print(f"  ℹ️ {property_name_full}: SMT grounding fallback yielded: {'SAT' if final_result_is_sat else 'UNSAT'}")
                else:
                    final_result_is_sat = None 
                    print(f"  ⚠️ {property_name_full}: SMT grounding fallback STILL UNKNOWN.")
            except Exception as e_ground: 
                grounding_exception_details = f"Grounding function error: {e_ground!r}"
                print(f"  ❌ {property_name_full}: ground_forall() FAILED with: {e_ground!r}")
                final_result_is_sat = None 
                used_grounding_fallback = True
        else: # UNKNOWN but not a ForAll for standard grounding
            print(f"  ⚠️ {property_name_full}: UNKNOWN, but formula not ForAll/Not(ForAll) for SMT grounding.")
        
        # --- Python Brute-Force Fallback ---
        if final_result_is_sat is None and used_grounding_fallback: # SMT grounding was attempted but still UNKNOWN or failed
            # Extract the simple name for dictionary lookup
            #identity_key_name_match = System.Text.RegularExpressions.Regex.Match(property_name_full, r"Identity '(.*?)'") # Using .NET Regex for placeholder
            # In Python, you'd use re.search or string manipulation:
            # import re
            # match = re.search(r"Identity '(.*?)'", property_name_full)
            # identity_key_name = match.group(1) if match else property_name_full # Simplified
            # For this script, let's assume property_name_full is directly usable or we map it
            # This part needs a robust way to get the key for PYTHON_IDENTITY_CHECKERS
            # Let's pass the key directly or use the full name if it matches.
            
            # Simplification: assume property_name_full is the key for PYTHON_IDENTITY_CHECKERS for now
            # For a real system, you might pass the identity_lambda or a clean key.
            # The `name` variable from the loop in `run_identity_catalogue_tests_scaled` is the clean key.
            # We need to pass that `name` to `check_smt_safe_fixed`.
            
            # For the purpose of this integration, let's assume 'property_name_full' can be
            # adjusted to be the key, or we modify the call to pass the original 'name'
            # Let's modify check_smt_safe_fixed to accept 'identity_key_for_py_fallback'
            # The original `property_name_full` from `f"Identity '{name}'"` means `name` is the key.
            
            clean_identity_name = property_name_full.replace("Identity '", "").replace("'", "") # Basic extraction
                                  
            if clean_identity_name in PYTHON_IDENTITY_CHECKERS:
                print(f"  🐍 {property_name_full}: SMT UNKNOWN after grounding. Falling back to Python brute-force (Ω={omega_val})...")
                used_python_brute_fallback = True
                brute_force_holds = python_brute_force_identity_check(clean_identity_name, omega_val)
                
                if brute_force_holds:
                    print(f"  ✅ {property_name_full}: Verified by Python brute-force (Property HOLDS).")
                    final_result_is_sat = False # Not(Property) is UNSAT if Property HOLDS
                else:
                    print(f"  ❌ {property_name_full}: Counterexample found by Python brute-force (Property FAILS).")
                    final_result_is_sat = True  # Not(Property) is SAT if Property FAILS
            else:
                print(f"  ⚠️ {property_name_full}: No Python brute-force checker for '{clean_identity_name}'. Result remains UNKNOWN.")
    solver.pop() 

    if final_result_is_sat is not None:
        passed_check = (expected_sat and final_result_is_sat) or \
                       (not expected_sat and not final_result_is_sat)

    report_suffix = ""
    if used_python_brute_fallback: report_suffix = " (Resolved via Python brute-force)"
    elif used_grounding_fallback and final_result_is_sat is not None: report_suffix = " (Resolved via SMT grounding)"
    elif used_grounding_fallback and grounding_exception_details: report_suffix = f" (SMT grounding FAILED: {grounding_exception_details})"
    elif used_grounding_fallback: report_suffix = " (SMT grounding attempted, result still UNKNOWN)"


    if passed_check:
        status_emoji = "✅"
        if not expected_sat: 
             print(f"{status_emoji} {property_name_full}: Property HOLDS (negation is UNSAT).{report_suffix}")
        else: 
             print(f"{status_emoji} {property_name_full}: Condition is SAT as expected.{report_suffix}")
        return True
    else:
        status_emoji = "❌"
        if final_result_is_sat is None: 
            outcome_desc = "Solver returned UNKNOWN"
        else: 
            outcome_desc = "UNSAT, but expected SAT" if expected_sat else "SAT, but expected UNSAT (property FAILS)"
        print(f"{status_emoji} {property_name_full}: {outcome_desc}.{report_suffix}")
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

# --- SMT Identity Catalogue (unchanged) ---
x_id_smt = Symbol("x_identity", INT); y_id_smt = Symbol("y_identity", INT); z_id_smt = Symbol("z_identity", INT)
IDENTITIES_CATALOGUE_SMT_ADD = { # Renamed to avoid clash if Python dict has same key
    "Flexible Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x, y), x), smt_avca_add(x, smt_avca_add(y, x))),
    "Left Alternative Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x, x), y), smt_avca_add(x, smt_avca_add(x, y))),
    "Right Alternative Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(y, x), x), smt_avca_add(y, smt_avca_add(x, x))),
    "Power Associativity (x⊕x)⊕x = x⊕(x⊕x) (⊕)": lambda x: Equals(smt_avca_add(smt_avca_add(x,x),x), smt_avca_add(x,smt_avca_add(x,x))),
    "Right Bol Identity (⊕)": lambda x, y, z: Equals(smt_avca_add(smt_avca_add(smt_avca_add(z, y), x), y), smt_avca_add(z, smt_avca_add(smt_avca_add(y, x), y))),
    "Moufang Identity (Commutative form for ⊕)": lambda x, y, z: Equals(smt_avca_add(smt_avca_add(smt_avca_add(x, y), z), x), smt_avca_add(x, smt_avca_add(y, smt_avca_add(z, x)))),
    "Steiner Property ((x⊕y)⊕y = x) (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x,y),y), x),
}

# --- Main Test Runner (Updated to pass identity key for Python fallback) ---
def run_identity_catalogue_tests_scaled(Omega_val: int):
    # ... (setup for smt_avca_add, etc. - same as before) ...
    print(f"\n--- Task ③ & ④: Testing Identity Catalogue for AVCA (Ω={Omega_val}) with SMT Scaling (LLM Final Patch v3 + Python Fallback) ---")
    global smt_avca_add, smt_avca_mul, U_smt_c_global, in_S_Omega_global_pred
    current_add_sym = Symbol(f"avca_add_O{Omega_val}_id_cat_sclFP3", SMT_AVCA_OP_TYPE) 
    current_mul_sym = Symbol(f"avca_mul_O{Omega_val}_id_cat_sclFP3", SMT_AVCA_OP_TYPE) 
    smt_avca_add, smt_avca_mul = current_add_sym, current_mul_sym
    U_smt_c_global, _, in_S_Omega_global_pred_local, avca_axioms = get_avca_v1_axioms(Omega_val, current_add_sym, current_mul_sym)
    in_S_Omega_global_pred = in_S_Omega_global_pred_local
    results_summary = {}
    solver_options = {"smt.random_seed": 42, "smt.mbqi": False} 
    with Solver(name="z3", solver_options=solver_options, logic="QF_UFLIA") as s: 
        for axiom_formula in avca_axioms: s.add_assertion(axiom_formula)
        print(f"\nTesting identities for (S_alg_{Omega_val}, ⊕):")
        for name, smt_identity_lambda in IDENTITIES_CATALOGUE_SMT_ADD.items(): # Use renamed SMT dict
            arity = smt_identity_lambda.__code__.co_argcount
            current_vars_smt = [var for var_idx, var in enumerate([x_id_smt, y_id_smt, z_id_smt]) if var_idx < arity]
            premise = And([in_S_Omega_global_pred(v) for v in current_vars_smt]) if current_vars_smt else TRUE()
            identity_body = smt_identity_lambda(*current_vars_smt)
            property_formula = ForAll(current_vars_smt, Implies(premise, identity_body)) if current_vars_smt else Implies(premise, identity_body)
            
            # Inside run_identity_catalogue_tests_scaled loop:
            holds = check_smt_safe_fixed(s, Not(property_formula), expected_sat=False,
                                        property_name_full=f"Identity '{name}'", # Full name for printing
                                        omega_val=Omega_val,
                                        identity_key_for_py_fallback=name # Pass the clean 'name' as the key
                                        )
            results_summary[name] = "Holds" if holds else "Fails (or Unknown/GroundingFailed)"
    print("\n--- Identity Catalogue Summary ---")
    for name, status in results_summary.items(): print(f"  Ω={Omega_val}: {name}: {status}")
    return results_summary
    
# --- SMT Check Utility (Simplified: SMT direct -> Python Brute-Force on UNKNOWN) ---
def check_smt_safe_fixed(solver: Solver, formula_to_assert: FNode, expected_sat: bool,
                         property_name_full: str, 
                         omega_val: int,
                         identity_key_for_py_fallback: Optional[str] = None, 
                         print_model_on_debug: bool = True) -> bool:
    global _Omega_py # Ensure access to global _Omega_py for set_py_avca_omega

    final_result_is_sat: Optional[bool] = None
    used_smt_direct = False
    used_python_brute_fallback = False
    passed_check = False
    
    solver.push()
    solver.add_assertion(formula_to_assert)
    
    try:
        # Initial SMT attempt
        final_result_is_sat = solver.solve()
        used_smt_direct = True
    except SolverReturnedUnknownResultError: 
        final_result_is_sat = None # Should be caught by solve() returning None
    except Exception as e_initial_solve:
        print(f"  ❌ {property_name_full}: Initial solver.solve() FAILED with: {e_initial_solve!r}")
        final_result_is_sat = None

    # If SMT solver returned UNKNOWN, go to Python brute-force fallback
    if final_result_is_sat is None: 
        # No SMT grounding attempt anymore, directly to Python if applicable
        if identity_key_for_py_fallback and identity_key_for_py_fallback in PYTHON_IDENTITY_CHECKERS:
            print(f"  🐍 {property_name_full}: SMT solver returned UNKNOWN. Falling back to Python brute-force (Ω={omega_val})...")
            used_python_brute_fallback = True
            
            current_py_omega_state = _Omega_py 
            set_py_avca_omega(omega_val)      
            
            brute_force_holds = python_brute_force_identity_check(identity_key_for_py_fallback, omega_val)
            
            if brute_force_holds:
                print(f"  ✅ {property_name_full}: Verified by Python brute-force (Property HOLDS).")
                final_result_is_sat = False # Not(Property) is UNSAT if Property HOLDS
            else:
                print(f"  ❌ {property_name_full}: Counterexample found by Python brute-force (Property FAILS).")
                final_result_is_sat = True  # Not(Property) is SAT if Property FAILS
            
            if current_py_omega_state is not None:
                set_py_avca_omega(current_py_omega_state)
            elif _Omega_py == omega_val : # If we set it and it wasn't set before
                 _Omega_py = None # Consider unsetting it, or manage state more carefully
        else:
            print(f"  ⚠️ {property_name_full}: SMT UNKNOWN, and no Python brute-force checker for key '{identity_key_for_py_fallback}'. Result remains UNKNOWN.")
            # final_result_is_sat remains None
            
    solver.pop() 

    # Determine if the check passed based on final_result_is_sat and expected_sat
    if final_result_is_sat is not None:
        passed_check = (expected_sat and final_result_is_sat) or \
                       (not expected_sat and not final_result_is_sat)

    # Reporting logic
    report_suffix = ""
    if used_python_brute_fallback and final_result_is_sat is not None: 
        report_suffix = " (Resolved via Python brute-force)"
    elif used_python_brute_fallback and final_result_is_sat is None: # Should not happen if python brute gives definite answer
        report_suffix = " (Python brute-force attempted but outcome still None? Check logic)"
    elif used_smt_direct and final_result_is_sat is None : # SMT was UNKNOWN, Python fallback not applicable/failed
        report_suffix = " (SMT UNKNOWN, Python fallback N/A or also failed)"


    if passed_check:
        status_emoji = "✅"
        if not expected_sat: 
             print(f"{status_emoji} {property_name_full}: Property HOLDS (negation is UNSAT).{report_suffix}")
        else: 
             print(f"{status_emoji} {property_name_full}: Condition is SAT as expected.{report_suffix}")
        return True
    else:
        status_emoji = "❌"
        if final_result_is_sat is None: 
            outcome_desc = "Solver returned UNKNOWN"
        else: 
            outcome_desc = "UNSAT, but expected SAT" if expected_sat else "SAT, but expected UNSAT (property FAILS)"
        print(f"{status_emoji} {property_name_full}: {outcome_desc}.{report_suffix}")
        return False

# --- Main Execution (Same as before) ---
if __name__ == "__main__":
    # (Your main execution block remains here)
    # ... unchanged ...
    print("AVCA Identity Catalogue Test Script with SMT Scaling (Task ③ & ④) - LLM Final Patch for Grounding v2 + Python Fallback")
    
    print("\n" + "="*70)
    run_identity_catalogue_tests_scaled(Omega_val=2)
    print("="*70)

    print("\n" + "="*70)
    run_identity_catalogue_tests_scaled(Omega_val=3)
    print("="*70)
    
    print("\n" + "="*70)
    # Test with a slightly larger Omega where SMT grounding might still be UNKNOWN
    # and Python fallback should kick in.
    # For Ω=5, Python fallback might take a few seconds (5^3 = 125 iterations for ternary laws).
    # For Ω=7, (7^3 = 343 iterations). For Ω=8 (8^3 = 512).
    # For Ω=10 (10^3 = 1000 iterations). This is where it starts to get noticeable.
    # The LLM suggested brute force up to Ω=10-20 is fine.
    print("Attempting with Omega = 5 (Python fallback might be used if SMT grounding is UNKNOWN):")
    run_identity_catalogue_tests_scaled(Omega_val=5) 
    print("="*70)

    print("\nScript finished.")
    print("\nExpected outcomes based on previous validated runs and Math LLM analysis:")
    print("Ω=2: All listed identities for ⊕ should HOLD.")
    print("Ω=3 and Ω=5:")
    print("  Flexible Law (⊕): Holds")
    print("  Left Alternative Law (⊕): Fails")
    print("  Right Alternative Law (⊕): Fails")
    print("  Power Associativity (⊕): Holds")
    print("  Right Bol Identity (⊕): Fails")
    print("  Moufang Identity (⊕): Fails")
    print("  Steiner Property ((x⊕y)⊕y = x) (⊕): Fails (Holds only for Ω=2 in this set)")