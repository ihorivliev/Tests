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

# Type alias for SMT function for AVCA operations
SMT_AVCA_OP_TYPE = FunctionType(INT, [INT, INT])

# --- Python AVCA Kernel (unchanged) ---
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

# --- Python Identity Definitions (Updated) ---
# Helper for algebraic comparison including Unio
def py_algebraic_equals(lhs: PyAVCVal, rhs: PyAVCVal) -> bool:
    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)
    if lhs_is_unio and rhs_is_unio: return True
    return lhs == rhs

def py_identity_flexible(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    return py_algebraic_equals(add_op(add_op(x_py, y_py), x_py), add_op(x_py, add_op(y_py, x_py)))
def py_identity_left_alternative(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    return py_algebraic_equals(add_op(add_op(x_py, x_py), y_py), add_op(x_py, add_op(x_py, y_py)))
def py_identity_right_alternative(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    return py_algebraic_equals(add_op(add_op(y_py, x_py), x_py), add_op(y_py, add_op(x_py, x_py)))
def py_identity_power_associativity(x_py: PyAVCVal, add_op: Callable) -> bool:
    return py_algebraic_equals(add_op(add_op(x_py,x_py),x_py), add_op(x_py,add_op(x_py,x_py)))
def py_identity_right_bol(x_py: PyAVCVal, y_py: PyAVCVal, z_py: PyAVCVal, add_op: Callable) -> bool:
    return py_algebraic_equals(add_op(add_op(add_op(z_py, y_py), x_py), y_py), add_op(z_py, add_op(add_op(y_py, x_py), y_py)))
def py_identity_moufang_commutative(x_py: PyAVCVal, y_py: PyAVCVal, z_py: PyAVCVal, add_op: Callable) -> bool:
    return py_algebraic_equals(add_op(add_op(add_op(x_py, y_py), z_py), x_py), add_op(x_py, add_op(y_py, add_op(z_py, x_py))))
def py_identity_steiner(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    return py_algebraic_equals(add_op(add_op(x_py,y_py),y_py), x_py)

# LPA: x^n y = x^(n-1) (xy)
def py_identity_left_power_alternative_n3(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    x2 = add_op(x_py, x_py)
    x3 = add_op(x2, x_py) # Assumes power-associativity for x^n definition
    return py_algebraic_equals(add_op(x3, y_py), add_op(x2, add_op(x_py, y_py)))
def py_identity_left_power_alternative_n4(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    x2 = add_op(x_py, x_py)
    x3 = add_op(x2, x_py)
    x4 = add_op(x3, x_py)
    return py_algebraic_equals(add_op(x4, y_py), add_op(x3, add_op(x_py, y_py)))

# RPA: y x^n = (y x^(n-1)) x
def py_identity_right_power_alternative_n3(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    x2 = add_op(x_py, x_py)
    x3 = add_op(x2, x_py)
    return py_algebraic_equals(add_op(y_py, x3), add_op(add_op(y_py, x2), x_py))
def py_identity_right_power_alternative_n4(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    x2 = add_op(x_py, x_py)
    x3 = add_op(x2, x_py)
    x4 = add_op(x3, x_py)
    return py_algebraic_equals(add_op(y_py, x4), add_op(add_op(y_py, x3), x_py))

def py_identity_diassociativity_len3_xy(x_py: PyAVCVal, y_py: PyAVCVal, add_op: Callable) -> bool:
    elements = [x_py, y_py]
    for a_val in elements:
        for b_val in elements:
            for c_val in elements:
                if not py_algebraic_equals(add_op(add_op(a_val, b_val), c_val), add_op(a_val, add_op(b_val, c_val))):
                    return False
    return True

PYTHON_IDENTITY_CHECKERS = {
    "Flexible Law (⊕)": (py_identity_flexible, 2),
    "Left Alternative Law (⊕)": (py_identity_left_alternative, 2), # This is LPA n=2
    "Right Alternative Law (⊕)": (py_identity_right_alternative, 2),# This is RPA n=2
    "Power Associativity (x⊕x)⊕x = x⊕(x⊕x) (⊕)": (py_identity_power_associativity, 1),
    "Right Bol Identity (⊕)": (py_identity_right_bol, 3),
    "Moufang Identity (Commutative form for ⊕)": (py_identity_moufang_commutative, 3),
    "Steiner Property ((x⊕y)⊕y = x) (⊕)": (py_identity_steiner, 2),
    "Left Power-Alternative (n=2) (⊕)": (py_identity_left_alternative, 2), # Explicitly named as per LLM
    "Right Power-Alternative (n=2) (⊕)": (py_identity_right_alternative, 2),# Explicitly named
    "Left Power-Alternative (n=3) (⊕)": (py_identity_left_power_alternative_n3, 2),
    "Right Power-Alternative (n=3) (⊕)": (py_identity_right_power_alternative_n3, 2),
    "Left Power-Alternative (n=4) (⊕)": (py_identity_left_power_alternative_n4, 2),
    "Right Power-Alternative (n=4) (⊕)": (py_identity_right_power_alternative_n4, 2),
    "Diassociativity (length 3 from x,y) (⊕)": (py_identity_diassociativity_len3_xy, 2)
}

def python_brute_force_identity_check(identity_key_name: str, omega_val: int) -> bool: # Unchanged
    if identity_key_name not in PYTHON_IDENTITY_CHECKERS:
        print(f"  WARNING (Python brute-force): No Python checker for identity '{identity_key_name}'.")
        return False 
    identity_checker_func, arity = PYTHON_IDENTITY_CHECKERS[identity_key_name]
    # set_py_avca_omega(omega_val) # This is now called within check_smt_safe_fixed before this function
    py_elements_for_product = []
    for i in range(omega_val): 
        py_elements_for_product.append(_ZERO_UNIO_py_repr if i == 0 else i)
    for value_tuple_py_op_args in itertools.product(py_elements_for_product, repeat=arity):
        if not identity_checker_func(*value_tuple_py_op_args, py_avca_add):
            return False 
    return True 

# --- Grounding Function (Math LLM's Final Patch - from your last successful run) ---
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

# --- SMT Check Utility (Unchanged from your last successful run) ---
def check_smt_safe_fixed(solver: Solver, formula_to_assert: FNode, expected_sat: bool,
                         property_name_full: str, omega_val: int,
                         identity_key_for_py_fallback: Optional[str] = None,
                         print_model_on_debug: bool = True) -> bool:
    global _Omega_py 
    final_result_is_sat: Optional[bool] = None; used_grounding_fallback = False
    used_python_brute_fallback = False; passed_check = False
    grounding_exception_object = None
    solver.push(); solver.add_assertion(formula_to_assert)
    try:
        final_result_is_sat = solver.solve()
    except SolverReturnedUnknownResultError: final_result_is_sat = None
    except Exception as e_initial_solve:
        print(f"  ❌ {property_name_full}: Initial solver.solve() FAILED with: {e_initial_solve!r}")
        final_result_is_sat = None
    if final_result_is_sat is None: 
        solver.pop(); solver.push() 
        original_property_formula_to_ground = None
        if formula_to_assert.is_not() and formula_to_assert.arg(0).is_forall():
            original_property_formula_to_ground = formula_to_assert.arg(0) 
        elif formula_to_assert.is_forall():
            original_property_formula_to_ground = formula_to_assert
        if original_property_formula_to_ground:
            print(f"  ⚠️ {property_name_full}: SMT solver returned UNKNOWN. Attempting SMT grounding fallback for Ω={omega_val}...")
            try:
                grounded_conjunction = ground_forall(original_property_formula_to_ground, omega_val)
                assertion_for_grounded = Not(grounded_conjunction) if formula_to_assert.is_not() else grounded_conjunction
                solver.add_assertion(assertion_for_grounded)
                used_grounding_fallback = True
                current_solve_result = solver.solve()
                if current_solve_result is not None:
                    final_result_is_sat = current_solve_result
                    print(f"  ℹ️ {property_name_full}: SMT grounding fallback yielded: {'SAT' if final_result_is_sat else 'UNSAT'}")
                else:
                    final_result_is_sat = None; print(f"  ⚠️ {property_name_full}: SMT grounding fallback STILL UNKNOWN.")
            except Exception as e_ground: 
                grounding_exception_object = e_ground
                print(f"  ❌ {property_name_full}: ground_forall() FAILED with: {e_ground!r}")
                final_result_is_sat = None 
                if not used_grounding_fallback: used_grounding_fallback = True 
        else:
            print(f"  ⚠️ {property_name_full}: Original UNKNOWN, but formula not ForAll/Not(ForAll) for SMT grounding.")
        if final_result_is_sat is None: 
            if identity_key_for_py_fallback and identity_key_for_py_fallback in PYTHON_IDENTITY_CHECKERS:
                print(f"  🐍 {property_name_full}: SMT UNKNOWN (after SMT grounding attempt if made). Falling back to Python brute-force (Ω={omega_val})...")
                used_python_brute_fallback = True
                current_py_omega_state = _Omega_py; set_py_avca_omega(omega_val)      
                brute_force_holds = python_brute_force_identity_check(identity_key_for_py_fallback, omega_val)
                if brute_force_holds:
                    print(f"  ✅ {property_name_full}: Verified by Python brute-force (Property HOLDS).")
                    final_result_is_sat = False 
                else:
                    print(f"  ❌ {property_name_full}: Counterexample found by Python brute-force (Property FAILS).")
                    final_result_is_sat = True  
                if current_py_omega_state is not None: set_py_avca_omega(current_py_omega_state)
                elif _Omega_py == omega_val : _Omega_py = None
            else:
                print(f"  ⚠️ {property_name_full}: No Python brute-force checker for '{identity_key_for_py_fallback}'. Result remains UNKNOWN.")
    solver.pop() 
    if final_result_is_sat is not None:
        passed_check = (expected_sat and final_result_is_sat) or \
                       (not expected_sat and not final_result_is_sat)
    report_suffix = ""
    if used_python_brute_fallback: report_suffix = " (Resolved via Python brute-force)"
    elif used_grounding_fallback and final_result_is_sat is not None : report_suffix = " (Resolved via SMT grounding)"
    elif used_grounding_fallback and grounding_exception_object: report_suffix = f" (SMT grounding FAILED: {grounding_exception_object!r})"
    elif used_grounding_fallback : report_suffix = " (SMT grounding attempted, result still UNKNOWN)"
    if passed_check:
        status_emoji = "✅"; print(f"{status_emoji} {property_name_full}: Property {'HOLDS (negation is UNSAT)' if not expected_sat else 'Condition is SAT as expected'}.{report_suffix}")
        return True
    else:
        status_emoji = "❌"; outcome_desc = "Solver returned UNKNOWN" if final_result_is_sat is None else \
                       ("UNSAT, but expected SAT" if expected_sat else "SAT, but expected UNSAT (property FAILS)")
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

# --- SMT Identity Catalogue (Added new power-alternative identities) ---
x_id_smt = Symbol("x_identity", INT); y_id_smt = Symbol("y_identity", INT); z_id_smt = Symbol("z_identity", INT)
# Helper for SMT power x^n using smt_avca_add
def smt_power(base: FNode, exp: int, add_op_sym: Callable) -> FNode:
    if exp == 1: return base
    if exp < 1: raise ValueError("Exponent must be positive for SMT power helper")
    res = base
    for _ in range(exp - 1):
        res = add_op_sym(res, base)
    return res

IDENTITIES_CATALOGUE_SMT_ADD = { 
    "Flexible Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x, y), x), smt_avca_add(x, smt_avca_add(y, x))),
    "Left Alternative Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x, x), y), smt_avca_add(x, smt_avca_add(x, y))), # LPA n=2
    "Right Alternative Law (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(y, x), x), smt_avca_add(y, smt_avca_add(x, x))),# RPA n=2
    "Power Associativity (x⊕x)⊕x = x⊕(x⊕x) (⊕)": lambda x: Equals(smt_avca_add(smt_avca_add(x,x),x), smt_avca_add(x,smt_avca_add(x,x))),
    "Right Bol Identity (⊕)": lambda x, y, z: Equals(smt_avca_add(smt_avca_add(smt_avca_add(z, y), x), y), smt_avca_add(z, smt_avca_add(smt_avca_add(y, x), y))),
    "Moufang Identity (Commutative form for ⊕)": lambda x, y, z: Equals(smt_avca_add(smt_avca_add(smt_avca_add(x, y), z), x), smt_avca_add(x, smt_avca_add(y, smt_avca_add(z, x)))),
    "Steiner Property ((x⊕y)⊕y = x) (⊕)": lambda x, y: Equals(smt_avca_add(smt_avca_add(x,y),y), x),
    
    # Explicit Power-Alternative laws for n=2, 3, 4
    "Left Power-Alternative (n=2) (⊕)": lambda x,y: Equals( # Same as L-Alt
        smt_avca_add(smt_power(x,2,smt_avca_add), y), 
        smt_avca_add(smt_power(x,1,smt_avca_add), smt_avca_add(x,y))
    ),
    "Right Power-Alternative (n=2) (⊕)": lambda x,y: Equals( # Same as R-Alt (with y as first arg in identity)
         smt_avca_add(y, smt_power(x,2,smt_avca_add)),
         smt_avca_add(smt_avca_add(y, smt_power(x,1,smt_avca_add)), x)
    ),
    "Left Power-Alternative (n=3) (⊕)": lambda x,y: Equals(
        smt_avca_add(smt_power(x,3,smt_avca_add), y), 
        smt_avca_add(smt_power(x,2,smt_avca_add), smt_avca_add(x,y))
    ),
    "Right Power-Alternative (n=3) (⊕)": lambda x,y: Equals(
         smt_avca_add(y, smt_power(x,3,smt_avca_add)),
         smt_avca_add(smt_avca_add(y, smt_power(x,2,smt_avca_add)), x)
    ),
    "Left Power-Alternative (n=4) (⊕)": lambda x,y: Equals(
        smt_avca_add(smt_power(x,4,smt_avca_add), y), 
        smt_avca_add(smt_power(x,3,smt_avca_add), smt_avca_add(x,y))
    ),
    "Right Power-Alternative (n=4) (⊕)": lambda x,y: Equals(
         smt_avca_add(y, smt_power(x,4,smt_avca_add)),
         smt_avca_add(smt_avca_add(y, smt_power(x,3,smt_avca_add)), x)
    ),
    "Diassociativity (length 3 from x,y) (⊕)": lambda x, y: And(
        Equals(smt_avca_add(smt_avca_add(x,x),x), smt_avca_add(x,smt_avca_add(x,x))), 
        Equals(smt_avca_add(smt_avca_add(x,x),y), smt_avca_add(x,smt_avca_add(x,y))), 
        Equals(smt_avca_add(smt_avca_add(x,y),x), smt_avca_add(x,smt_avca_add(y,x))), 
        Equals(smt_avca_add(smt_avca_add(x,y),y), smt_avca_add(x,smt_avca_add(y,y))), 
        Equals(smt_avca_add(smt_avca_add(y,x),x), smt_avca_add(y,smt_avca_add(x,x))), 
        Equals(smt_avca_add(smt_avca_add(y,x),y), smt_avca_add(y,smt_avca_add(x,y))), 
        Equals(smt_avca_add(smt_avca_add(y,y),x), smt_avca_add(y,smt_avca_add(y,x))), 
        Equals(smt_avca_add(smt_avca_add(y,y),y), smt_avca_add(y,smt_avca_add(y,y)))
    )
}

# --- Main Test Runner (run_identity_catalogue_tests_scaled - unchanged) ---
def run_identity_catalogue_tests_scaled(Omega_val: int):
    # ... (Same setup as before) ...
    print(f"\n--- Task ③ & ④: Testing Identity Catalogue for AVCA (Ω={Omega_val}) with SMT Scaling (LLM Final Patch v4 + Python Fallback) ---") # Renamed test suite
    global smt_avca_add, smt_avca_mul, U_smt_c_global, in_S_Omega_global_pred
    current_add_sym = Symbol(f"avca_add_O{Omega_val}_id_cat_sclFP4", SMT_AVCA_OP_TYPE) 
    current_mul_sym = Symbol(f"avca_mul_O{Omega_val}_id_cat_sclFP4", SMT_AVCA_OP_TYPE) 
    smt_avca_add, smt_avca_mul = current_add_sym, current_mul_sym
    U_smt_c_global, _, in_S_Omega_global_pred_local, avca_axioms = get_avca_v1_axioms(Omega_val, current_add_sym, current_mul_sym)
    in_S_Omega_global_pred = in_S_Omega_global_pred_local
    results_summary = {}
    solver_options = {"smt.random_seed": 42, "smt.mbqi": False} 
    with Solver(name="z3", solver_options=solver_options) as s: 
        for axiom_formula in avca_axioms: s.add_assertion(axiom_formula)
        print(f"\nTesting identities for (S_alg_{Omega_val}, ⊕):")
        for name, smt_identity_lambda in IDENTITIES_CATALOGUE_SMT_ADD.items():
            arity = smt_identity_lambda.__code__.co_argcount
            current_vars_smt = [var for var_idx, var in enumerate([x_id_smt, y_id_smt, z_id_smt]) if var_idx < arity]
            premise_conjuncts = [in_S_Omega_global_pred(v) for v in current_vars_smt]
            premise = And(premise_conjuncts) if current_vars_smt else TRUE()
            identity_body = smt_identity_lambda(*current_vars_smt)
            property_formula = ForAll(current_vars_smt, Implies(premise, identity_body)) if current_vars_smt else Implies(premise, identity_body)
            if not current_vars_smt and isinstance(identity_body, FNode) and identity_body.is_bool_constant():
                 property_formula = identity_body
            holds = check_smt_safe_fixed(s, Not(property_formula), expected_sat=False,
                                         property_name_full=f"Identity '{name}'",
                                         omega_val=Omega_val,
                                         identity_key_for_py_fallback=name 
                                         ) 
            results_summary[name] = "Holds" if holds else "Fails (or Unknown/GroundingFailed)"
    print("\n--- Identity Catalogue Summary ---")
    for name, status in results_summary.items(): print(f"  Ω={Omega_val}: {name}: {status}")
    return results_summary

# --- Main Execution ---
if __name__ == "__main__":
    print("AVCA Identity Catalogue Test Script with SMT Scaling (Task ③ & ④) - LLM Final Patch for Grounding & Python Fallback + New Identities")
    
    # Omega values to test, as requested by the math LLM's latest advice
    # (Ω=2 for baseline, then 3, 4, 5, 6)
    omegas_to_test = [2, 3, 4, 5, 6]

    for test_omega in omegas_to_test:
        print("\n" + "="*70)
        # This function will print its own detailed "Identity Catalogue Summary" for the current Omega
        run_identity_catalogue_tests_scaled(Omega_val=test_omega)
        print("="*70)

    print("\nScript finished.")
    print("Please review the 'Identity Catalogue Summary' output for each Omega value above.")
    print("This output should be compared against mathematical expectations and loop theory literature for classification.")