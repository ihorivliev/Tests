# ==========================================================
# AVCA_Ω – SMT Proof Script (V12 - Corrected Calls, Full Gems 4 & 5)
# Includes Core Gem 1.1 properties, and new Gems 4 & 5 explorations.
# Using PySMT + Z3
# ==========================================================

from pysmt.shortcuts import (
    Symbol, Int, And, Or, Not, Equals, Ite, Plus, Times, LE, LT, GE,
    FreshSymbol, ForAll, Exists, Solver, is_sat, is_unsat, NotEquals,
    get_model, Portfolio, BOOL, Implies
)
from pysmt.typing import INT, FunctionType, BOOL as SMT_BOOL_TYPE
from typing import List, Dict, Tuple, Callable, Any, Optional
import itertools
import math

# --- Python AVCA "Best Combination" Kernel (for brute-force checks) ---
_Omega_py: Optional[int] = None
_ZERO_UNIO_py_repr = "Unio('zero')"
_AREO_UNIO_py_repr = "Unio('areo')"
PyAVCVal = Any

def U_py_repr_val(val_repr: PyAVCVal) -> str:
    if val_repr == _ZERO_UNIO_py_repr: return "U_z"
    if val_repr == _AREO_UNIO_py_repr: return "U_a"
    return str(val_repr)

def set_py_avca_omega(omega_val: int):
    global _Omega_py
    if not isinstance(omega_val, int) or omega_val < 1:
        raise ValueError("Python AVCA Omega must be >= 1.")
    _Omega_py = omega_val

def _check_py_val(x: PyAVCVal, omega: int, op_name: str = "py_op", arg_name: str = "input"):
    if x == _ZERO_UNIO_py_repr or x == _AREO_UNIO_py_repr: return
    if not isinstance(x, int): raise TypeError(f"Py AVCA val for {op_name}/{arg_name} must be int or Unio sentinel: {x}")
    if omega == 1 and isinstance(x, int): raise ValueError(f"DFI {x} invalid for {op_name}/{arg_name} for Python AVCA Omega=1")
    if omega > 1 and not (1 <= x < omega): raise ValueError(f"DFI {x} out of range [1, {omega-1}] for {op_name}/{arg_name} for Python AVCA Omega={omega}")

def py_avca_add(a: PyAVCVal, b: PyAVCVal) -> PyAVCVal:
    if _Omega_py is None: raise ValueError("Python AVCA Omega not set for py_avca_add.")
    _check_py_val(a, _Omega_py, "py_avca_add", "a"); _check_py_val(b, _Omega_py, "py_avca_add", "b")
    if a == _ZERO_UNIO_py_repr or a == _AREO_UNIO_py_repr: return b
    if b == _ZERO_UNIO_py_repr or b == _AREO_UNIO_py_repr: return a
    res: int = a + b # type: ignore
    return res if res < _Omega_py else _AREO_UNIO_py_repr

def py_avca_mul(a: PyAVCVal, b: PyAVCVal) -> PyAVCVal:
    if _Omega_py is None: raise ValueError("Python AVCA Omega not set for py_avca_mul.")
    _check_py_val(a, _Omega_py, "py_avca_mul", "a"); _check_py_val(b, _Omega_py, "py_avca_mul", "b")
    is_a_zu = a == _ZERO_UNIO_py_repr; is_a_au = a == _AREO_UNIO_py_repr
    is_b_zu = b == _ZERO_UNIO_py_repr; is_b_au = b == _AREO_UNIO_py_repr
    if is_a_zu or is_a_au or is_b_zu or is_b_au:
        return _AREO_UNIO_py_repr if is_a_au or is_b_au else _ZERO_UNIO_py_repr
    else: 
        res: int = a * b # type: ignore
        return res if 1 <= res < _Omega_py else _AREO_UNIO_py_repr
# --- End Python AVCA Ops ---

SMT_OP_TYPE = FunctionType(INT, [INT, INT])

def check_smt(solver: Solver, formula: object, expected_sat: bool,
              property_name: str, print_model_on_debug: bool = True) -> bool:
    solver.push()
    solver.add_assertion(formula)
    result = solver.solve()
    model_str = ""
    passed_check = (expected_sat and result) or (not expected_sat and not result)
    if not passed_check and result and print_model_on_debug:
        model_str = f" (Debug: Model/Counterexample exists for unexpected SAT)"
    elif expected_sat and result and print_model_on_debug and "Exists" in property_name : # Crude check for witness
        model_str = f" (Debug: Witness model exists)"
    solver.pop()
    if passed_check:
        status_emoji = "✅"; outcome_desc = "SAT as expected" if expected_sat else "UNSAT as expected"
        print(f"{status_emoji} {property_name}: {outcome_desc}.{model_str}")
        return True
    else:
        status_emoji = "❌"; outcome_desc = "UNSAT, but expected SAT" if expected_sat else "SAT, but expected UNSAT"
        print(f"{status_emoji} {property_name}: {outcome_desc}.{model_str}")
        return False

def get_avca_axiom_formulas(Omega_val: int, # Python int for Omega
                            add_func_sym_to_use: object, 
                            mul_func_sym_to_use: object) -> \
                            Tuple[object, Callable[[Any], Any], Callable[[Any], Any], List[object]]:
    Omega_smt_c = Int(Omega_val); U_smt_c = Int(0)
    in_S_Omega_f = lambda x_var: And(GE(x_var, Int(0)), LT(x_var, Omega_smt_c))
    is_DFI_f: Callable[[Any], Any] = (lambda x_var: Equals(Int(0), Int(1))) if Omega_val == 1 \
        else (lambda x_var: And(GE(x_var, Int(1)), LT(x_var, Omega_smt_c)))
    
    func_name_prefix = add_func_sym_to_use.symbol_name().split('_O')[0] 
    x_ax = Symbol(f"x_ax_{func_name_prefix}_O{Omega_val}", INT)
    y_ax = Symbol(f"y_ax_{func_name_prefix}_O{Omega_val}", INT)
    q_vars_ax = [x_ax, y_ax]; sum_ax = Plus(x_ax,y_ax); prod_ax = Times(x_ax,y_ax)
    
    ax_list = [
        ForAll([x_ax],Implies(in_S_Omega_f(x_ax),Equals(add_func_sym_to_use(U_smt_c,x_ax),x_ax))),
        ForAll([x_ax],Implies(in_S_Omega_f(x_ax),Equals(add_func_sym_to_use(x_ax,U_smt_c),x_ax))),
        ForAll(q_vars_ax,Implies(And(in_S_Omega_f(x_ax),in_S_Omega_f(y_ax),is_DFI_f(x_ax),is_DFI_f(y_ax),LT(sum_ax,Omega_smt_c)),Equals(add_func_sym_to_use(x_ax,y_ax),sum_ax))),
        ForAll(q_vars_ax,Implies(And(in_S_Omega_f(x_ax),in_S_Omega_f(y_ax),is_DFI_f(x_ax),is_DFI_f(y_ax),GE(sum_ax,Omega_smt_c)),Equals(add_func_sym_to_use(x_ax,y_ax),U_smt_c))),
        ForAll([x_ax],Implies(in_S_Omega_f(x_ax),Equals(mul_func_sym_to_use(U_smt_c,x_ax),U_smt_c))),
        ForAll([x_ax],Implies(in_S_Omega_f(x_ax),Equals(mul_func_sym_to_use(x_ax,U_smt_c),U_smt_c))),
        ForAll(q_vars_ax,Implies(And(in_S_Omega_f(x_ax),in_S_Omega_f(y_ax),is_DFI_f(x_ax),is_DFI_f(y_ax),GE(prod_ax,Int(1)),LT(prod_ax,Omega_smt_c)),Equals(mul_func_sym_to_use(x_ax,y_ax),prod_ax))),
        ForAll(q_vars_ax,Implies(And(in_S_Omega_f(x_ax),in_S_Omega_f(y_ax),is_DFI_f(x_ax),is_DFI_f(y_ax),GE(prod_ax,Omega_smt_c)),Equals(mul_func_sym_to_use(x_ax,y_ax),U_smt_c)))
    ]
    return U_smt_c, is_DFI_f, in_S_Omega_f, ax_list

# --- Gem 4: Loop-theoretic DNA --- (Copied from V11 which produced "Bellissimo")
def run_gem4_tests(Omega_val: int, s: Solver, add_op_func_callable: Callable, U_smt_const: object,
                   is_DFI_pred: Callable, in_S_Omega_pred: Callable) -> bool:
    print("\n--- Gem 4: Associator Defect & Loop Classification ---")
    overall_gem4_passed = True
    
    print("\nGem 4-A: Checking Loop Properties for ⊕...")
    x_lp_q = Symbol(f"x_lp_q_O{Omega_val}", INT)
    y_lp_q = Symbol(f"y_lp_q_O{Omega_val}", INT)
    z_lp_q = Symbol(f"z_lp_q_O{Omega_val}", INT) 
    q2li = [x_lp_q, y_lp_q]; q3li = [x_lp_q, y_lp_q, z_lp_q]
    
    if Omega_val <= 2:
        print(f"✅ ⊕ Left Inverse Existence (Loop property): Holds by inspection for Ω={Omega_val}.")
    else: 
        prop_left_inv_exists = ForAll([x_lp_q], Implies(in_S_Omega_pred(x_lp_q),
                                                Exists([y_lp_q], And(in_S_Omega_pred(y_lp_q),
                                                               Equals(add_op_func_callable(x_lp_q,y_lp_q), U_smt_const)))))
        if not check_smt(s, Not(prop_left_inv_exists), False, f"⊕ Left Inverse Existence (Loop property) for Ω={Omega_val}"): 
            overall_gem4_passed = False

    prop_power_assoc = ForAll([x_lp_q], Implies(in_S_Omega_pred(x_lp_q),
                                       Equals(add_op_func_callable(add_op_func_callable(x_lp_q,x_lp_q),x_lp_q),
                                              add_op_func_callable(x_lp_q,add_op_func_callable(x_lp_q,x_lp_q)))))
    if not check_smt(s, Not(prop_power_assoc), False, "⊕ Power-Associativity"): 
        overall_gem4_passed = False
    
    if overall_gem4_passed : 
        print(f"   ⊕ (for Ω={Omega_val}) confirmed consistent with Commutative (prev. proven), Power-Associative Loop with Inverses (or passed specific checks).")

    lhs_flex = add_op_func_callable(add_op_func_callable(x_lp_q, y_lp_q), x_lp_q)
    rhs_flex = add_op_func_callable(x_lp_q, add_op_func_callable(y_lp_q, x_lp_q))
    flexible_law_prop = ForAll(q2li, Implies(And(in_S_Omega_pred(x_lp_q), in_S_Omega_pred(y_lp_q)), Equals(lhs_flex, rhs_flex)))
    if not check_smt(s, Not(flexible_law_prop), False, f"⊕ Flexible Law (Ω={Omega_val})"): overall_gem4_passed = False

    left_alt_law = ForAll(q2li, Implies(And(in_S_Omega_pred(x_lp_q), in_S_Omega_pred(y_lp_q)),
                                     Equals(add_op_func_callable(add_op_func_callable(x_lp_q,x_lp_q),y_lp_q), 
                                            add_op_func_callable(x_lp_q,add_op_func_callable(x_lp_q,y_lp_q)))))
    if not check_smt(s, Not(left_alt_law), (Omega_val > 2), f"⊕ Left Alternative Law (Fails Ω≥3)"): overall_gem4_passed = False

    right_alt_law = ForAll(q2li, Implies(And(in_S_Omega_pred(x_lp_q), in_S_Omega_pred(y_lp_q)),
                                     Equals(add_op_func_callable(add_op_func_callable(x_lp_q,y_lp_q),y_lp_q), 
                                            add_op_func_callable(x_lp_q,add_op_func_callable(y_lp_q,y_lp_q)))))
    if not check_smt(s, Not(right_alt_law), (Omega_val > 2), f"⊕ Right Alternative Law (Fails Ω≥3)"): overall_gem4_passed = False
    
    lhs_bol = add_op_func_callable(add_op_func_callable(add_op_func_callable(z_lp_q,y_lp_q),x_lp_q),y_lp_q)
    rhs_bol_inner = add_op_func_callable(add_op_func_callable(y_lp_q,x_lp_q),y_lp_q)
    rhs_bol = add_op_func_callable(z_lp_q,rhs_bol_inner)
    right_bol_law = ForAll(q3li, Implies(And(in_S_Omega_pred(x_lp_q), in_S_Omega_pred(y_lp_q), in_S_Omega_pred(z_lp_q)), Equals(lhs_bol, rhs_bol)))
    if not check_smt(s, Not(right_bol_law), (Omega_val > 2), f"⊕ Right Bol Identity (Fails Ω≥3)"): overall_gem4_passed = False
    
    print("\nGem 4-B: Analyzing Associator Defect for ⊕...")
    a_ad_q = Symbol(f"a_ad_q_O{Omega_val}", INT); b_ad_q = Symbol(f"b_ad_q_O{Omega_val}", INT); c_ad_q = Symbol(f"c_ad_q_O{Omega_val}", INT)
    q_vars_ad = [a_ad_q, b_ad_q, c_ad_q]
    associativity_holds_for_triplet = Equals(add_op_func_callable(add_op_func_callable(a_ad_q,b_ad_q),c_ad_q),
                                             add_op_func_callable(a_ad_q,add_op_func_callable(b_ad_q,c_ad_q)))
    associator_fails_for_triplet = Not(associativity_holds_for_triplet)
    exists_defect_triplet = Exists(q_vars_ad, And(in_S_Omega_pred(a_ad_q), in_S_Omega_pred(b_ad_q), in_S_Omega_pred(c_ad_q), associator_fails_for_triplet))
    expected_sat_defect = (Omega_val >= 3)
    if not check_smt(s, exists_defect_triplet, expected_sat_defect, f"⊕ Non-Associative Triplet Exists (Expect SAT for Ω≥3)"): overall_gem4_passed = False
    defect_claim_condition = ForAll(q_vars_ad, Implies(
                                        And(in_S_Omega_pred(a_ad_q), in_S_Omega_pred(b_ad_q), in_S_Omega_pred(c_ad_q),
                                            Not(Equals(a_ad_q,U_smt_const)), Not(Equals(b_ad_q,U_smt_const))),
                                        associativity_holds_for_triplet ))
    expected_sat_for_not_defect_claim = (Omega_val >= 3) 
    if not check_smt(s, Not(defect_claim_condition), expected_sat_for_not_defect_claim, 
                     f"⊕ Defect Claim (associative if a≠U & b≠U) - Expect {'SAT (claim is false)' if expected_sat_for_not_defect_claim else 'UNSAT (claim is true)'}"): overall_gem4_passed = False
    print(f"   Calculating Nucleus Size for ⊕ (Ω={Omega_val}):")
    nucleus_set_py = []
    n_nuc_sym = Symbol(f"n_nuc_O{Omega_val}", INT) 
    x_nuc_q_gem4b = Symbol(f"x_nuc_q_gem4b_O{Omega_val}", INT); y_nuc_q_gem4b = Symbol(f"y_nuc_q_gem4b_O{Omega_val}", INT) 
    is_in_nucleus_prop_for_n = ForAll([x_nuc_q_gem4b, y_nuc_q_gem4b], Implies(
                                And(in_S_Omega_pred(x_nuc_q_gem4b), in_S_Omega_pred(y_nuc_q_gem4b)), 
                                Equals(add_op_func_callable(add_op_func_callable(n_nuc_sym, x_nuc_q_gem4b), y_nuc_q_gem4b), 
                                       add_op_func_callable(n_nuc_sym, add_op_func_callable(x_nuc_q_gem4b, y_nuc_q_gem4b)))))
    current_nucleus_passed_expectation = True
    for k_val_iter in range(Omega_val):
        k_smt_iter = Int(k_val_iter)
        prop_k_is_nucleus = Implies(in_S_Omega_pred(k_smt_iter), is_in_nucleus_prop_for_n.substitute({n_nuc_sym: k_smt_iter}))
        s.push(); s.add_assertion(Not(prop_k_is_nucleus)); k_is_provably_in_nucleus = not s.solve(); s.pop()
        expected_to_be_in_nucleus = (Omega_val <= 2) or (k_val_iter == 0)
        if k_is_provably_in_nucleus:
            nucleus_set_py.append(k_val_iter); print(f"    Confirmed: {k_val_iter} IS in ⊕-nucleus.")
            if not expected_to_be_in_nucleus: print(f"    >>> WARNING: {k_val_iter} IN nucleus, NOT expected (Ω={Omega_val})."); current_nucleus_passed_expectation = False
        else:
            print(f"    Confirmed: {k_val_iter} is NOT in ⊕-nucleus.")
            if expected_to_be_in_nucleus: print(f"    >>> WARNING: {k_val_iter} NOT in nucleus, WAS expected (Ω={Omega_val})."); current_nucleus_passed_expectation = False
    if not current_nucleus_passed_expectation: overall_gem4_passed = False
    print(f"   Nucleus Elements for ⊕ (Ω={Omega_val}): {nucleus_set_py}"); print(f"   Nucleus Size = {len(nucleus_set_py)}")
    expected_nucleus_size = Omega_val if Omega_val <= 2 else 1 
    if len(nucleus_set_py) != expected_nucleus_size:
        print(f"   WARNING: ⊕-Nucleus size {len(nucleus_set_py)} != expected {expected_nucleus_size}."); overall_gem4_passed = False
    else: print(f"   ⊕-Nucleus size matches expectation ({expected_nucleus_size}).")

    print("\nGem 4-C: Associator Distribution Histogram for ⊕...")
    if Omega_val <= 5: 
        set_py_avca_omega(Omega_val)
        py_U_hist = _ZERO_UNIO_py_repr 
        py_S_Omega_hist = [py_U_hist] + list(range(1, Omega_val)) if Omega_val > 1 else [py_U_hist]
        associator_hist_py: Dict[Tuple[str,str], int] = {}
        for val_a_h in py_S_Omega_hist:
            for val_b_h in py_S_Omega_hist:
                for val_c_h in py_S_Omega_hist:
                    try:
                        lhs_h = py_avca_add(py_avca_add(val_a_h, val_b_h), val_c_h)
                        rhs_h = py_avca_add(val_a_h, py_avca_add(val_b_h, val_c_h))
                        pair_repr_h = (U_py_repr_val(lhs_h), U_py_repr_val(rhs_h))
                        associator_hist_py[pair_repr_h] = associator_hist_py.get(pair_repr_h, 0) + 1
                    except ValueError: associator_hist_py[("ERROR", "ERROR")] = associator_hist_py.get(("ERROR", "ERROR"), 0) + 1
        print(f"Associator Histogram for Ω={Omega_val} ((LHS,RHS) : count):")
        for pair_h, count_h in sorted(associator_hist_py.items()):
            print(f"  {pair_h}: {count_h}{'  <-- Non-associative instances' if pair_h[0] != pair_h[1] else ''}")
    else: print("   Skipping associator histogram for Ω > 5.")
    return overall_gem4_passed

# --- Gem 5: Distributive Islands ---
def run_gem5_tests(Omega_val: int, s: Solver, add_op_func_callable: Callable, mul_op_func_callable: Callable, 
                   U_smt_const: object, is_DFI_pred: Callable, in_S_Omega_pred: Callable) -> bool: 
    print(f"\n--- Gem 5: Distributive Islands ---")
    overall_gem5_passed = True
    print(f"\nGem 5-A: Testing Candidate Distributive Sub-algebra {{U,1,Ω-1}} for Ω={Omega_val}...")
    if Omega_val < 2: print("   N/A for Ω < 2."); return True 
    one_smt_val = Int(1)
    if Omega_val == 2:
         print(f"   For Ω=2, candidate subset is effectively {{U,1}} (F2). Testing F2 properties:")
         subset_R_F2 = lambda v_var: Or(Equals(v_var, U_smt_const), Equals(v_var, one_smt_val))
         a_f2,b_f2,c_f2 = Symbol(f"a_f2_O{Omega_val}",INT), Symbol(f"b_f2_O{Omega_val}",INT), Symbol(f"c_f2_O{Omega_val}",INT)
         q_f2 = [a_f2,b_f2,c_f2]
         cl_add_f2 = ForAll(q_f2[:2], Implies(And(subset_R_F2(a_f2),subset_R_F2(b_f2)), subset_R_F2(add_op_func_callable(a_f2,b_f2))))
         cl_mul_f2 = ForAll(q_f2[:2], Implies(And(subset_R_F2(a_f2),subset_R_F2(b_f2)), subset_R_F2(mul_op_func_callable(a_f2,b_f2))))
         ass_add_f2 = ForAll(q_f2, Implies(And(subset_R_F2(a_f2),subset_R_F2(b_f2),subset_R_F2(c_f2)), Equals(add_op_func_callable(add_op_func_callable(a_f2,b_f2),c_f2), add_op_func_callable(a_f2,add_op_func_callable(b_f2,c_f2)))))
         dist_f2 = ForAll(q_f2, Implies(And(subset_R_F2(a_f2),subset_R_F2(b_f2),subset_R_F2(c_f2)), Equals(mul_op_func_callable(a_f2,add_op_func_callable(b_f2,c_f2)),add_op_func_callable(mul_op_func_callable(a_f2,b_f2),mul_op_func_callable(a_f2,c_f2)))))
         if not check_smt(s, Not(cl_add_f2), False, "  {U,1} Closure ⊕ (Ω=2)"): overall_gem5_passed=False
         if not check_smt(s, Not(cl_mul_f2), False, "  {U,1} Closure ⊗ (Ω=2)"): overall_gem5_passed=False
         if not check_smt(s, Not(ass_add_f2), False, "  {U,1} Assoc ⊕ (Ω=2)"): overall_gem5_passed=False
         if not check_smt(s, Not(dist_f2), False, "  {U,1} Distrib (Ω=2)"): overall_gem5_passed=False
         if not overall_gem5_passed: return False
    elif Omega_val >= 3:
        omega_minus_1_smt_val = Int(Omega_val - 1)
        subset_R_U1Top = lambda v_var: Or(Equals(v_var, U_smt_const), Equals(v_var, one_smt_val), Equals(v_var, omega_minus_1_smt_val))
        a_u1t,b_u1t,c_u1t = Symbol(f"a_u1t_O{Omega_val}",INT), Symbol(f"b_u1t_O{Omega_val}",INT), Symbol(f"c_u1t_O{Omega_val}",INT)
        q_u1t = [a_u1t,b_u1t,c_u1t]
        current_candidate_passed = True
        prop_closure_add_u1t = ForAll(q_u1t[:2], Implies(And(subset_R_U1Top(a_u1t),subset_R_U1Top(b_u1t)), subset_R_U1Top(add_op_func_callable(a_u1t,b_u1t))))
        if not check_smt(s, Not(prop_closure_add_u1t), False, "  {U,1,Ω-1} Closure under ⊕"): current_candidate_passed=False
        prop_closure_mul_u1t = ForAll(q_u1t[:2], Implies(And(subset_R_U1Top(a_u1t),subset_R_U1Top(b_u1t)), subset_R_U1Top(mul_op_func_callable(a_u1t,b_u1t))))
        if not check_smt(s, Not(prop_closure_mul_u1t), False, "  {U,1,Ω-1} Closure under ⊗"): current_candidate_passed=False
        prop_assoc_add_sub_u1t = ForAll(q_u1t, Implies(And(subset_R_U1Top(a_u1t),subset_R_U1Top(b_u1t),subset_R_U1Top(c_u1t)), 
                                                       Equals(add_op_func_callable(add_op_func_callable(a_u1t,b_u1t),c_u1t), add_op_func_callable(a_u1t,add_op_func_callable(b_u1t,c_u1t)))))
        if not check_smt(s, Not(prop_assoc_add_sub_u1t), True, f"  {{U,1,Ω-1}} ⊕-Non-Associativity (Expect SAT for Ω≥3)"): current_candidate_passed=False
        prop_distrib_sub_u1t = ForAll(q_u1t, Implies(And(subset_R_U1Top(a_u1t),subset_R_U1Top(b_u1t),subset_R_U1Top(c_u1t)),
                                                   Equals(mul_op_func_callable(a_u1t, add_op_func_callable(b_u1t,c_u1t)),
                                                          add_op_func_callable(mul_op_func_callable(a_u1t,b_u1t), mul_op_func_callable(a_u1t,c_u1t)))))
        if not check_smt(s, Not(prop_distrib_sub_u1t), True, f"  {{U,1,Ω-1}} Non-Distributivity (Expect SAT for Ω≥3)"): current_candidate_passed=False
        print(f"   Overall for {{U,1,Ω-1}} at Ω={Omega_val}: {'Test results align with expectations' if current_candidate_passed else 'Some test results FAILED against expectation'}")
        if not current_candidate_passed: overall_gem5_passed = False
    
    print(f"\nGem 5-B: Simplified Check for Largest Distributive Subset Size (Ω={Omega_val})...")
    a_lds,b_lds,c_lds = Symbol(f"a_lds_O{Omega_val}",INT), Symbol(f"b_lds_O{Omega_val}",INT), Symbol(f"c_lds_O{Omega_val}",INT)
    q_vars_lds = [a_lds,b_lds,c_lds]
    prop_distrib_global = ForAll(q_vars_lds, Implies(And(in_S_Omega_pred(a_lds), in_S_Omega_pred(b_lds), in_S_Omega_pred(c_lds)),
                                                 Equals(mul_op_func_callable(a_lds, add_op_func_callable(b_lds,c_lds)),
                                                        add_op_func_callable(mul_op_func_callable(a_lds,b_lds), mul_op_func_callable(a_lds,c_lds)))))
    if Omega_val <= 2:
        if check_smt(s, Not(prop_distrib_global), False, f"  Global Distributivity (Ω={Omega_val} ≤ 2)"):
            print(f"   Ω={Omega_val}: Global distributivity holds. Largest size is {Omega_val}.")
        else: print(f"   Ω={Omega_val}: Global distributivity FAILED for S_Omega (unexpected)."); overall_gem5_passed=False
    else: # Omega_val >= 3
        if check_smt(s, Not(prop_distrib_global), True, f"  Global Non-Distributivity (Ω={Omega_val} ≥ 3)"):
            print(f"   Ω={Omega_val}: Global distributivity fails as expected. Known proper rings are size 2 {{U,k}}.")
            if Omega_val == 3:
                k_cand = Int(2) 
                subset_R_Uk_actual = lambda v_var: Or(Equals(v_var, U_smt_const), Equals(v_var, k_cand))
                prop_distrib_Uk = ForAll(q_vars_lds, Implies(And(subset_R_Uk_actual(a_lds),subset_R_Uk_actual(b_lds),subset_R_Uk_actual(c_lds)),
                                                        Equals(mul_op_func_callable(a_lds,add_op_func_callable(b_lds,c_lds)),add_op_func_callable(mul_op_func_callable(a_lds,b_lds),mul_op_func_callable(a_lds,c_lds)))))
                if not check_smt(s, Not(prop_distrib_Uk), False, "  Distributivity for {U,2} (Ω=3)"): overall_gem5_passed=False
        else: print(f"   Ω={Omega_val}: Global distributivity HELD for S_Omega (unexpected for Ω≥3)."); overall_gem5_passed=False
    return overall_gem5_passed

# --- Track ④: Asymptotic & analytic viewpoint (Pythonic Brute Force) ---
def run_track4_asymptotic_analysis(Omega_val: int) -> bool:
    print(f"\n--- Track ④: Asymptotic & Analytic Viewpoint (Ω={Omega_val}) ---")
    if Omega_val < 3:
        print("   Defect density not applicable for Ω < 3.")
        return True 
    set_py_avca_omega(Omega_val) 
    py_U_val_hist = _ZERO_UNIO_py_repr 
    py_S_Omega_elements = [py_U_val_hist] + list(range(1, Omega_val)) if Omega_val > 1 else [py_U_val_hist]
    print(f"Calculating ⊕-associativity defect density for Ω={Omega_val}...")
    fails = 0
    total_triples = len(py_S_Omega_elements)**3
    if total_triples == 0: return True 
    # Inside run_track4_asymptotic_analysis function
    # ... (setup code for py_S_Omega_elements, total_triples remains the same) ...
    for a_py_h in py_S_Omega_elements:
        for b_py_h in py_S_Omega_elements:
            for c_py_h in py_S_Omega_elements:
                try:
                    lhs_h = py_avca_add(py_avca_add(a_py_h, b_py_h), c_py_h)
                    rhs_h = py_avca_add(a_py_h, py_avca_add(b_py_h, c_py_h))
                    
                    # Algebraic comparison:
                    # Unio objects are algebraically equal regardless of specific aspect representation
                    lhs_is_py_unio = lhs_h == _ZERO_UNIO_py_repr or lhs_h == _AREO_UNIO_py_repr
                    rhs_is_py_unio = rhs_h == _ZERO_UNIO_py_repr or rhs_h == _AREO_UNIO_py_repr

                    if lhs_is_py_unio and rhs_is_py_unio:
                        # Both are Unio, so algebraically equal
                        pass 
                    elif lhs_h == rhs_h: # Covers DFI==DFI and catches cases where one might be Unio and other DFI
                        pass
                    else: # They are algebraically different
                        fails += 1
                except ValueError: 
                    fails += 1 # Count as a failure if op itself fails for some reason
    
    density = fails / total_triples if total_triples > 0 else 0.0
    print(f"   Ω={Omega_val}, Failing Triples = {fails}, Total Triples = {total_triples}, Defect Density = {density:.4f}")
    return True

# --- Main Execution Structure ---
def prove_for_all_gems_v2(Omega_val: int): # Main test harness for a given Omega
    print(f"\n{'='*20} Verifying AVCA Gems for Ω = {Omega_val} {'='*20}")
    solver_options = {"smt.random_seed": 42}      # <- MBQI left at default (true)
    with Solver(name="z3", solver_options=solver_options) as s:
        s.push()
        main_add_func_sym  = Symbol(f"avca_add_main_O{Omega_val}", SMT_OP_TYPE)
        main_mul_func_sym  = Symbol(f"avca_mul_main_O{Omega_val}", SMT_OP_TYPE)

        U_const_main, isDFI_pred_main, inS_pred_main, main_axioms_formula_list = \
            get_avca_axiom_formulas(Omega_val, main_add_func_sym, main_mul_func_sym)
        for ax_formula in main_axioms_formula_list: 
            s.add_assertion(ax_formula)
        
        def add_op_main_call(t1, t2): return main_add_func_sym(t1,t2)
        def mul_op_main_call(t1, t2): return main_mul_func_sym(t1,t2)
        
        all_passed_this_omega = True

        print("\n--- Verifying Gem 1.1 Core Properties ---")
        x_core_q = Symbol(f"x_core_O{Omega_val}", INT); y_core_q = Symbol(f"y_core_O{Omega_val}", INT); z_core_q = Symbol(f"z_core_O{Omega_val}", INT)
        q2c = [x_core_q,y_core_q]; q3c = [x_core_q,y_core_q,z_core_q]

        print("\nChecking Commutativity...")
        p_comm_add = ForAll(q2c, Implies(And(inS_pred_main(x_core_q),inS_pred_main(y_core_q)), Equals(add_op_main_call(x_core_q,y_core_q),add_op_main_call(y_core_q,x_core_q))))
        if not check_smt(s,Not(p_comm_add),False,"Commutativity of ⊕"):all_passed_this_omega=False
        p_comm_mul = ForAll(q2c, Implies(And(inS_pred_main(x_core_q),inS_pred_main(y_core_q)), Equals(mul_op_main_call(x_core_q,y_core_q),mul_op_main_call(y_core_q,x_core_q))))
        if not check_smt(s,Not(p_comm_mul),False,"Commutativity of ⊗"):all_passed_this_omega=False

        print("\nChecking Associativity of ⊗...")
        p_assoc_mul=ForAll(q3c,Implies(And(inS_pred_main(x_core_q),inS_pred_main(y_core_q),inS_pred_main(z_core_q)),Equals(mul_op_main_call(mul_op_main_call(x_core_q,y_core_q),z_core_q),mul_op_main_call(x_core_q,mul_op_main_call(y_core_q,z_core_q)))))
        if not check_smt(s,Not(p_assoc_mul),False,"Associativity of ⊗"):all_passed_this_omega=False

        print("\nChecking Phase Transition of ⊕-Associativity...")
        p_assoc_add=ForAll(q3c,Implies(And(inS_pred_main(x_core_q),inS_pred_main(y_core_q),inS_pred_main(z_core_q)),Equals(add_op_main_call(add_op_main_call(x_core_q,y_core_q),z_core_q),add_op_main_call(x_core_q,add_op_main_call(y_core_q,z_core_q)))))
        if Omega_val<=2:
            if not check_smt(s,Not(p_assoc_add),False,f"⊕-Associativity (Ω={Omega_val} ≤ 2)"):all_passed_this_omega=False
        else: # Omega_val >= 3
            if not check_smt(s,Not(p_assoc_add),True,f"⊕-Non-Associativity (Ω={Omega_val} ≥ 3)"):all_passed_this_omega=False
            # Check counterexample only if Omega_val >= 3 (where 1 and Omega_val-1 are distinct DFIs)
            if Omega_val>=3 : 
                one_smt=Int(1)
                omega_minus_1_val = Omega_val-1 # This is DFI if Omega_val >= 2
                # Ensure 'one' is a valid DFI (i.e. 1 < Omega_val, so Omega_val >= 2)
                # And omega_minus_1_val is a DFI (i.e. omega_minus_1_val >= 1 so Omega_val >=2)
                # For the (1,1,Omega-1) counterexample, we need DFI(1) and DFI(Omega-1) to be valid.
                # DFI(1) exists if Omega_val >= 2.
                # DFI(Omega-1) exists if Omega_val-1 >= 1 => Omega_val >= 2.
                # For them to be used in (1,1,Omega-1), we need Omega_val >= 3 for non-trivial distinctness from U in some cases.
                if 1 < Omega_val and omega_minus_1_val >= 1 : # Both 1 and Omega-1 are valid DFIs
                    om1_smt=Int(omega_minus_1_val)
                    lhs_cex=add_op_main_call(add_op_main_call(one_smt,one_smt),om1_smt)
                    rhs_cex=add_op_main_call(one_smt,add_op_main_call(one_smt,om1_smt))
                    cex_f=NotEquals(lhs_cex,rhs_cex)
                    if not check_smt(s,cex_f,True,f"⊕-Non-Associativity Counterexample (1,1,Ω-1) for Ω={Omega_val}"):all_passed_this_omega=False
        
        print("\nChecking Global Distributivity (⊗ over ⊕)...")
        p_dist=ForAll(q3c,Implies(And(inS_pred_main(x_core_q),inS_pred_main(y_core_q),inS_pred_main(z_core_q)),Equals(mul_op_main_call(x_core_q,add_op_main_call(y_core_q,z_core_q)),add_op_main_call(mul_op_main_call(x_core_q,y_core_q),mul_op_main_call(x_core_q,z_core_q)))))
        if Omega_val>=3:
            if not check_smt(s,Not(p_dist),True,f"Non-Distributivity (Ω={Omega_val} ≥ 3)"):all_passed_this_omega=False
        else:
            if not check_smt(s,Not(p_dist),False,f"Distributivity (Ω={Omega_val} ≤ 2)"):all_passed_this_omega=False

        print("\nChecking Uniqueness of Tables...")
        add2_f_sym_uniq = Symbol(f"avca_add2_uniq_O{Omega_val}", SMT_OP_TYPE)
        mul2_f_sym_uniq = Symbol(f"avca_mul2_uniq_O{Omega_val}", SMT_OP_TYPE)
        
        # Corrected: get_avca_axiom_formulas returns 4 items.
        # We only need the list of axioms for add2_f_sym_uniq and mul2_f_sym_uniq.
        _u2_dummy, _isDFI2_dummy, _inS2_dummy, axioms2_list_formulas_uniq = \
            get_avca_axiom_formulas(Omega_val, add2_f_sym_uniq, mul2_f_sym_uniq)
        
        ex_x_u = Symbol(f"ex_x_u_O{Omega_val}",INT); ex_y_u = Symbol(f"ex_y_u_O{Omega_val}",INT)
        q_ex_u = [ex_x_u,ex_y_u]
        diff_add = NotEquals(main_add_func_sym(ex_x_u,ex_y_u), add2_f_sym_uniq(ex_x_u,ex_y_u))
        diff_mul = NotEquals(main_mul_func_sym(ex_x_u,ex_y_u), mul2_f_sym_uniq(ex_x_u,ex_y_u))
        exists_diff = Exists(q_ex_u, And(inS_pred_main(ex_x_u),inS_pred_main(ex_y_u),Or(diff_add,diff_mul)))
        
        if not check_smt(s, And(And(*axioms2_list_formulas_uniq), exists_diff), False, "Uniqueness of ⊕ and ⊗ tables"): 
            all_passed_this_omega=False

        print("\nChecking Inverse-Count Lemma (InvCnt⊕) Property...")
        if Omega_val == 1:
            print("✅ InvCnt⊕ Property: N/A for Ω=1 (No DFI elements).")
        else:
            inv_count_prop_holds_for_all_a = True
            for a_py_val_loop in range(1, Omega_val):
                a_smt_val_loop = Int(a_py_val_loop)
                indicators = []
                for t_py_val_loop in range(1, Omega_val): 
                    t_smt_val_loop = Int(t_py_val_loop)
                    condition = Equals(add_op_main_call(a_smt_val_loop, t_smt_val_loop), U_const_main)
                    indicators.append(Ite(condition, Int(1), Int(0)))
                current_sum_of_indicators = Int(0)
                if indicators: 
                    current_sum_of_indicators = Plus(*indicators) if len(indicators) > 1 else indicators[0]
                count_formula = Equals(current_sum_of_indicators, a_smt_val_loop)
                if not check_smt(s, Not(count_formula), False, f"InvCnt⊕ Property for a={a_py_val_loop}"):
                    inv_count_prop_holds_for_all_a = False; all_passed_this_omega = False
            if inv_count_prop_holds_for_all_a and Omega_val > 1:
                 print(f"✅ InvCnt⊕ Property: Passed for all DFI 'a' in Ω={Omega_val}.")
            elif not inv_count_prop_holds_for_all_a and Omega_val > 1:
                 print(f"❌ InvCnt⊕ Property: Failed for at least one DFI 'a' in Ω={Omega_val}.")
        
        # --- Call Gem 4 & 5 functions ---
        # Pass the correct SMT callables and predicates
        if not run_gem4_tests(Omega_val, s, add_op_main_call, U_const_main, isDFI_pred_main, inS_pred_main): 
            all_passed_this_omega = False
        if not run_gem5_tests(Omega_val, s, add_op_main_call, mul_op_main_call, U_const_main, isDFI_pred_main, inS_pred_main): 
            all_passed_this_omega = False

        s.pop() 
    print(f"\n--- Overall Result for Ω = {Omega_val}: {'PASSED All Checks' if all_passed_this_omega else 'FAILED Some Checks'} ---")
    
    # Run Track 4 (Asymptotic) analysis outside the SMT solver context for this Omega_val
    if Omega_val >= 3: 
        run_track4_asymptotic_analysis(Omega_val) # This uses Python ops, scope is fine
        
    return all_passed_this_omega

# Main driver loop
if __name__ == "__main__":
    MAX_OMEGA_TEST = 3 # For quicker testing initially
    final_results = {}
    print("Starting AVCA Gem Verification Script (V12 - Final Scope Fixes)...")
    for omega_run_val_main in range(1, MAX_OMEGA_TEST + 1):
        passed_main = prove_for_all_gems_v2(omega_run_val_main) 
        final_results[omega_run_val_main] = passed_main
    
    print("\n\n====== FINAL SCRIPT EXECUTION SUMMARY ======")
    all_omegas_passed_overall_main = True
    for omega_val_res_main, status_res_main in final_results.items():
        print(f"Ω = {omega_val_res_main}: {'PASSED ALL CHECKS' if status_res_main else 'FAILED SOME CHECKS'}")
        if not status_res_main:
            all_omegas_passed_overall_main = False

    if all_omegas_passed_overall_main:
        print(f"\nAll gem checks passed for Ω = 1 up to {MAX_OMEGA_TEST}! ✔")
    else:
        print(f"\nSome gem checks FAILED. Please review output for Ω = 1 up to {MAX_OMEGA_TEST}. ❌")