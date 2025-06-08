# ==========================================================
# AVCA_Ω – SMT Proof Script for Gem 1.1 Components (Improved)
# Based on LLM pseudocode blueprint and feedback.
# Using PySMT + Z3
# ==========================================================

from pysmt.shortcuts import (
    Symbol, Int, And, Or, Not, Equals, Ite, Plus, Times, LE, LT, GE,
    FreshSymbol, ForAll, Exists, Solver, is_sat, is_unsat, NotEquals,
    get_model, Portfolio, BOOL, Implies
)
from pysmt.typing import INT, FunctionType, BOOL as SMT_BOOL_TYPE
from typing import List, Dict, Tuple

# --- Global Solver Instance (initialized once) ---
# For more advanced scalability with quantifiers in Z3 via PySMT,
# one might explore options directly if PySMT's Solver object exposes them,
# or use options available when creating the solver if global_solver is defined per Omega run.
# e.g., solver_options={"smt.mbqi": "false", "smt.random_seed": 123}
# For this script, we'll keep it simple.
global_solver = Solver(name="z3") # No specific logic, let Z3 auto-detect

def check_smt(solver: Solver, formula: object, expected_sat: bool, property_name: str, print_model_on_fail: bool = True) -> bool:
    """Helper to check SAT/UNSAT and print results, optionally models on failure."""
    solver.push()
    solver.add_assertion(formula)
    result = solver.solve()
    model_str = ""

    passed_check = (expected_sat and result) or (not expected_sat and not result)

    if not passed_check and print_model_on_fail and result: # Only try to get model if SAT and it's a failure
        try:
            model = solver.get_model()
            # To make model printing useful, one would typically iterate over relevant symbols.
            # For now, a simple indication.
            model_str = f" (Model/Counterexample exists)"
        except Exception as e:
            model_str = f" (Error getting model: {e})"
    solver.pop()

    if passed_check:
        status_emoji = "✅"
        outcome_desc = "SAT as expected" if expected_sat else "UNSAT as expected"
        print(f"{status_emoji} {property_name}: {outcome_desc}.")
        return True
    else:
        status_emoji = "❌"
        outcome_desc = "UNSAT, but expected SAT" if expected_sat else "SAT, but expected UNSAT"
        print(f"{status_emoji} {property_name}: {outcome_desc}.{model_str}")
        return False

def prove_for(Omega_val: int, s: Solver):
    print(f"\n--- Verifying AVCA Properties for Ω = {Omega_val} ---")
    assert Omega_val >= 1

    s.push() # Create a scope for this Omega_val's theory

    Omega_smt_const = Int(Omega_val)
    U = Int(0)

    in_S_Omega = lambda x_var: And(GE(x_var, Int(0)), LT(x_var, Omega_smt_const))

    is_U = lambda z_var: Equals(z_var, U)
    if Omega_val == 1:
        is_DFI = lambda z_var: Equals(Int(0), Int(1)) # Effectively False for SMT
    else:
        is_DFI = lambda z_var: And(GE(z_var, Int(1)), LT(z_var, Omega_smt_const))

    arg_types = [INT, INT]
    op_type = FunctionType(INT, arg_types)
    
    add_func_name = f"avca_add_O{Omega_val}" # Unique names for functions per Omega
    mul_func_name = f"avca_mul_O{Omega_val}"
    add_func  = Symbol(add_func_name, op_type)
    mul_func  = Symbol(mul_func_name, op_type)

    def avca_add(t1: object, t2: object) -> object: return add_func(t1, t2)
    def avca_mul(t1: object, t2: object) -> object: return mul_func(t1, t2)

    x = Symbol("x_q", INT) # Using _q to avoid clashes with potential model vars if printed
    y = Symbol("y_q", INT)
    sum_xy  = Plus(x, y)
    prod_xy = Times(x, y)
    axioms = []
    q_vars = [x,y]

    # Axiom 3.1 Id⊕
    axioms.append(ForAll(q_vars[:1], Implies(in_S_Omega(x), Equals(avca_add(U, x), x))))
    axioms.append(ForAll(q_vars[:1], Implies(in_S_Omega(x), Equals(avca_add(x, U), x))))
    # Axiom 3.2 Cls⊕
    condition_cls_add = And(is_DFI(x), is_DFI(y), LT(sum_xy, Omega_smt_const))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_cls_add),
                                       Equals(avca_add(x, y), sum_xy))))
    # Axiom 3.3 Ovfl⊕
    condition_ovfl_add = And(is_DFI(x), is_DFI(y), GE(sum_xy, Omega_smt_const))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_ovfl_add),
                                        Equals(avca_add(x, y), U))))
    # Axiom 3.4 Ann⊗
    axioms.append(ForAll(q_vars[:1], Implies(in_S_Omega(x), Equals(avca_mul(U, x), U))))
    axioms.append(ForAll(q_vars[:1], Implies(in_S_Omega(x), Equals(avca_mul(x, U), U))))
    # Axiom 3.5 Cls⊗
    condition_cls_mul = And(is_DFI(x), is_DFI(y), GE(prod_xy, Int(1)), LT(prod_xy, Omega_smt_const))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_cls_mul),
                                       Equals(avca_mul(x, y), prod_xy))))
    # Axiom 3.6 Ovfl⊗
    condition_ovfl_mul = And(is_DFI(x), is_DFI(y), GE(prod_xy, Omega_smt_const))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_ovfl_mul),
                                        Equals(avca_mul(x, y), U))))
    
    # REMOVED: Explicit Output Range Totality Axioms for add_func, mul_func
    # These are now expected to be emergent from the 6 operational axioms above,
    # as they define the result for all input cases within S_Omega to be within S_Omega.
    # axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)), in_S_Omega(add_func(x,y)))))
    # axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)), in_S_Omega(mul_func(x,y)))))

    theory = And(*axioms)
    s.add_assertion(theory)
    all_passed = True

    # --- Start of property checks ---
    # For proving a universal property P: check_smt(s, Not(P), False, "Property P")
    # For showing a property P can be false (existential counterexample): check_smt(s, Not(P), True, "Property P can fail")

    print("\nChecking Commutativity...")
    prop_comm_add = ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)),
                                         Equals(avca_add(x, y), avca_add(y, x))))
    if not check_smt(s, Not(prop_comm_add), False, "Commutativity of ⊕"): all_passed = False

    prop_comm_mul = ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)),
                                         Equals(avca_mul(x, y), avca_mul(y, x))))
    if not check_smt(s, Not(prop_comm_mul), False, "Commutativity of ⊗"): all_passed = False

    print("\nChecking Associativity of ⊗...")
    z = Symbol("z_q", INT)
    q_vars_3 = [x,y,z]
    prop_assoc_mul = ForAll(q_vars_3, Implies(And(in_S_Omega(x), in_S_Omega(y), in_S_Omega(z)),
                                            Equals(avca_mul(avca_mul(x, y), z),
                                                   avca_mul(x, avca_mul(y, z)))))
    if not check_smt(s, Not(prop_assoc_mul), False, "Associativity of ⊗"): all_passed = False

    print("\nChecking Phase Transition of ⊕-Associativity...")
    prop_assoc_add = ForAll(q_vars_3, Implies(And(in_S_Omega(x), in_S_Omega(y), in_S_Omega(z)),
                                            Equals(avca_add(avca_add(x, y), z),
                                                   avca_add(x, avca_add(y, z)))))
    if Omega_val <= 2:
        if not check_smt(s, Not(prop_assoc_add), False, f"⊕-Associativity (Ω={Omega_val} ≤ 2)"): all_passed = False
    else: 
        if not check_smt(s, Not(prop_assoc_add), True, f"⊕-Non-Associativity (Ω={Omega_val} ≥ 3)"): all_passed = False
        if Omega_val >= 3: 
            one = Int(1)
            # Ensure Omega_val-1 is a valid DFI if Omega_val=1 or 2 is not the case
            # For Omega_val=3, Omega_val-1 = 2 (DFI).
            # For Omega_val=2, Omega_val-1 = 1 (DFI). Test isn't run here.
            # For Omega_val=1, Omega_val-1 = 0 (U). Test isn't run here.
            if Omega_val > 1 : # Ensure omega_minus_1 is potentially meaningful
                omega_minus_1_val = Omega_val - 1
                if omega_minus_1_val >= 1: # Is DFI
                    omega_minus_1 = Int(omega_minus_1_val)
                    # Check if 'one' and 'omega_minus_1' are valid for current Omega_val
                    # This is implicitly handled by how avca_add will behave if given out-of-DFI-range values
                    # but it's better to ensure the constants are meaningful.
                    # The `add` function doesn't use is_DFI, but applies rules based on value ranges.
                    lhs_cex = avca_add(avca_add(one, one), omega_minus_1)
                    rhs_cex = avca_add(one, avca_add(one, omega_minus_1))
                    cex_formula = NotEquals(lhs_cex, rhs_cex)
                    if not check_smt(s, cex_formula, True, f"⊕-Non-Associativity Counterexample (1,1,Ω-1) for Ω={Omega_val}"): all_passed = False
                # else for Omega_val=1 or 2, this counterexample isn't the one, handled by prop_assoc_add check.
            # else for Omega_val=1, no DFI 'one'.

    print("\nChecking Global Distributivity (⊗ over ⊕)...")
    prop_distrib = ForAll(q_vars_3, Implies(And(in_S_Omega(x), in_S_Omega(y), in_S_Omega(z)),
                                         Equals(avca_mul(x, avca_add(y, z)),
                                                avca_add(avca_mul(x, y), avca_mul(x, z)))))
    if Omega_val >= 3:
        if not check_smt(s, Not(prop_distrib), True, f"Non-Distributivity (Ω={Omega_val} ≥ 3)"): all_passed = False
    else: 
        if not check_smt(s, Not(prop_distrib), False, f"Distributivity (Ω={Omega_val} ≤ 2)"): all_passed = False

    print("\nChecking Uniqueness of Tables...")
    add2_func = Symbol(f"avca_add2_O{Omega_val}", op_type) 
    mul2_func = Symbol(f"avca_mul2_O{Omega_val}", op_type)

    def avca_add2(t1: object, t2: object) -> object: return add2_func(t1, t2)
    def avca_mul2(t1: object, t2: object) -> object: return mul2_func(t1, t2)
    
    axioms2 = []
    axioms2.append(ForAll(q_vars[:1], Implies(in_S_Omega(x), Equals(avca_add2(U, x), x))))
    axioms2.append(ForAll(q_vars[:1], Implies(in_S_Omega(x), Equals(avca_add2(x, U), x))))
    condition_cls_add2 = And(is_DFI(x), is_DFI(y), LT(sum_xy, Omega_smt_const))
    axioms2.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_cls_add2),
                                       Equals(avca_add2(x, y), sum_xy))))
    condition_ovfl_add2 = And(is_DFI(x), is_DFI(y), GE(sum_xy, Omega_smt_const))
    axioms2.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_ovfl_add2),
                                        Equals(avca_add2(x, y), U))))
    axioms2.append(ForAll(q_vars[:1], Implies(in_S_Omega(x), Equals(avca_mul2(U, x), U))))
    axioms2.append(ForAll(q_vars[:1], Implies(in_S_Omega(x), Equals(avca_mul2(x, U), U))))
    condition_cls_mul2 = And(is_DFI(x), is_DFI(y), GE(prod_xy, Int(1)), LT(prod_xy, Omega_smt_const))
    axioms2.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_cls_mul2),
                                       Equals(avca_mul2(x, y), prod_xy))))
    condition_ovfl_mul2 = And(is_DFI(x), is_DFI(y), GE(prod_xy, Omega_smt_const))
    axioms2.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_ovfl_mul2),
                                        Equals(avca_mul2(x, y), U))))
    
    # REMOVED: Explicit range totality for add2_func, mul2_func as they should also be emergent
    # axioms2.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)), in_S_Omega(add2_func(x,y)))))
    # axioms2.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)), in_S_Omega(mul2_func(x,y)))))

    ex_x_uniq = Symbol("ex_x_uniq", INT) 
    ex_y_uniq = Symbol("ex_y_uniq", INT)
    q_vars_ex_uniq = [ex_x_uniq, ex_y_uniq]
    
    diff_add_u = NotEquals(add_func(ex_x_uniq, ex_y_uniq), add2_func(ex_x_uniq, ex_y_uniq)) 
    diff_mul_u = NotEquals(mul_func(ex_x_uniq, ex_y_uniq), mul2_func(ex_x_uniq, ex_y_uniq)) 
    
    exists_diff_formula = Exists(q_vars_ex_uniq, And(
        in_S_Omega(ex_x_uniq), 
        in_S_Omega(ex_y_uniq), 
        Or(diff_add_u, diff_mul_u)
    ))
    
    # Check if (axioms_for_op1_already_on_s AND axioms_for_op2 AND exists_diff_formula) is UNSAT
    if not check_smt(s, And(And(*axioms2), exists_diff_formula), False, "Uniqueness of ⊕ and ⊗ tables (checking if a different one exists)"): 
        all_passed = False

    print("\nChecking Inverse-Count Lemma (InvCnt⊕)...")
    if Omega_val == 1:
        print("✅ InvCnt⊕: N/A for Ω=1 (No DFI elements).")
    else:
        inv_count_holds_for_all_a = True
        for a_py_val in range(1, Omega_val): # Iterate DFI 'a'
            a_smt_val = Int(a_py_val)
            indicators = []
            # Iterate DFI 't'
            for t_py_val in range(1, Omega_val): 
                t_smt_val = Int(t_py_val)
                condition = Equals(avca_add(a_smt_val, t_smt_val), U)
                indicators.append(Ite(condition, Int(1), Int(0)))
            
            current_sum_of_indicators = Int(0)
            if indicators: # This list will not be empty if Omega_val > 1
                current_sum_of_indicators = Plus(*indicators) if len(indicators) > 1 else indicators[0]
            
            count_formula = Equals(current_sum_of_indicators, a_smt_val)
            if not check_smt(s, Not(count_formula), False, f"InvCnt⊕ for a={a_py_val}"):
                inv_count_holds_for_all_a = False
                all_passed = False
        
        if inv_count_holds_for_all_a and Omega_val > 1: # Check Omega_val > 1 for meaningful pass message
             print(f"✅ InvCnt⊕: Passed for all DFI 'a' in Ω={Omega_val}.")
        elif not inv_count_holds_for_all_a and Omega_val > 1: # Ensure this prints only if actually failed
             print(f"❌ InvCnt⊕: Failed for at least one DFI 'a' in Ω={Omega_val}.")

    s.pop() 

    print(f"\n--- Overall Result for Ω = {Omega_val}: {'PASSED All Checks' if all_passed else 'FAILED Some Checks'} ---")
    return all_passed

# Main driver loop
if __name__ == "__main__":
    MAX_OMEGA_TEST = 3 
    final_results = {}
    for omega_run_val in range(1, MAX_OMEGA_TEST + 1):
        passed = prove_for(omega_run_val, global_solver) 
        final_results[omega_run_val] = passed
    
    print("\n\n====== SCRIPT EXECUTION SUMMARY ======")
    all_omegas_passed_overall = True
    for omega_val_res, status_res in final_results.items():
        print(f"Ω = {omega_val_res}: {'PASSED' if status_res else 'FAILED'}")
        if not status_res:
            all_omegas_passed_overall = False

    if all_omegas_passed_overall:
        print(f"\nAll checks passed for Ω = 1 up to {MAX_OMEGA_TEST}! ✔")
    else:
        print(f"\nSome checks FAILED. Please review output for Ω values up to {MAX_OMEGA_TEST}. ❌")