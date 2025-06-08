# Based on the SCRIPT YOU PROVIDED as "inspiration"
# Minimal correction for the 'FALSE' issue.

from pysmt.shortcuts import (
    Symbol, Int, And, Or, Not, Equals, Ite, Plus, Times, LE, LT, GE, GT, # Added GT
    FreshSymbol, ForAll, Exists, Solver, is_sat, is_unsat, NotEquals,
    Function, Implies, # Added Implies from your script
    TRUE, FALSE # Ensure TRUE and FALSE are imported
)
from pysmt.typing import INT, FunctionType, BOOL as SMT_BOOL_TYPE # SMT_BOOL_TYPE if needed
from typing import List, Dict, Tuple

# --- Global Solver Instance (initialized once) ---
# As per your provided script, though for sequential Omega testing,
# ensuring a clean state per Omega (e.g., by re-creating solver or full reset)
# might be more robust if UFs are named without Omega_val.
# However, your script names UFs with Omega_val, and uses push/pop which is good.
global_solver = Solver(name="z3")

def check_smt(solver: Solver, formula: object, expected_sat: bool, property_name: str) -> bool:
    """Helper to check SAT/UNSAT and print results (from your script)."""
    solver.push()
    solver.add_assertion(formula)
    result = solver.solve()
    model_str = ""
    # (Optional model printing logic from your script can be re-inserted here if desired)
    solver.pop()

    if expected_sat:
        if result:
            print(f"    ✅ {property_name}: SAT as expected.{model_str}")
            return True
        else:
            print(f"    ❌ {property_name}: UNSAT, but expected SAT.{model_str}")
            return False
    else: # Expected UNSAT
        if not result:
            print(f"    ✅ {property_name}: UNSAT as expected.{model_str}")
            return True
        else:
            print(f"    ❌ {property_name}: SAT, but expected UNSAT.{model_str}")
            return False

def prove_for(Omega_val: int, s: Solver): # Takes solver 's' as argument
    print(f"\n--- Verifying AVCA Properties for Ω = {Omega_val} ---")
    assert Omega_val >= 1

    s.push() # Manage context for this Omega_val

    Omega_smt_const = Int(Omega_val)
    U = Int(0)

    in_S_Omega = lambda x_var: And(GE(x_var, Int(0)), LT(x_var, Omega_smt_const))

    is_U_lambda = lambda z_var: Equals(z_var, U) # Renamed to avoid conflict if is_U is a global
    
    # CORRECTED is_DFI using PySMT's FALSE()
    if Omega_val == 1:
        is_DFI_lambda = lambda z_var: FALSE() # Use PySMT's FALSE()
    else:
        is_DFI_lambda = lambda z_var: And(GE(z_var, Int(1)), LT(z_var, Omega_smt_const)) # Omega_val-1 done by LT

    arg_types = [INT, INT]
    op_type = FunctionType(INT, arg_types)
    
    add_func_name = f"avca_add_O{Omega_val}" # Unique names per Omega
    mul_func_name = f"avca_mul_O{Omega_val}"
    add_func  = Symbol(add_func_name, op_type)
    mul_func  = Symbol(mul_func_name, op_type)

    # Lambdas for applying the SMT Function symbols
    # These must match how they are used in axiom definitions.
    # The blueprint used avca_add and avca_mul.
    # Using apply_ to avoid confusion with Python's 'add'.
    apply_avca_add = lambda t1, t2: Function(add_func, (t1, t2))
    apply_avca_mul = lambda t1, t2: Function(mul_func, (t1, t2))

    x = Symbol("x", INT) # For ForAll, PySMT makes them bound
    y = Symbol("y", INT)
    sum_xy  = Plus(x, y)
    prod_xy = Times(x, y)
    axioms = []
    q_vars = [x,y] # For 2-var quantifiers

    # Axioms using the lambdas for function application
    # A1. Totality (Output Range Constraint for UFs)
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)), in_S_Omega(apply_avca_add(x,y)))))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)), in_S_Omega(apply_avca_mul(x,y)))))

    # A3. Id_⊕
    axioms.append(ForAll([x], Implies(in_S_Omega(x), Equals(apply_avca_add(U, x), x))))
    axioms.append(ForAll([x], Implies(in_S_Omega(x), Equals(apply_avca_add(x, U), x))))

    # A4. Cls_⊕
    condition_cls_add = And(is_DFI_lambda(x), is_DFI_lambda(y), LT(sum_xy, Omega_smt_const))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_cls_add),
                                        Equals(apply_avca_add(x, y), sum_xy))))
    # A5. Ovfl_⊕
    condition_ovfl_add = And(is_DFI_lambda(x), is_DFI_lambda(y), GE(sum_xy, Omega_smt_const))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_ovfl_add),
                                        Equals(apply_avca_add(x, y), U))))
    # Ann_⊗
    axioms.append(ForAll([x], Implies(in_S_Omega(x), Equals(apply_avca_mul(U, x), U))))
    axioms.append(ForAll([x], Implies(in_S_Omega(x), Equals(apply_avca_mul(x, U), U))))

    # Cls_⊗
    condition_cls_mul = FALSE()
    if Omega_val > 1:
        condition_cls_mul = And(is_DFI_lambda(x), is_DFI_lambda(y), GE(prod_xy, Int(1)), LT(prod_xy, Omega_smt_const))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_cls_mul),
                                        Equals(apply_avca_mul(x, y), prod_xy))))
    # Ovfl_⊗
    condition_ovfl_mul = FALSE()
    if Omega_val > 1:
        condition_ovfl_mul = And(is_DFI_lambda(x), is_DFI_lambda(y), GE(prod_xy, Omega_smt_const))
    axioms.append(ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y), condition_ovfl_mul),
                                        Equals(apply_avca_mul(x, y), U))))

    theory = And(*axioms) # Use unpacking for list of axioms
    s.add_assertion(theory)
    all_passed_this_omega = True
    print("  Axioms encoded and asserted for this Omega.")

    # --- Commutativity ---
    print("\n  Checking Commutativity...")
    prop_comm_add = ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)),
                                         Equals(apply_avca_add(x, y), apply_avca_add(y, x))))
    if not check_smt(s, Not(prop_comm_add), False, "Commutativity of ⊕"): all_passed_this_omega = False

    prop_comm_mul = ForAll(q_vars, Implies(And(in_S_Omega(x), in_S_Omega(y)),
                                         Equals(apply_avca_mul(x, y), apply_avca_mul(y, x))))
    if not check_smt(s, Not(prop_comm_mul), False, "Commutativity of ⊗"): all_passed_this_omega = False

    # --- Associativity of ⊗ ---
    print("\n  Checking Associativity of ⊗...")
    z = Symbol("z", INT) # Bound variable for 3-var quantifiers
    q_vars_3 = [x,y,z]
    prop_assoc_mul = ForAll(q_vars_3, Implies(And(in_S_Omega(x), in_S_Omega(y), in_S_Omega(z)),
                                           Equals(apply_avca_mul(apply_avca_mul(x, y), z),
                                                  apply_avca_mul(x, apply_avca_mul(y, z)))))
    if not check_smt(s, Not(prop_assoc_mul), False, "Associativity of ⊗"): all_passed_this_omega = False

    # --- Phase Transition of ⊕-Associativity ---
    print("\n  Checking Phase Transition of ⊕-Associativity...")
    prop_assoc_add = ForAll(q_vars_3, Implies(And(in_S_Omega(x), in_S_Omega(y), in_S_Omega(z)),
                                           Equals(apply_avca_add(apply_avca_add(x, y), z),
                                                  apply_avca_add(x, apply_avca_add(y, z)))))
    if Omega_val <= 2:
        if not check_smt(s, Not(prop_assoc_add), False, f"⊕-Associativity (Ω={Omega_val} ≤ 2)"): all_passed_this_omega = False
    else: # Omega_val >= 3, expect non-associativity (i.e., Not(prop_assoc_add) is SAT)
        if not check_smt(s, Not(prop_assoc_add), True, f"⊕-Non-Associativity (Ω={Omega_val} ≥ 3)"): all_passed_this_omega = False
        if Omega_val >= 3: # Check specific counterexample (1,1,Omega-1)
            one = Int(1)
            omega_minus_1_val = Omega_val - 1
            if omega_minus_1_val >= 1: # Ensure Omega-1 is a valid DFI
                omega_minus_1 = Int(omega_minus_1_val)
                lhs_cex = apply_avca_add(apply_avca_add(one, one), omega_minus_1)
                rhs_cex = apply_avca_add(one, apply_avca_add(one, omega_minus_1))
                cex_formula = NotEquals(lhs_cex, rhs_cex)
                # We expect this specific counterexample to be true (SAT) given the theory
                if not check_smt(s, cex_formula, True, f"⊕-Non-Associativity Counterexample (1,1,Ω-1) for Ω={Omega_val}",):
                    all_passed_this_omega = False
            else:
                 print(f"      Skipping specific counterexample check for Ω={Omega_val} as Ω-1 is not a valid DFI for this formula.")


    # (Skipping Distributivity, Uniqueness, InvCnt for brevity based on previous focus)
    # ... these would follow the same pattern as in your provided script ...

    s.pop() # Pop context for this Omega_val
    print(f"\n--- Overall Result for Ω = {Omega_val}: {'PASSED All Performed Checks' if all_passed_this_omega else 'FAILED Some Performed Checks'} ---")
    return all_passed_this_omega

if __name__ == "__main__":
    MAX_OMEGA_TEST = 4 # As per your last output
    final_results = {}
    for omega_run_val in range(1, MAX_OMEGA_TEST + 1):
        passed = prove_for(omega_run_val, global_solver) # Pass the global_solver
        final_results[omega_run_val] = passed
    
    print("\n\n====== SCRIPT EXECUTION SUMMARY ======")
    all_omegas_passed_overall = True
    for omega_val_res, status_res in final_results.items():
        print(f"Ω = {omega_val_res}: {'PASSED' if status_res else 'FAILED'}")
        if not status_res:
            all_omegas_passed_overall = False

    if all_omegas_passed_overall:
        print(f"\nAll performed checks passed for Ω = 1 up to {MAX_OMEGA_TEST}! ✔")
    else:
        print(f"\nSome performed checks FAILED. Please review output for Ω values up to {MAX_OMEGA_TEST}. ❌")