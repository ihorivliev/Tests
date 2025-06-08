from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, ForAll, Exists, Solver, 
                             TRUE, FALSE, # Ensured TRUE and FALSE are imported
                             # Function, # Not used for this declaration style as Leq is a symbol
                             get_model)
from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE, FunctionType # Added FunctionType
from pysmt.fnode import FNode 
from typing import List, Dict, Tuple, Callable

# --- Configuration for Ω=3 ---
OMEGA_VAL = 3
U_SMT = Int(0)
DFI1_SMT = Int(1)
DFI2_SMT = Int(2)
S_Omega_elements_smt = [U_SMT, DFI1_SMT, DFI2_SMT]
S_Omega_elements_py = [0, 1, 2] 

# --- Standard AVCA Operations for Omega=3 (U=0, DFI1=1, DFI2=2) ---
avca_add_table_omega3 = {
    (0,0):0, (0,1):1, (0,2):2,
    (1,0):1, (1,1):2, (1,2):0,
    (2,0):2, (2,1):0, (2,2):0
}
avca_mul_table_omega3 = {
    (0,0):0, (0,1):0, (0,2):0,
    (1,0):0, (1,1):1, (1,2):2,
    (2,0):0, (2,1):2, (2,2):0
}

# --- User Defined Partial Order Predicate ---
Leq_predicate_name = "Leq_UserDefined" 
Leq = Symbol(Leq_predicate_name, FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE]))

def get_user_defined_order_assertions() -> List[FNode]:
    """
    ****************************************************************************
    *** USER ACTION REQUIRED: Define your candidate partial order Leq(x,y) below. ***
    ****************************************************************************
    """
    user_assertions = []
    
    # --- EXAMPLE: A simple linear order U < DFI1 < DFI2 ---
    user_assertions.append(Leq(Int(0), Int(0))) 
    user_assertions.append(Leq(Int(1), Int(1))) 
    user_assertions.append(Leq(Int(2), Int(2))) 
    user_assertions.append(Leq(Int(0), Int(1))) 
    user_assertions.append(Leq(Int(0), Int(2))) 
    user_assertions.append(Leq(Int(1), Int(2))) 
    user_assertions.append(Not(Leq(Int(1), Int(0))))
    user_assertions.append(Not(Leq(Int(2), Int(0))))
    user_assertions.append(Not(Leq(Int(2), Int(1))))
    # --- END OF EXAMPLE ---

    print(f"User has provided {len(user_assertions)} assertions for defining Leq(x,y).")
    if not user_assertions:
        print("WARNING: No user assertions for Leq(x,y) provided. Tests will be trivial or fail.")
    return user_assertions

def run_order_theoretic_check():
    print(f"\n--- H-O1: SMT Order-Theoretic Check Framework (Omega={OMEGA_VAL}) ---")
    
    user_order_facts = get_user_defined_order_assertions()
    if not user_order_facts:
        print("  Skipping tests as no candidate order defined by user in get_user_defined_order_assertions().")
        return

    # Use QF_UFLIA for Quantifier-Free Uninterpreted Functions and Linear Integer Arithmetic
    solver_logic = "QF_UFLIA" 

    print("\n  Test 1: Verifying if user-defined Leq is a Partial Order...")

    print("    Testing Reflexivity: Forall x. Leq(x,x)")
    with Solver(name="z3", logic=solver_logic) as s:
        s.add_assertions(user_order_facts)
        reflex_CEX_clauses = [Not(Leq(el, el)) for el in S_Omega_elements_smt] 
        s.add_assertion(Or(reflex_CEX_clauses) if reflex_CEX_clauses else FALSE())
        result_refl = s.solve()
        print(f"      Reflexivity Check (Exists x. NOT Leq(x,x)): {'SAT (Reflexivity FAILS!)' if result_refl else 'UNSAT (Reflexivity Holds - OK)'}")

    print("    Testing Antisymmetry: Forall x,y. (Leq(x,y) & Leq(y,x)) -> x=y")
    with Solver(name="z3", logic=solver_logic) as s:
        s.add_assertions(user_order_facts)
        antisym_CEX_clauses = []
        for x_el_idx in range(len(S_Omega_elements_smt)):
            for y_el_idx in range(x_el_idx + 1, len(S_Omega_elements_smt)): 
                x_el = S_Omega_elements_smt[x_el_idx]
                y_el = S_Omega_elements_smt[y_el_idx]
                antisym_CEX_clauses.append(And(Leq(x_el, y_el), Leq(y_el, x_el)))
        s.add_assertion(Or(antisym_CEX_clauses) if antisym_CEX_clauses else FALSE())
        result_antisym = s.solve()
        print(f"      Antisymmetry Check (Exists x!=y. Leq(x,y)&Leq(y,x)): {'SAT (Antisymmetry FAILS!)' if result_antisym else 'UNSAT (Antisymmetry Holds - OK)'}")

    print("    Testing Transitivity: Forall x,y,z. (Leq(x,y) & Leq(y,z)) -> Leq(x,z)")
    with Solver(name="z3", logic=solver_logic) as s:
        s.add_assertions(user_order_facts)
        trans_CEX_clauses = []
        for x_t in S_Omega_elements_smt:
            for y_t in S_Omega_elements_smt:
                for z_t in S_Omega_elements_smt:
                    trans_CEX_clauses.append(And(Leq(x_t, y_t), Leq(y_t, z_t), Not(Leq(x_t, z_t))))
        s.add_assertion(Or(trans_CEX_clauses) if trans_CEX_clauses else FALSE())
        result_trans = s.solve()
        print(f"      Transitivity Check (Exists x,y,z. Leq(x,y)&Leq(y,z)&NOT Leq(x,z)): {'SAT (Transitivity FAILS!)' if result_trans else 'UNSAT (Transitivity Holds - OK)'}")

    print("\n  Test 2: Checking Monotonicity of AVCA-⊕ for user-defined Leq (Omega=3 instances)...")
    add_is_monotone = True
    mono_add_cex_found = False
    # For monotonicity tests, we need a solver instance that knows the user_order_facts
    with Solver(name="z3", logic=solver_logic) as s_mono_add:
        s_mono_add.add_assertions(user_order_facts)
        for x_py_m in S_Omega_elements_py:
            for a_py_m in S_Omega_elements_py:
                for b_py_m in S_Omega_elements_py:
                    x_smt_m, a_smt_m, b_smt_m = Int(x_py_m), Int(a_py_m), Int(b_py_m)
                    premise_leq_ab = Leq(a_smt_m, b_smt_m) # This is an SMT formula
                    
                    res_xa = Int(avca_add_table_omega3[(x_py_m, a_py_m)])
                    res_xb = Int(avca_add_table_omega3[(x_py_m, b_py_m)])
                    conclusion1_leq_xaxb = Leq(res_xa, res_xb)
                    
                    res_ax = Int(avca_add_table_omega3[(a_py_m, x_py_m)])
                    res_bx = Int(avca_add_table_omega3[(b_py_m, x_py_m)])
                    conclusion2_leq_axbx = Leq(res_ax, res_bx)

                    # Check if (premise_leq_ab is true AND conclusion1_leq_xaxb is false) is SAT
                    s_mono_add.push()
                    s_mono_add.add_assertion(premise_leq_ab) 
                    s_mono_add.add_assertion(Not(conclusion1_leq_xaxb))
                    if s_mono_add.solve():
                        print(f"    ⊕ Monotonicity fails (left op): a={a_py_m}, b={b_py_m}, x={x_py_m}. Leq(a,b) may hold but Not(Leq(x⊕a, x⊕b)) possible.")
                        add_is_monotone = False; mono_add_cex_found = True
                    s_mono_add.pop()
                    if mono_add_cex_found: break 
                    
                    s_mono_add.push()
                    s_mono_add.add_assertion(premise_leq_ab)
                    s_mono_add.add_assertion(Not(conclusion2_leq_axbx))
                    if s_mono_add.solve():
                        print(f"    ⊕ Monotonicity fails (right op): a={a_py_m}, b={b_py_m}, x={x_py_m}. Leq(a,b) may hold but Not(Leq(a⊕x, b⊕x)) possible.")
                        add_is_monotone = False; mono_add_cex_found = True
                    s_mono_add.pop()
                    if mono_add_cex_found: break 
                if mono_add_cex_found: break 
            if mono_add_cex_found: break 
    
    if add_is_monotone: print("    AVCA-⊕ IS Monotone w.r.t. user-defined Leq for Omega=3.")
    else: print("    AVCA-⊕ IS NOT Monotone w.r.t. user-defined Leq for Omega=3.")

    print("\n  Test 3: Checking Monotonicity of AVCA-⊗ for user-defined Leq (Omega=3 instances)...")
    mul_is_monotone = True
    mono_mul_cex_found = False
    with Solver(name="z3", logic=solver_logic) as s_mono_mul:
        s_mono_mul.add_assertions(user_order_facts)
        for x_py_m in S_Omega_elements_py:
            for a_py_m in S_Omega_elements_py:
                for b_py_m in S_Omega_elements_py:
                    x_smt_m, a_smt_m, b_smt_m = Int(x_py_m), Int(a_py_m), Int(b_py_m)
                    premise_leq_ab = Leq(a_smt_m, b_smt_m)
                    res_xa = Int(avca_mul_table_omega3[(x_py_m, a_py_m)])
                    res_xb = Int(avca_mul_table_omega3[(x_py_m, b_py_m)])
                    conclusion1_leq_xaxb = Leq(res_xa, res_xb)
                    res_ax = Int(avca_mul_table_omega3[(a_py_m, x_py_m)])
                    res_bx = Int(avca_mul_table_omega3[(b_py_m, x_py_m)])
                    conclusion2_leq_axbx = Leq(res_ax, res_bx)

                    s_mono_mul.push()
                    s_mono_mul.add_assertion(premise_leq_ab)
                    s_mono_mul.add_assertion(Not(conclusion1_leq_xaxb))
                    if s_mono_mul.solve():
                        print(f"    ⊗ Monotonicity fails (left op): a={a_py_m}, b={b_py_m}, x={x_py_m}. Leq(a,b) may hold but Not(Leq(x⊗a, x⊗b)) possible.")
                        mul_is_monotone = False; mono_mul_cex_found = True
                    s_mono_mul.pop()
                    if mono_mul_cex_found: break

                    s_mono_mul.push()
                    s_mono_mul.add_assertion(premise_leq_ab)
                    s_mono_mul.add_assertion(Not(conclusion2_leq_axbx))
                    if s_mono_mul.solve():
                        print(f"    ⊗ Monotonicity fails (right op): a={a_py_m}, b={b_py_m}, x={x_py_m}. Leq(a,b) may hold but Not(Leq(a⊗x, b⊗x)) possible.")
                        mul_is_monotone = False; mono_mul_cex_found = True
                    s_mono_mul.pop()
                    if mono_mul_cex_found: break
                if mono_mul_cex_found: break
            if mono_mul_cex_found: break
    
    if mul_is_monotone: print("    AVCA-⊗ IS Monotone w.r.t. user-defined Leq for Omega=3.")
    else: print("    AVCA-⊗ IS NOT Monotone w.r.t. user-defined Leq for Omega=3.")

    print("\n  Note: Further tests for join (⊕ as LUB) and meet (⊗ as GLB) properties can be added.")

# --- Main Execution Block ---
if __name__ == "__main__":
    print("Running H-O1 Order-Theoretic Checks. Please ensure you have defined")
    print("your candidate partial order in get_user_defined_order_assertions().")
    print("The example provided is a simple linear order U < DFI1 < DFI2.\n")
    run_order_theoretic_check()

