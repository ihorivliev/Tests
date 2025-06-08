from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, get_model, LE)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Global Symbolic Constants ---
U_S = Int(0) # Canonical SMT representation for Unio

# --- Refined Symbolic AVCA Add function based on CCA1-CCA4 ---
def symbolic_avca_add_refined(op1: FNode, op2: FNode, current_omega_smt: FNode) -> FNode:
    """
    Defines op1 ⊕ op2 based on CCA1-CCA4 for symbolic Omega.
    Assumes op1, op2 are constrained by the caller to be valid elements of S_Omega
    (i.e., either U_S or a DFI w.r.t current_omega_smt).
    U_S (Int(0)) represents Unio.
    DFIs are Int(1) ... current_omega_smt - 1.
    """
    cond_op1_is_U = Equals(op1, U_S)
    cond_op2_is_U = Equals(op2, U_S)
    
    # DFI-DFI logic (CCA3 and CCA4)
    # This branch is taken if neither op1 nor op2 is U_S, implying both must be DFIs
    # (given the caller ensures op1, op2 are valid S_Omega elements).
    dfi_sum_expr = Plus(op1, op2) 
    dfi_dfi_result = Ite(LT(dfi_sum_expr, current_omega_smt), # if op1+op2 < Omega (CCA3)
                         dfi_sum_expr,                       
                         U_S)                                # else U (CCA4)

    return Ite(cond_op1_is_U, op2,                    # If op1 is U, result is op2 (CCA2)
               Ite(cond_op2_is_U, op1,                # Else if op2 is U, result is op1 (CCA2)
                   dfi_dfi_result))                  # Else (both must be DFI), apply DFI logic

# --- Helper to constrain a symbolic variable 'x' to be in S_Omega ---
def constrain_to_s_omega(x_smt: FNode, omega_smt: FNode) -> List[FNode]:
    constraints = []
    # x_SMT can be U (0) OR a DFI (an integer k where 1 <= k < Omega_SMT)
    cond_x_is_U = Equals(x_smt, U_S)
    cond_x_is_DFI = And(GE(x_smt, Int(1)), LT(x_smt, omega_smt))
    
    constraints.append(Or(cond_x_is_U, cond_x_is_DFI))
    
    # If Omega_SMT is 1, then x_SMT must be U (no DFIs exist)
    constraints.append(Implies(Equals(omega_smt, Int(1)), cond_x_is_U))
    # If x_SMT is DFI, then Omega_SMT must be >= 2
    constraints.append(Implies(cond_x_is_DFI, GE(omega_smt, Int(2))))
    return constraints

# --- Test 1: Symbolic CCA1 (Totality of symbolic_avca_add_refined output) ---
def test_symbolic_cca1_totality():
    print("\n--- SMT Test for CCA1 (Totality of ⊕ output) with SYMBOLIC Omega, a, b ---")
    
    Omega_SMT = Symbol("Omega_Sym_CCA1", SMT_INT_TYPE)
    a_SMT = Symbol("a_Sym_CCA1", SMT_INT_TYPE)
    b_SMT = Symbol("b_Sym_CCA1", SMT_INT_TYPE)
    
    assertions = []
    assertions.append(GE(Omega_SMT, Int(1)))
    assertions.extend(constrain_to_s_omega(a_SMT, Omega_SMT))
    assertions.extend(constrain_to_s_omega(b_SMT, Omega_SMT))

    res_SMT = symbolic_avca_add_refined(a_SMT, b_SMT, Omega_SMT)
    
    # Property: res_SMT must be in S_Omega
    # Assert negation: res_SMT is NOT in S_Omega
    cond_res_is_U = Equals(res_SMT, U_S)
    cond_res_is_DFI = And(GE(res_SMT, Int(1)), LT(res_SMT, Omega_SMT))
    # Special handling for Omega_SMT = 1, where DFI condition is never met
    res_in_S_Omega = Ite(Equals(Omega_SMT, Int(1)),
                           cond_res_is_U, # If Omega=1, result must be U
                           Or(cond_res_is_U, cond_res_is_DFI)) # If Omega > 1

    assertions.append(Not(res_in_S_Omega))
    
    print(f"Applied {len(assertions)} total assertions for CCA1 symbolic test.")

    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for CCA1 Totality (Asserting NOT Property):")
        if not result:
            print("  UNSAT (EXPECTED)")
            print("  This formally proves that for any Omega >= 1 and any valid 'a', 'b' in S_Omega,")
            print("  the output of symbolic_avca_add_refined(a,b,Omega) is also in S_Omega.")
        else:
            print("  SAT (UNEXPECTED!) - Totality for symbolic_avca_add_refined fails.")
            # Model printing similar to previous scripts if SAT

# --- Test 2: Symbolic CCA4 (DFI Overflow) ---
def test_symbolic_cca4_dfi_overflow():
    print("\n--- SMT Test for CCA4 (DFI Overflow: a,b∈DFI, a+b≥Ω ⇒ a⊕b=U) with SYMBOLIC Omega, a, b ---")

    Omega_SMT = Symbol("Omega_Sym_CCA4", SMT_INT_TYPE)
    a_DFI_SMT = Symbol("a_DFI_Sym_CCA4", SMT_INT_TYPE)
    b_DFI_SMT = Symbol("b_DFI_Sym_CCA4", SMT_INT_TYPE)

    assertions = []
    assertions.append(GE(Omega_SMT, Int(1))) # CCA4 applies for Ω≥1 (though DFI empty if Ω=1)

    # Constraints for a_DFI_SMT and b_DFI_SMT to be valid DFI elements
    # Only add these constraints if Omega_SMT allows for DFIs (i.e. Omega_SMT >= 2)
    # If Omega_SMT = 1, premise of CCA4 (a,b in DFI) is false, so implication is true.
    
    # Premise of CCA4: a,b in DFI AND a+b >= Omega
    # DFI condition: 1 <= val < Omega_SMT
    cond_a_is_DFI_for_CCA4 = And(GE(a_DFI_SMT, Int(1)), LT(a_DFI_SMT, Omega_SMT))
    cond_b_is_DFI_for_CCA4 = And(GE(b_DFI_SMT, Int(1)), LT(b_DFI_SMT, Omega_SMT))
    both_are_DFI_for_CCA4 = And(cond_a_is_DFI_for_CCA4, cond_b_is_DFI_for_CCA4)

    sum_ab_SMT = Plus(a_DFI_SMT, b_DFI_SMT)
    cond_sum_overflows = GE(sum_ab_SMT, Omega_SMT)
    
    premise_CCA4 = And(both_are_DFI_for_CCA4, cond_sum_overflows)
    
    # Result from symbolic_avca_add
    op_result_cca4 = symbolic_avca_add_refined(a_DFI_SMT, b_DFI_SMT, Omega_SMT)
    
    # Property to verify (CCA4: premise_CCA4 => op_result_cca4 == U_S)
    property_cca4 = Implies(premise_CCA4, Equals(op_result_cca4, U_S))
    
    # Assert the negation of the property. 
    # Also need constraints to ensure premise can be true (e.g. Omega >= 2 for DFIs to exist)
    assertions.append(Implies(premise_CCA4, GE(Omega_SMT, Int(1)))) # If premise holds, DFIs must exist, so Omega>=2 generally. Min DFI sum is 1+1=2. So premise implies sum >= Omega.
                                                                # If Omega=1, DFI empty, premise_CCA4 false. Implication true.
                                                                # If Omega=2, DFI={1}. a=1,b=1. sum=2. sum>=Omega (2>=2) true.
                                                                # both_are_DFI true. premise_CCA4 true. Expect 1+1=U.

    assertions.append(Not(property_cca4)) 
    
    print(f"Applied {len(assertions)} total assertions for CCA4 symbolic test.")

    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
            
        result = s.solve()
        print(f"\nSMT Result for CCA4 (Asserting NOT Property):")
        if not result:
            print("  UNSAT (EXPECTED)")
            print("  This formally proves that for any Omega >= 1, and any DFI 'a', 'b' (if they exist),")
            print("  if a+b >= Omega, then a⊕b=U when ⊕ is defined by symbolic_avca_add_refined.")
        else:
            print("  SAT (UNEXPECTED!) - CCA4 (DFI Overflow) does not hold universally.")
            # Model printing

# --- Test 3: Symbolic Emergent Commutativity ---
def test_symbolic_emergent_commutativity():
    print("\n--- SMT Test for Emergent Commutativity with SYMBOLIC Omega, a, b ---")

    Omega_SMT = Symbol("Omega_Sym_Comm", SMT_INT_TYPE)
    a_SMT = Symbol("a_Sym_Comm", SMT_INT_TYPE)
    b_SMT = Symbol("b_Sym_Comm", SMT_INT_TYPE)

    assertions = []
    assertions.append(GE(Omega_SMT, Int(1)))
    assertions.extend(constrain_to_s_omega(a_SMT, Omega_SMT))
    assertions.extend(constrain_to_s_omega(b_SMT, Omega_SMT))

    res_ab = symbolic_avca_add_refined(a_SMT, b_SMT, Omega_SMT)
    res_ba = symbolic_avca_add_refined(b_SMT, a_SMT, Omega_SMT)
    
    # Property: res_ab == res_ba
    # Assert negation: res_ab != res_ba
    assertions.append(Not(Equals(res_ab, res_ba)))
    
    print(f"Applied {len(assertions)} total assertions for Emergent Commutativity symbolic test.")

    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Emergent Commutativity (Asserting NOT Property):")
        if not result:
            print("  UNSAT (EXPECTED)")
            print("  This formally proves that for any Omega >= 1 and any valid 'a', 'b' in S_Omega,")
            print("  a⊕b = b⊕a when ⊕ is defined by symbolic_avca_add_refined (CCA1-4).")
        else:
            print("  SAT (UNEXPECTED!) - Commutativity does not emerge universally.")
            # Model printing

# --- Test 4: Symbolic Associativity for Omega <= 2 ---
def test_symbolic_associativity_omega_le_2():
    print("\n--- SMT Test for Associativity for SYMBOLIC Omega <= 2 ---")

    Omega_SMT = Symbol("Omega_Sym_AssocLe2", SMT_INT_TYPE)
    a_SMT = Symbol("a_Sym_AssocLe2", SMT_INT_TYPE)
    b_SMT = Symbol("b_Sym_AssocLe2", SMT_INT_TYPE)
    c_SMT = Symbol("c_Sym_AssocLe2", SMT_INT_TYPE)

    assertions = []
    # Constraint: 1 <= Omega_SMT <= 2
    assertions.append(GE(Omega_SMT, Int(1)))
    assertions.append(LE(Omega_SMT, Int(2))) # LE for Less Than or Equal

    # Constrain a, b, c to be in S_Omega for this Omega_SMT
    assertions.extend(constrain_to_s_omega(a_SMT, Omega_SMT))
    assertions.extend(constrain_to_s_omega(b_SMT, Omega_SMT))
    assertions.extend(constrain_to_s_omega(c_SMT, Omega_SMT))

    # (a @ b) @ c
    op_ab = symbolic_avca_add_refined(a_SMT, b_SMT, Omega_SMT)
    lhs = symbolic_avca_add_refined(op_ab, c_SMT, Omega_SMT)
    # a @ (b @ c)
    op_bc = symbolic_avca_add_refined(b_SMT, c_SMT, Omega_SMT)
    rhs = symbolic_avca_add_refined(a_SMT, op_bc, Omega_SMT)

    # Property: Associativity Holds (lhs == rhs)
    # Assert negation: lhs != rhs
    assertions.append(Not(Equals(lhs, rhs)))
    
    print(f"Applied {len(assertions)} total assertions for Associativity (Omega<=2) symbolic test.")

    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
            
        result = s.solve()
        print(f"\nSMT Result for Associativity Omega <= 2 (Asserting NOT Property):")
        if not result:
            print("  UNSAT (EXPECTED)")
            print("  This formally proves that for any Omega in {1, 2} and any valid 'a', 'b', 'c' in S_Omega,")
            print("  (a⊕b)⊕c = a⊕(b⊕c) holds when ⊕ is defined by symbolic_avca_add_refined (CCA1-4).")
        else:
            print("  SAT (UNEXPECTED!) - Associativity fails for Omega <= 2.")
            # Model printing

if __name__ == "__main__":
    # Test for CCA2 (Identity) was already successful (from previous script)
    # Test for CCA3 (DFI-Haven) was also successful (from previous script)
    # Test for Non-Associativity for Omega >= 3 was also successful (from previous script)

    # Running new tests:
    test_symbolic_cca1_totality()
    test_symbolic_cca4_dfi_overflow() # New test for symbolic CCA4
    test_symbolic_emergent_commutativity() # New test for symbolic commutativity
    test_symbolic_associativity_omega_le_2() # New test for symbolic associativity for Omega <= 2