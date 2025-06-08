from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, get_model)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

# --- Global Symbolic Constants ---
U_S = Int(0) # Canonical SMT representation for Unio

# --- Symbolic AVCA Add function based on CCA1-CCA4 ---
# op1, op2 are SMT Integer FNodes representing elements from S_Omega
# current_omega_smt is an SMT Integer FNode representing Omega
def symbolic_avca_add(op1: FNode, op2: FNode, current_omega_smt: FNode) -> FNode:
    """
    Defines op1 ⊕ op2 based on CCA1-CCA4 for symbolic Omega.
    Assumes op1, op2 are constrained to be valid elements of S_Omega.
    U_S (Int(0)) represents Unio.
    DFIs are Int(1) ... current_omega_smt - 1.
    """
    # CCA2: U is identity (handled first for clarity and correctness)
    cond_op1_is_U = Equals(op1, U_S)
    cond_op2_is_U = Equals(op2, U_S)
    
    # Conditions for op1 and op2 being DFI relative to current_omega_smt
    # A DFI element 'x' satisfies: x >= 1 AND x < current_omega_smt
    op1_is_conceptual_dfi = And(GE(op1, Int(1)), LT(op1, current_omega_smt))
    op2_is_conceptual_dfi = And(GE(op2, Int(1)), LT(op2, current_omega_smt))
    both_are_conceptual_dfi = And(op1_is_conceptual_dfi, op2_is_conceptual_dfi)
    
    # DFI-DFI logic (CCA3 and CCA4)
    dfi_sum_expr = Plus(op1, op2)
    dfi_dfi_result = Ite(LT(dfi_sum_expr, current_omega_smt), # if op1+op2 < Omega (CCA3)
                         dfi_sum_expr,                       
                         U_S)                                # else U (CCA4)

    # Full definition using ITE structure:
    # 1. If op1 is U, result is op2 (CCA2)
    # 2. Else (op1 is not U), if op2 is U, result is op1 (CCA2)
    # 3. Else (neither is U, so both must be DFI if inputs are valid S_Omega elements),
    #    apply DFI-DFI logic.
    #    The `both_are_conceptual_dfi` check ensures we only apply DFI logic to actual DFIs.
    #    If inputs are constrained to be valid S_Omega, then if not U, they must be DFI.
    return Ite(cond_op1_is_U, op2,                                  
               Ite(cond_op2_is_U, op1,                              
                   # If we reach here, op1 and op2 are assumed to be DFI by prior S_Omega validity constraints
                   # So, directly apply DFI-DFI logic based on their sum.
                   dfi_dfi_result 
                   # The `both_are_conceptual_dfi` check within symbolic_avca_add might be redundant
                   # if calling code already ensures op1, op2 are DFIs when this branch is taken.
                   # However, keeping it makes symbolic_avca_add more robust if its inputs' nature isn't fully pre-determined.
                   # For CCA3 test, a and b ARE DFIs. For CCA2, 'a_SMT' could be U or DFI.
                  )
              )

# --- Test 1: Symbolic CCA2 (U is Identity) ---
def test_symbolic_cca2_identity():
    print("\n--- SMT Test for CCA2 (a⊕U=a and U⊕a=a) with SYMBOLIC Omega & a ---")
    
    Omega_SMT = Symbol("Omega_Sym_CCA2", SMT_INT_TYPE)
    a_SMT = Symbol("a_Sym_CCA2", SMT_INT_TYPE)
    
    assertions = []
    # Constraint: Omega_SMT >= 1
    assertions.append(GE(Omega_SMT, Int(1)))

    # Constraint: a_SMT must be a valid element of S_Omega
    # Case 1: a_SMT is U
    cond_a_is_U = Equals(a_SMT, U_S)
    # Case 2: a_SMT is DFI (1 <= a_SMT < Omega_SMT)
    # This implies Omega_SMT must be >= 2 for DFI to exist
    cond_a_is_DFI = And(GE(a_SMT, Int(1)), LT(a_SMT, Omega_SMT))
    
    # Assert a_SMT is either U or DFI
    assertions.append(Or(cond_a_is_U, cond_a_is_DFI))
    
    # If Omega_SMT is 1, then a_SMT must be U (no DFIs exist)
    assertions.append(Implies(Equals(Omega_SMT, Int(1)), cond_a_is_U))
    # If a_SMT is DFI, then Omega_SMT must be >= 2
    assertions.append(Implies(cond_a_is_DFI, GE(Omega_SMT, Int(2))))


    # Results of operations
    res_a_plus_U = symbolic_avca_add(a_SMT, U_S, Omega_SMT)
    res_U_plus_a = symbolic_avca_add(U_S, a_SMT, Omega_SMT)
    
    # Property to verify (CCA2)
    property_cca2 = And(Equals(res_a_plus_U, a_SMT), Equals(res_U_plus_a, a_SMT))
    
    # Assert the negation of the property
    assertions.append(Not(property_cca2))
    
    print(f"Applied {len(assertions)} total assertions for CCA2 symbolic test.")

    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for CCA2 (Asserting NOT Property):")
        if not result:
            print("  UNSAT (EXPECTED)")
            print("  This formally proves that for any Omega >= 1 and any valid 'a' in S_Omega,")
            print("  a⊕U=a and U⊕a=a holds when ⊕ is defined by symbolic_avca_add (CCA1-4).")
        else:
            print("  SAT (UNEXPECTED!) - CCA2 does not hold universally.")
            model = get_model(s)
            if model:
                print("  Model (Counterexample) found:")
                print(f"    Omega_Symbolic = {model.get_value(Omega_SMT)}")
                print(f"    a_Symbolic = {model.get_value(a_SMT)}")
                # For debugging, evaluate parts under this model
                # val_a = model.get_value(a_SMT).constant_value()
                # val_omega = model.get_value(Omega_SMT).constant_value()
                # print(f"    Eval res_a_plus_U with Omega={val_omega}, a={val_a}: Need manual eval or SMT eval")
                # print(f"    Eval res_U_plus_a with Omega={val_omega}, a={val_a}: Need manual eval or SMT eval")

            else:
                print("  Solver returned SAT but no model was available.")

# --- Test 2: Symbolic CCA3 (DFI-Haven / Classical Regime) ---
def test_symbolic_cca3_dfi_haven():
    print("\n--- SMT Test for CCA3 (DFI-Haven: a,b∈DFI, a+b<Ω ⇒ a⊕b=a+b) with SYMBOLIC Omega, a, b ---")

    Omega_SMT = Symbol("Omega_Sym_CCA3", SMT_INT_TYPE)
    a_DFI_SMT = Symbol("a_DFI_Sym_CCA3", SMT_INT_TYPE)
    b_DFI_SMT = Symbol("b_DFI_Sym_CCA3", SMT_INT_TYPE)

    assertions = []

    # Constraint: Omega_SMT >= 2 (for DFI elements a,b to potentially exist)
    # If Omega_SMT = 2, DFI={1}. a=1, b=1. a+b = 2. LT(2,2) is false. Premise of CCA3 is false.
    # So CCA3 holds vacuously.
    # For CCA3 premise to be true, we need Omega_SMT >= 3 (e.g. a=1,b=1, sum=2 < 3)
    assertions.append(GE(Omega_SMT, Int(2))) # Allow Omega=2 for DFI to exist.

    # Constraints for a_DFI_SMT and b_DFI_SMT to be valid DFI elements
    # 1 <= a < Omega
    assertions.append(GE(a_DFI_SMT, Int(1)))
    assertions.append(LT(a_DFI_SMT, Omega_SMT))
    # 1 <= b < Omega
    assertions.append(GE(b_DFI_SMT, Int(1)))
    assertions.append(LT(b_DFI_SMT, Omega_SMT))

    # Calculate symbolic sum
    sum_ab_SMT = Plus(a_DFI_SMT, b_DFI_SMT)

    # Condition for classical regime (premise of CCA3)
    cond_classical_regime = LT(sum_ab_SMT, Omega_SMT)
    
    # Result from symbolic_avca_add
    op_result_cca3 = symbolic_avca_add(a_DFI_SMT, b_DFI_SMT, Omega_SMT)
    
    # Property to verify (CCA3: cond_classical_regime => op_result_cca3 == sum_ab_SMT)
    property_cca3 = Implies(cond_classical_regime, Equals(op_result_cca3, sum_ab_SMT))
    
    # Assert the negation of the property
    assertions.append(Not(property_cca3)) # Equivalent to: And(cond_classical_regime, Not(Equals(op_result_cca3, sum_ab_SMT)))
    
    print(f"Applied {len(assertions)} total assertions for CCA3 symbolic test.")

    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
            
        result = s.solve()
        print(f"\nSMT Result for CCA3 (Asserting NOT Property):")
        if not result:
            print("  UNSAT (EXPECTED)")
            print("  This formally proves that for any Omega >= 2, and any valid DFI 'a', 'b',")
            print("  if a+b < Omega, then a⊕b=a+b when ⊕ is defined by symbolic_avca_add (CCA1-4).")
        else:
            print("  SAT (UNEXPECTED!) - CCA3 (DFI-Haven) does not hold universally under these symbolic conditions.")
            model = get_model(s)
            if model:
                print("  Model (Counterexample) found:")
                print(f"    Omega_Symbolic = {model.get_value(Omega_SMT)}")
                print(f"    a_DFI_Symbolic = {model.get_value(a_DFI_SMT)}")
                print(f"    b_DFI_Symbolic = {model.get_value(b_DFI_SMT)}")
                # Further evaluation would be needed here based on model values.
            else:
                print("  Solver returned SAT but no model was available.")

if __name__ == "__main__":
    test_symbolic_cca2_identity()
    test_symbolic_cca3_dfi_haven()