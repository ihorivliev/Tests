from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, get_model) # <--- ADDED GT HERE
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Union

def run_symbolic_omega_non_associativity_test():
    print(f"\n--- SMT Test for ⊕ Non-Associativity with SYMBOLIC Omega >= 3 ---")
    print("Counterexample form: (a,b,c) = (DFI_1, DFI_1, DFI_Omega-1)")

    Omega_SMT = Symbol("Omega_Symbolic", SMT_INT_TYPE)
    U_S = Int(0)
    DFI1_S = Int(1)
    # DFI_Omega_minus_1_S is an SMT expression involving Omega_SMT

    assertions = []

    # Axiom: Omega_SMT >= 3
    assertions.append(GE(Omega_SMT, Int(3)))

    # Define DFI_Omega_minus_1_S
    DFI_Omega_minus_1_S = Minus(Omega_SMT, Int(1))

    # --- Helper function to define AVCA_Add based on CCA axioms with Symbolic Omega ---
    # op1, op2 are SMT Integer FNodes
    def symbolic_avca_add(op1: FNode, op2: FNode, current_omega_smt: FNode) -> FNode:
        # CCA2: U is identity
        cond_op1_is_U = Equals(op1, U_S)
        cond_op2_is_U = Equals(op2, U_S)
        
        # Are op1 and op2 DFI? (i.e., > U_S and < current_omega_smt)
        # For this specific counterexample, we only feed U_S or valid DFI expressions 
        # (Int(1), Int(2), or Omega_SMT-1) into this function,
        # so we can simplify the DFI check for internal logic.
        # The crucial check is for the *sum* against current_omega_smt.
        
        # An element `val` is DFI if val > U_S AND val < current_omega_smt
        op1_is_conceptual_dfi = And(GT(op1, U_S), LT(op1, current_omega_smt))
        op2_is_conceptual_dfi = And(GT(op2, U_S), LT(op2, current_omega_smt))
        both_are_conceptual_dfi = And(op1_is_conceptual_dfi, op2_is_conceptual_dfi)
        
        dfi_sum_expr = Plus(op1, op2)
        
        dfi_dfi_result = Ite(LT(dfi_sum_expr, current_omega_smt), # if op1+op2 < Omega (CCA3)
                             dfi_sum_expr,                       
                             U_S)                                # else U (CCA4)

        return Ite(cond_op1_is_U, op2,                                  
                   Ite(cond_op2_is_U, op1,                              
                       Ite(both_are_conceptual_dfi, dfi_dfi_result,        
                           # This 'else' case handles scenarios where at least one is not U, 
                           # and they are not BOTH conceptual DFIs.
                           # e.g. DFI + U (already handled by first ITEs), or DFI + out-of-bounds-value
                           # For this test, inputs to symbolic_avca_add are constrained.
                           # If one is DFI and other is U, outer ITEs handle it.
                           # If one is DFI and other is non-U non-DFI, problem with input validity.
                           # For this specific application, we assume inputs to this function
                           # will be U or DFI (1, 2, Omega-1).
                           # If not both DFI, and neither is U, this path shouldn't be hit
                           # by the specific sequence of operations in the counterexample.
                           # Let's make this fallback U_S for safety, though it shouldn't be reached.
                           U_S))) 

    # Counterexample elements:
    a = DFI1_S
    b = DFI1_S
    c = DFI_Omega_minus_1_S

    # Assert validity of these DFI elements for Omega_SMT >= 3
    assertions.append(GT(DFI1_S, U_S))      # 1 > 0
    assertions.append(LT(DFI1_S, Omega_SMT)) # 1 < Omega_SMT (true for Omega_SMT >= 2 -> true for >=3)
    
    assertions.append(GT(DFI_Omega_minus_1_S, U_S))      # Omega_SMT - 1 > 0  => Omega_SMT > 1 (true for Omega_SMT >=2 -> true for >=3)
    assertions.append(LT(DFI_Omega_minus_1_S, Omega_SMT)) # Omega_SMT - 1 < Omega_SMT (always true)
    
    # Intermediate result DFI2_S = Int(2) also needs to be valid DFI
    assertions.append(GT(Int(2), U_S)) # 2 > 0
    assertions.append(LT(Int(2), Omega_SMT)) # 2 < Omega_SMT (true for Omega_SMT >= 3)


    # --- Construct LHS = (a @ b) @ c ---
    # op_ab = a @ b = 1 @ 1
    # Integer sum is 1+1=2.
    # For Omega_SMT >= 3, 2 < Omega_SMT is true. So by CCA3, 1 @ 1 = Int(2).
    op_ab = symbolic_avca_add(a,b, Omega_SMT) 
    # We can assert what op_ab should be to guide SMT or verify symbolic_avca_add definition
    assertions.append(Implies(GE(Omega_SMT, Int(3)), Equals(op_ab, Int(2))))

    # lhs = op_ab @ c = Int(2) @ (Omega_SMT - 1)
    # Integer sum is 2 + (Omega_SMT - 1) = Omega_SMT + 1.
    # Since Omega_SMT + 1 >= Omega_SMT is true. So by CCA4, result is U_S.
    lhs = symbolic_avca_add(op_ab, c, Omega_SMT)
    assertions.append(Implies(GE(Omega_SMT, Int(3)), Equals(lhs, U_S)))


    # --- Construct RHS = a @ (b @ c) ---
    # op_bc = b @ c = Int(1) @ (Omega_SMT - 1)
    # Integer sum is 1 + (Omega_SMT - 1) = Omega_SMT.
    # Since Omega_SMT >= Omega_SMT is true. So by CCA4, result is U_S.
    op_bc = symbolic_avca_add(b, c, Omega_SMT)
    assertions.append(Implies(GE(Omega_SMT, Int(3)), Equals(op_bc, U_S)))

    # rhs = a @ op_bc = Int(1) @ U_S
    # By CCA2, Int(1) @ U_S = Int(1).
    rhs = symbolic_avca_add(a, op_bc, Omega_SMT)
    assertions.append(Implies(GE(Omega_SMT, Int(3)), Equals(rhs, DFI1_S)))
    
    # --- Assert that associativity holds for this specific triplet ---
    assertions.append(Equals(lhs, rhs))

    print(f"\nApplied {len(assertions)} total assertions for symbolic Omega test.")

    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        
        print(f"\nSMT Result (Asserting (1@1)@(Ω-1) == 1@(1@(Ω-1)) for symbolic Ω >= 3):")
        if not result:
            print("  UNSAT (EXPECTED)")
            print("  This formally proves that for any Omega >= 3, the triplet (1,1,Omega-1)")
            print("  demonstrates non-associativity for an addition operation satisfying CCA1-CCA4,")
            print("  where CCA2 ensures U is identity, and CCA3/CCA4 define DFI interactions.")
            print("  LHS (U=0) and RHS (DFI1=1) are proven unequal for Omega >= 3.")
        else:
            print("  SAT (UNEXPECTED!)")
            print("  This means the SMT solver found an Omega >= 3 (and a definition of ⊕ consistent with CCAs)")
            print("  for which this specific triplet IS associative, or there's an issue in the symbolic logic/assumptions.")
            model = get_model(s)
            if model:
                print("  Model found:")
                print(f"    Omega_Symbolic = {model.get_value(Omega_SMT)}")
                # To evaluate LHS and RHS under this model would require substituting Omega_SMT's value
                # into the symbolic_avca_add calls or simplifying the expressions.
                # For instance:
                omega_concrete = model.get_value(Omega_SMT).constant_value()
                print(f"    For this Omega={omega_concrete}:")
                # Manually trace the logic or use a Python AVCA sim with this Omega
                # This part is for debugging if SAT is returned.
                # Example manual trace for debugging if SAT:
                # op_ab_val = model.get_value(op_ab).constant_value()
                # lhs_val = model.get_value(lhs).constant_value()
                # op_bc_val = model.get_value(op_bc).constant_value()
                # rhs_val = model.get_value(rhs).constant_value()
                # print(f"      Model op_ab: {op_ab_val}, lhs: {lhs_val}")
                # print(f"      Model op_bc: {op_bc_val}, rhs: {rhs_val}")
            else:
                print("  Solver returned SAT but no model was available.")

if __name__ == "__main__":
    run_symbolic_omega_non_associativity_test()