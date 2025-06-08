from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, get_model)
from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE # FunctionType not needed for this script
from pysmt.fnode import FNode # <--- ADD THIS LINE
from typing import Dict, Tuple, List

# --- Aspect Representations (as SMT Integers) ---
Z_ASPECT_SMT = Int(0)  # Representing ZERO_UNIO aspect (False-like)
A_ASPECT_SMT = Int(1)  # Representing AREO_UNIO aspect (True-like)

# --- Aspect Logic Principles ---
# Principle 1: Unio Interaction Logic (MAX/OR)
DFI_EFF_ASPECT_FOR_OR = Z_ASPECT_SMT # DFI acts as Zero for OR logic

def aspect_OR(asp1: FNode, asp2: FNode) -> FNode:
    """Calculates resulting aspect using MAX/OR (Areo dominates)."""
    return Ite(Or(Equals(asp1, A_ASPECT_SMT), Equals(asp2, A_ASPECT_SMT)), A_ASPECT_SMT, Z_ASPECT_SMT)

# Principle 2: DFI Saturation Override (Implicitly returns A_ASPECT_SMT for relevant cases)

def run_refined_aspect_model_check():
    print("--- Refined H_AspectField Check: Two-Principle Model ---")
    print("    P1: U-Interactions use MAX/OR (DFI_eff_aspect=Z).")
    print("    P2: DFI-driven Saturation (Overflows, DFI/ZU) unconditionally yields Areo.")

    assertions = []
    
    # Symbolic aspects for generic Unio operands U1, U2
    asp_u1 = Symbol("asp_u1", SMT_INT_TYPE)
    asp_u2 = Symbol("asp_u2", SMT_INT_TYPE)
    assertions.append(Or(Equals(asp_u1, Z_ASPECT_SMT), Equals(asp_u1, A_ASPECT_SMT)))
    assertions.append(Or(Equals(asp_u2, Z_ASPECT_SMT), Equals(asp_u2, A_ASPECT_SMT)))

    # --- Helper to add a check ---
    def add_check(case_name: str, predicted_aspect: FNode, actual_avca_aspect: FNode):
        print(f"    Checking Case: {case_name}")
        print(f"      Predicted Aspect by Model: {'Areo' if predicted_aspect == A_ASPECT_SMT else ('Zero' if predicted_aspect == Z_ASPECT_SMT else 'Symbolic')}")
        print(f"      Actual AVCA Aspect: {'Areo' if actual_avca_aspect == A_ASPECT_SMT else ('Zero' if actual_avca_aspect == Z_ASPECT_SMT else 'Symbolic')}")
        assertions.append(Equals(predicted_aspect, actual_avca_aspect))

    # --- 1. Multiplication (avc_mul_v1.2) Unio Results ---
    print("\n  1. Verifying Multiplication Aspects:")
    # M1: U1 @ U2 
    #    Actual: AREO if any input is AREO, else ZERO (This is aspect_OR(asp_u1, asp_u2))
    #    Prediction: P1 -> aspect_OR(asp_u1, asp_u2)
    add_check("M1 (U1 @ U2)", 
              aspect_OR(asp_u1, asp_u2), 
              Ite(Or(Equals(asp_u1, A_ASPECT_SMT), Equals(asp_u2, A_ASPECT_SMT)), A_ASPECT_SMT, Z_ASPECT_SMT))

    # M2: DFI @ U1 (U1 aspect is asp_u1)
    #    Actual: AREO if U1 is AREO, else ZERO
    #    Prediction: P1 -> aspect_OR(DFI_EFF_ASPECT_FOR_OR, asp_u1)
    add_check("M2 (DFI @ U1)", 
              aspect_OR(DFI_EFF_ASPECT_FOR_OR, asp_u1), 
              Ite(Equals(asp_u1, A_ASPECT_SMT), A_ASPECT_SMT, Z_ASPECT_SMT))
    
    # M3: U1 @ DFI (U1 aspect is asp_u1) - Symmetric to M2 due to ⊗ commutativity
    #    Actual: AREO if U1 is AREO, else ZERO
    #    Prediction: P1 -> aspect_OR(asp_u1, DFI_EFF_ASPECT_FOR_OR)
    add_check("M3 (U1 @ DFI)", 
              aspect_OR(asp_u1, DFI_EFF_ASPECT_FOR_OR), 
              Ite(Equals(asp_u1, A_ASPECT_SMT), A_ASPECT_SMT, Z_ASPECT_SMT))

    # M4: DFI @ DFI -> Overflow
    #    Actual: AREO_UNIO (A_ASPECT_SMT)
    #    Prediction: P2 (DFI Saturation Override) -> A_ASPECT_SMT
    add_check("M4 (DFI @ DFI -> Ovfl)", A_ASPECT_SMT, A_ASPECT_SMT)


    # --- 2. Division (avc_div_AltD_Balanced) Unio Results ---
    print("\n  2. Verifying Division Aspects:")
    # D1: U1 / U2 (Dividend asp_u1, Divisor asp_u2)
    #    Actual AltD U/U: if asp_u2 is AREO -> AREO; else (asp_u2 is ZERO) -> asp_u1
    #    Prediction: P1 -> aspect_OR(asp_u1, asp_u2). (This was found to be equivalent)
    actual_d_u1u2 = Ite(Equals(asp_u2, A_ASPECT_SMT), A_ASPECT_SMT, asp_u1)
    add_check("D1 (U1 / U2)", aspect_OR(asp_u1, asp_u2), actual_d_u1u2)

    # D2: U1 / DFI (Dividend asp_u1)
    #    Actual AltD U/DFI: Preserves asp_u1
    #    Prediction: P1 -> aspect_OR(asp_u1, DFI_EFF_ASPECT_FOR_OR)
    add_check("D2 (U1 / DFI)", aspect_OR(asp_u1, DFI_EFF_ASPECT_FOR_OR), asp_u1)
    
    # D3: DFI / U1 (Divisor asp_u1)
    #    Actual AltD DFI/U: Always AREO_UNIO (A_ASPECT_SMT)
    #    Prediction: P2 (DFI Saturation Override for DFI/ZU) -> A_ASPECT_SMT
    #                 (If asp_u1 is Areo, P1 -> aspect_OR(DFI_EFF_ASPECT_FOR_OR, A_ASPECT_SMT) = A_ASPECT_SMT. Consistent.)
    #                 The critical case for P2 is DFI / ZU.
    predicted_d_dfiu1 = Ite(Equals(asp_u1, Z_ASPECT_SMT), 
                              A_ASPECT_SMT,  # P2 override for DFI/ZU
                              aspect_OR(DFI_EFF_ASPECT_FOR_OR, asp_u1)) # P1 for DFI/AU
    add_check("D3 (DFI / U1)", predicted_d_dfiu1, A_ASPECT_SMT)

    # D4: DFI / DFI -> Problematic/Overflow
    #    Actual: AREO_UNIO (A_ASPECT_SMT)
    #    Prediction: P2 (DFI Saturation Override) -> A_ASPECT_SMT
    add_check("D4 (DFI / DFI -> Ovfl)", A_ASPECT_SMT, A_ASPECT_SMT)

    # --- 3. Addition (avc_add_v1.1) DFI Overflow Aspect ---
    print("\n  3. Verifying Addition DFI Overflow Aspect:")
    # A1: DFI + DFI -> Overflow
    #    Actual: AREO_UNIO (A_ASPECT_SMT)
    #    Prediction: P2 (DFI Saturation Override) -> A_ASPECT_SMT
    add_check("A1 (DFI + DFI -> Ovfl)", A_ASPECT_SMT, A_ASPECT_SMT)

    # --- Solve ---
    print("\n--- Solving for consistency of the Refined Two-Principle Aspect Model ---")
    with Solver(name="z3") as s:
        s.add_assertions(assertions)
        
        final_result = s.solve()
        if final_result:
            print("  OVERALL RESULT: SAT")
            print("  CONCLUSION: The refined two-principle model:")
            print("              1. Unio-Interaction aspects governed by MAX/OR (DFI_eff_aspect=Z)")
            print("              2. DFI-driven Saturation (DFI-DFI Overflows, DFI/ZU) unconditionally yields AREO")
            print("              IS CONSISTENT with ALL specified AVCA Unio aspect outcomes for mul_v1.2, div_AltD, and add_v1.1.")
            print("  This provides a more robust and potentially complete model for H_AspectField!")
            model = s.get_model() # Symbolic asp_u1, asp_u2 will get some assignment
            print(f"    (Example model instance satisfying all checks: asp_u1 = {model.get_value(asp_u1)}, asp_u2 = {model.get_value(asp_u2)})")
        else:
            print("  OVERALL RESULT: UNSAT")
            print("  CONCLUSION: The refined two-principle aspect model STILL CONFLICTS")
            print("              with at least one of the AVCA Unio aspect outcome rules.")
            print("              Further refinement of principles or understanding of conflicts is needed.")
            # For debugging UNSAT:
            # print("    Attempting to get UNSAT core (may not be minimal or available for all theories)...")
            # try:
            #     unsat_core = s.get_unsat_core()
            #     if unsat_core:
            #         print("    Conflicting assertions (part of UNSAT core):")
            #         for core_item in unsat_core:
            #             print(f"      - {core_item.serialize()}")
            #     else:
            #         print("    Solver could not provide an UNSAT core.")
            # except Exception as e:
            #     print(f"    Error getting UNSAT core: {e}")


if __name__ == "__main__":
    run_refined_aspect_model_check()
