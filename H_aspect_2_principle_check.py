from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, get_model)
from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE 
from pysmt.fnode import FNode 
from typing import Dict, Tuple, List

# --- Aspect Representations (as SMT Integers) ---
Z_ASPECT_SMT = Int(0)  # Representing ZERO_UNIO aspect
A_ASPECT_SMT = Int(1)  # Representing AREO_UNIO aspect

# --- Aspect Logic Principles ---
# Principle 1: Unio Interaction Logic (MAX/OR)
DFI_EFF_ASPECT_FOR_OR = Z_ASPECT_SMT # DFI acts as Zero for OR logic when it's not a saturation driver

def aspect_OR(asp1: FNode, asp2: FNode) -> FNode:
    """Calculates resulting aspect using MAX/OR (Areo dominates Z, A dominates A)."""
    return Ite(Or(Equals(asp1, A_ASPECT_SMT), Equals(asp2, A_ASPECT_SMT)), 
               A_ASPECT_SMT, 
               Z_ASPECT_SMT)

# Principle 2: DFI Saturation Override (Implicitly returns A_ASPECT_SMT for relevant cases)

# --- Main Test Function ---
def run_two_principle_aspect_model_check(): # Renamed function
    print("--- aspect_two_principle_check.py: SMT Check for Refined Two-Principle Aspect Model ---")
    print("    P1: U-Interactions (U-U, U-DFI where U leads) use MAX/OR (DFI_eff_aspect=Z).")
    print("    P2: DFI-driven Saturation (DFI-DFI Overflows, DFI/ZU) unconditionally yields Areo.")

    assertions = []
    
    asp_u1 = Symbol("asp_u1_2p", SMT_INT_TYPE) # Suffix for two-principle
    asp_u2 = Symbol("asp_u2_2p", SMT_INT_TYPE)
    assertions.append(Or(Equals(asp_u1, Z_ASPECT_SMT), Equals(asp_u1, A_ASPECT_SMT)))
    assertions.append(Or(Equals(asp_u2, Z_ASPECT_SMT), Equals(asp_u2, A_ASPECT_SMT)))

    def add_check(case_name: str, predicted_aspect: FNode, actual_avca_aspect: FNode):
        # print(f"    Checking Case: {case_name}") # Verbose, can be enabled for debug
        assertions.append(Equals(predicted_aspect, actual_avca_aspect))

    # --- 1. Multiplication (avc_mul_v1.2) Unio Results ---
    # M1: U1 @ U2 (Predicted by P1)
    actual_m_u1u2 = Ite(Or(Equals(asp_u1, A_ASPECT_SMT), Equals(asp_u2, A_ASPECT_SMT)), A_ASPECT_SMT, Z_ASPECT_SMT)
    add_check("M1 (U1 @ U2)", aspect_OR(asp_u1, asp_u2), actual_m_u1u2)

    # M2: DFI @ U1 (U1 aspect is asp_u1) (Predicted by P1, DFI_eff_aspect=Z)
    actual_m_dfiu1 = Ite(Equals(asp_u1, A_ASPECT_SMT), A_ASPECT_SMT, Z_ASPECT_SMT)
    add_check("M2 (DFI @ U1)", aspect_OR(DFI_EFF_ASPECT_FOR_OR, asp_u1), actual_m_dfiu1)
    
    # M3: U1 @ DFI (U1 aspect is asp_u1) (Predicted by P1, DFI_eff_aspect=Z)
    actual_m_u1dfi = Ite(Equals(asp_u1, A_ASPECT_SMT), A_ASPECT_SMT, Z_ASPECT_SMT) 
    add_check("M3 (U1 @ DFI)", aspect_OR(asp_u1, DFI_EFF_ASPECT_FOR_OR), actual_m_u1dfi)

    # M4: DFI @ DFI -> Overflow (Predicted by P2)
    add_check("M4 (DFI @ DFI -> Ovfl)", A_ASPECT_SMT, A_ASPECT_SMT)

    # --- 2. Division (avc_div_AltD_Balanced) Unio Results ---
    # D1: U1 / U2 (Dividend asp_u1, Divisor asp_u2) (Predicted by P1, as MAX/OR matches AltD U/U)
    actual_d_u1u2 = Ite(Equals(asp_u2, A_ASPECT_SMT), A_ASPECT_SMT, asp_u1) 
    add_check("D1 (U1 / U2)", aspect_OR(asp_u1, asp_u2), actual_d_u1u2)

    # D2: U1 / DFI (Dividend asp_u1) (Predicted by P1, DFI_eff_aspect=Z)
    actual_d_u1dfi = asp_u1 
    add_check("D2 (U1 / DFI)", aspect_OR(asp_u1, DFI_EFF_ASPECT_FOR_OR), actual_d_u1dfi)
    
    # D3: DFI / U1 (Divisor asp_u1)
    #    Actual AltD DFI/U: Always AREO_UNIO (A_ASPECT_SMT)
    #    Prediction: If U1 is ZU (asp_u1=Z), P2 (DFI Saturation Override for DFI/ZU) -> AREO.
    #                 If U1 is AU (asp_u1=A), P1 -> aspect_OR(DFI_EFF_ASPECT_FOR_OR, A_ASPECT_SMT) = AREO.
    #    So, predicted is always AREO by combining P1 and P2 precedence for DFI/ZU.
    predicted_d_dfiu1 = Ite(Equals(asp_u1, Z_ASPECT_SMT), 
                              A_ASPECT_SMT,  # P2 override for DFI/ZU
                              aspect_OR(DFI_EFF_ASPECT_FOR_OR, asp_u1)) # P1 for DFI/AU -> A_ASPECT_SMT
    add_check("D3 (DFI / U1)", predicted_d_dfiu1, A_ASPECT_SMT)


    # D4: DFI / DFI -> Problematic/Overflow (Predicted by P2)
    add_check("D4 (DFI / DFI -> Ovfl)", A_ASPECT_SMT, A_ASPECT_SMT)

    # --- 3. Addition (avc_add_v1.1) DFI Overflow Aspect ---
    # A1: DFI + DFI -> Overflow (Predicted by P2)
    add_check("A1 (DFI + DFI -> Ovfl)", A_ASPECT_SMT, A_ASPECT_SMT)

    print("\n--- Solving for consistency of the Refined Two-Principle Aspect Model ---")
    with Solver(name="z3") as s: # CORRECTED: Removed log_queries=False
        s.add_assertions(assertions)
        
        final_result = s.solve()
        if final_result:
            print("  OVERALL RESULT: SAT")
            print("  CONCLUSION: The refined two-principle model IS CONSISTENT")
            print("              with ALL specified AVCA Unio aspect outcomes for mul_v1.2, div_AltD, and add_v1.1 DFI overflow.")
            model = s.get_model()
            if model: 
                print(f"    (Example model instance for symbolic aspects: asp_u1 = {model.get_value(asp_u1)}, asp_u2 = {model.get_value(asp_u2)})")
        else:
            print("  OVERALL RESULT: UNSAT")
            print("  CONCLUSION: The refined two-principle aspect model STILL CONFLICTS")
            print("              with at least one of the AVCA Unio aspect outcome rules.")
            print("    (This was UNEXPECTED based on previous analysis.)")
            if s.supports_unsat_cores():
                print("    Attempting to get UNSAT core...")
                try:
                    unsat_core = s.get_unsat_core()
                    if unsat_core:
                        print("    Conflicting assertions (UNSAT core):")
                        for core_item_idx, core_item in enumerate(unsat_core):
                            print(f"      - Core Conflict {core_item_idx+1}: {core_item.serialize()}")
                    else:
                        print("    Solver could not provide an UNSAT core (list was empty).")
                except Exception as e:
                    print(f"    Error getting UNSAT core: {e}")
            else:
                print("    Solver does not support UNSAT cores for direct analysis here.")


if __name__ == "__main__":
    run_two_principle_aspect_model_check()
