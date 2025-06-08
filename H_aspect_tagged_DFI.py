from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Ite, Minus, LT, GE, GT, get_model)
from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Dict, Tuple, List

# --- Aspect Representations (as SMT Integers) ---
Z_ASPECT_SMT = Int(0)  # Representing ZERO_UNIO aspect
A_ASPECT_SMT = Int(1)  # Representing AREO_UNIO aspect

# --- Core Aspect Operation: MAX/OR ---
def aspect_OR(eff_asp1: FNode, eff_asp2: FNode) -> FNode:
    """Calculates resulting aspect using MAX/OR (Areo dominates Z, A dominates A)."""
    return Ite(Or(Equals(eff_asp1, A_ASPECT_SMT), Equals(eff_asp2, A_ASPECT_SMT)), 
               A_ASPECT_SMT, 
               Z_ASPECT_SMT)

# --- Main Test Function ---
def run_tagged_dfi_aspect_model_check():
    print("--- aspect_tagged_dfi_check.py: SMT Check for Unified Aspect Model with Tagged DFIs ---")
    print("    Hypothesis: A single MAX/OR aspect op works if DFIs get an 'Areo tag'")
    print("    when involved in DFI-driven saturation events, otherwise they are 'Zero-tagged'.")

    assertions = []
    
    # Symbolic aspects for generic Unio operands U1, U2
    asp_u1 = Symbol("asp_u1_td", SMT_INT_TYPE) 
    asp_u2 = Symbol("asp_u2_td", SMT_INT_TYPE)
    assertions.append(Or(Equals(asp_u1, Z_ASPECT_SMT), Equals(asp_u1, A_ASPECT_SMT)))
    assertions.append(Or(Equals(asp_u2, Z_ASPECT_SMT), Equals(asp_u2, A_ASPECT_SMT)))

    # Default effective aspect for DFI when it's NOT a saturation-driver
    DFI_AS_ZERO_TAG = Z_ASPECT_SMT
    # Effective aspect for DFI when IT IS a saturation-driver (gets "Areo-tagged")
    DFI_AS_AREO_TAG = A_ASPECT_SMT

    # --- Helper to add a check ---
    def add_check(case_name: str, 
                  eff_asp_op1: FNode, # Effective aspect of operand 1 for OR
                  eff_asp_op2: FNode, # Effective aspect of operand 2 for OR
                  actual_avca_aspect: FNode, # The true aspect AVCA rule produces
                  is_final_check: bool = False): # Flag for the final combined check
        
        predicted_aspect = aspect_OR(eff_asp_op1, eff_asp_op2)
        constraint = Equals(predicted_aspect, actual_avca_aspect)
        
        if not is_final_check: # Add individual constraints for debugging/logging
            print(f"    Constraint for {case_name}: Pred({eff_asp_op1.serialize() if not eff_asp_op1.is_constant() else eff_asp_op1.constant_value()},{eff_asp_op2.serialize() if not eff_asp_op2.is_constant() else eff_asp_op2.constant_value()}) == Actual({actual_avca_aspect.serialize() if not actual_avca_aspect.is_constant() else actual_avca_aspect.constant_value()})")
        assertions.append(constraint)


    # --- 1. Multiplication (avc_mul_v1.2) Unio Results ---
    print("\n  1. Defining Multiplication Aspect Constraints for Tagged-DFI model:")
    # M1: U1 @ U2 
    #    Effective aspects: asp_u1, asp_u2
    #    Actual AVCA rule: AREO if any input asp_u1 or asp_u2 is AREO, else ZERO.
    actual_m_u1u2 = Ite(Or(Equals(asp_u1, A_ASPECT_SMT), Equals(asp_u2, A_ASPECT_SMT)), A_ASPECT_SMT, Z_ASPECT_SMT)
    add_check("M1 (U1 @ U2)", asp_u1, asp_u2, actual_m_u1u2)

    # M2: DFI @ U1 (U1 aspect is asp_u1)
    #    DFI is a non-saturating input here, so its effective aspect is DFI_AS_ZERO_TAG.
    #    Actual AVCA rule: AREO if asp_u1 is AREO, else ZERO.
    actual_m_dfiu1 = Ite(Equals(asp_u1, A_ASPECT_SMT), A_ASPECT_SMT, Z_ASPECT_SMT)
    add_check("M2 (DFI @ U1)", DFI_AS_ZERO_TAG, asp_u1, actual_m_dfiu1)
    
    # M3: U1 @ DFI (U1 aspect is asp_u1) - Symmetric to M2
    #    DFI is non-saturating input. Effective DFI_asp = DFI_AS_ZERO_TAG.
    #    Actual AVCA rule: AREO if asp_u1 is AREO, else ZERO.
    actual_m_u1dfi = Ite(Equals(asp_u1, A_ASPECT_SMT), A_ASPECT_SMT, Z_ASPECT_SMT)
    add_check("M3 (U1 @ DFI)", asp_u1, DFI_AS_ZERO_TAG, actual_m_u1dfi)

    # M4: DFI @ DFI -> Overflow. THIS IS A DFI-DRIVEN SATURATION EVENT.
    #    Effective aspects for both DFIs become DFI_AS_AREO_TAG.
    #    Actual AVCA rule: Always AREO_UNIO (A_ASPECT_SMT).
    add_check("M4 (DFI @ DFI -> Ovfl)", DFI_AS_AREO_TAG, DFI_AS_AREO_TAG, A_ASPECT_SMT)

    # --- 2. Division (avc_div_AltD_Balanced) Unio Results ---
    print("\n  2. Defining Division Aspect Constraints for Tagged-DFI model:")
    # D1: U1 / U2 (Dividend asp_u1, Divisor asp_u2)
    #    Effective aspects: asp_u1, asp_u2.
    #    Actual AltD U/U rule: if asp_u2 is AREO -> AREO; else (asp_u2 is ZERO) -> asp_u1.
    #    This was previously shown to be equivalent to aspect_OR(asp_u1, asp_u2).
    actual_d_u1u2 = Ite(Equals(asp_u2, A_ASPECT_SMT), A_ASPECT_SMT, asp_u1) 
    add_check("D1 (U1 / U2)", asp_u1, asp_u2, actual_d_u1u2)

    # D2: U1 / DFI (Dividend asp_u1)
    #    DFI is non-saturating input. Effective DFI_asp = DFI_AS_ZERO_TAG. U1_asp = asp_u1.
    #    Actual AltD U/DFI rule: Preserves dividend aspect (asp_u1).
    add_check("D2 (U1 / DFI)", asp_u1, DFI_AS_ZERO_TAG, asp_u1)
    
    # D3: DFI / U1 (Divisor asp_u1)
    #    Actual AltD DFI/U rule: Always AREO_UNIO (A_ASPECT_SMT).
    #    Effective DFI_asp for OR: Tagged as AREO if U1 is ZU (DFI/ZU is saturation event), else tagged as ZERO.
    eff_dfi_asp_for_d3 = Ite(Equals(asp_u1, Z_ASPECT_SMT), DFI_AS_AREO_TAG, DFI_AS_ZERO_TAG)
    eff_u1_asp_for_d3 = asp_u1 # U1's aspect is itself
    add_check("D3 (DFI / U1)", eff_dfi_asp_for_d3, eff_u1_asp_for_d3, A_ASPECT_SMT)

    # D4: DFI / DFI -> Problematic/Overflow. THIS IS A DFI-DRIVEN SATURATION EVENT.
    #    Effective aspects for both DFIs become DFI_AS_AREO_TAG.
    #    Actual AVCA rule: Always AREO_UNIO (A_ASPECT_SMT).
    add_check("D4 (DFI / DFI -> Ovfl)", DFI_AS_AREO_TAG, DFI_AS_AREO_TAG, A_ASPECT_SMT)

    # --- 3. Addition (avc_add_v1.1) DFI Overflow Aspect ---
    print("\n  3. Defining Addition DFI Overflow Aspect Constraint for Tagged-DFI model:")
    # A1: DFI + DFI -> Overflow. THIS IS A DFI-DRIVEN SATURATION EVENT.
    #    Effective aspects for both DFIs become DFI_AS_AREO_TAG.
    #    Actual AVCA rule: Always AREO_UNIO (A_ASPECT_SMT).
    add_check("A1 (DFI + DFI -> Ovfl)", DFI_AS_AREO_TAG, DFI_AS_AREO_TAG, A_ASPECT_SMT)
    
    # --- Solve ---
    print(f"\n--- Solving for consistency of the Unified Tagged-DFI Aspect Model ({len(assertions)} assertions) ---")
    with Solver(name="z3") as s:
        s.add_assertions(assertions) # Add all check assertions
        
        final_result = s.solve()
        if final_result:
            print("  OVERALL RESULT: SAT")
            print("  CONCLUSION: The Unified Tagged-DFI model (MAX/OR where DFIs become Areo-tagged")
            print("              in DFI-driven saturation contexts) IS CONSISTENT with ALL specified AVCA Unio aspect outcomes.")
            print("  This is a **MAJOR ELEGANCE WIN** for H_AspectField, unifying P1 and P2 under a single operator with contextual tagging!")
            model = s.get_model()
            if model:
                 print(f"    (Example model instance for symbolic aspects: asp_u1 = {model.get_value(asp_u1)}, asp_u2 = {model.get_value(asp_u2)})")
        else:
            print("  OVERALL RESULT: UNSAT")
            print("  CONCLUSION: The Unified Tagged-DFI aspect model STILL CONFLICTS")
            print("              with at least one of the AVCA Unio aspect outcome rules.")
            print("  This means the 'tagging' logic or the single OR operator is still not perfectly capturing all cases.")
            # For debugging UNSAT, print the UNSAT core
            if s.supports_unsat_cores():
                print("    Attempting to get UNSAT core...")
                try:
                    unsat_core = s.get_unsat_core()
                    if unsat_core:
                        print("    Conflicting assertions (UNSAT core - names refer to internal SMT representation):")
                        for core_item_idx, core_item in enumerate(unsat_core):
                            print(f"      - Core Conflict {core_item_idx+1}: {core_item.serialize()}")
                    else:
                        print("    Solver could not provide an UNSAT core (list was empty).")
                except Exception as e:
                    print(f"    Error getting UNSAT core: {e}")
            else:
                print("    Solver does not support UNSAT cores for direct analysis here.")

if __name__ == "__main__":
    run_tagged_dfi_aspect_model_check()
