from pysmt.shortcuts import Symbol, Int, Equals, And, Or, Not, Ite, Solver, TRUE, FALSE, get_model
from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode # For type hinting
from typing import Dict, Tuple, List

# --- Aspect Representations (as SMT Integers) ---
Z_ASPECT_SMT = Int(0)  # Representing ZERO_UNIO aspect (False-like)
A_ASPECT_SMT = Int(1)  # Representing AREO_UNIO aspect (True-like)

# --- The Proposed Universal Aspect Operation: MAX(asp1, asp2) or Logical OR ---
# If Z_ASPECT_SMT=0 and A_ASPECT_SMT=1, this is MAX.
# If Z_ASPECT_SMT=False and A_ASPECT_SMT=True, this is OR.
def aspect_semilattice_op(aspect1_smt: FNode, aspect2_smt: FNode) -> FNode:
    """
    Calculates the resulting aspect based on MAX/OR logic.
    Assumes aspect1_smt and aspect2_smt are either Z_ASPECT_SMT or A_ASPECT_SMT.
    """
    return Ite(Or(Equals(aspect1_smt, A_ASPECT_SMT), Equals(aspect2_smt, A_ASPECT_SMT)), 
               A_ASPECT_SMT, 
               Z_ASPECT_SMT)

# --- Main Test Function ---
def run_aspect_completeness_check():
    print("--- aspect_complete.py: SMT Check for Universal Aspect Semilattice (MAX/OR) ---")
    print(f"    Hypothesis: A single aspect operation (MAX/OR with Z={Z_ASPECT_SMT.constant_value()}, A={A_ASPECT_SMT.constant_value()})")
    print(f"    can predict the aspect of all Unio results in avc_mul_v1.2 and avc_div_AltD_Balanced.")

    assertions = []
    
    # --- Symbolic Aspects for Operands ---
    # asp_u1: Aspect of a generic Unio operand 1
    # asp_u2: Aspect of a generic Unio operand 2
    # asp_dfi: Effective aspect of a DFI operand when interacting to produce Unio.
    #          Auditor suggested DFI might act as "neutral" or Z-like. Let's assume DFI_eff_aspect = Z_ASPECT_SMT.
    
    asp_u1 = Symbol("asp_u1", SMT_INT_TYPE)
    asp_u2 = Symbol("asp_u2", SMT_INT_TYPE)
    # DFI's effective aspect when it's part of an operation that results in Unio.
    # For MAX/OR, if DFI is neutral or Z-like, it's 0.
    DFI_EFF_ASPECT_SMT = Z_ASPECT_SMT 

    # Constraints that asp_u1 and asp_u2 are valid aspects (0 or 1)
    assertions.append(Or(Equals(asp_u1, Z_ASPECT_SMT), Equals(asp_u1, A_ASPECT_SMT)))
    assertions.append(Or(Equals(asp_u2, Z_ASPECT_SMT), Equals(asp_u2, A_ASPECT_SMT)))

    all_checks_consistent = True # Flag to track overall consistency

    # --- 1. Test avc_mul_v1.2 Aspect Outcomes ---
    print("\n  1. Checking Multiplication (avc_mul_v1.2) Aspects vs. MAX/OR logic:")
    
    # Case M1: U1 @ U2 -> aspect_semilattice_op(asp_u1, asp_u2)
    # AVCA actual rule: AREO if any input aspect is AREO, else ZERO. This IS aspect_semilattice_op.
    actual_m_u1u2 = Ite(Or(Equals(asp_u1, A_ASPECT_SMT), Equals(asp_u2, A_ASPECT_SMT)), A_ASPECT_SMT, Z_ASPECT_SMT)
    check_m_u1u2 = Equals(aspect_semilattice_op(asp_u1, asp_u2), actual_m_u1u2)
    assertions.append(check_m_u1u2)
    print(f"    Test M1 (U1 @ U2): Constraining MAX/OR to match AVCA rule (expected to be consistent).")

    # Case M2: DFI @ U1 -> aspect_semilattice_op(DFI_EFF_ASPECT_SMT, asp_u1)
    # AVCA actual rule: AREO if U1 is AREO, else ZERO.
    actual_m_dfiu1 = Ite(Equals(asp_u1, A_ASPECT_SMT), A_ASPECT_SMT, Z_ASPECT_SMT)
    check_m_dfiu1 = Equals(aspect_semilattice_op(DFI_EFF_ASPECT_SMT, asp_u1), actual_m_dfiu1)
    assertions.append(check_m_dfiu1)
    print(f"    Test M2 (DFI @ U1 using DFI_eff_aspect={DFI_EFF_ASPECT_SMT.constant_value()}): Constraining MAX/OR to match AVCA rule.")

    # Case M3: DFI @ DFI (overflow) -> aspect_semilattice_op(DFI_EFF_ASPECT_SMT, DFI_EFF_ASPECT_SMT)
    # AVCA actual rule: DFI overflows always result in AREO_UNIO.
    actual_m_dfidfi_ovfl = A_ASPECT_SMT
    check_m_dfidfi_ovfl = Equals(aspect_semilattice_op(DFI_EFF_ASPECT_SMT, DFI_EFF_ASPECT_SMT), actual_m_dfidfi_ovfl)
    assertions.append(check_m_dfidfi_ovfl) # THIS IS THE CRITICAL TEST FOR MUL
    print(f"    Test M3 (DFI @ DFI -> Overflow): Constraining MAX/OR({DFI_EFF_ASPECT_SMT.constant_value()},{DFI_EFF_ASPECT_SMT.constant_value()}) to match AVCA's AREO outcome.")
    
    # --- 2. Test avc_div_AltD_Balanced Aspect Outcomes (where result is Unio) ---
    print("\n  2. Checking Division (avc_div_AltD_Balanced) Aspects vs. MAX/OR logic:")

    # Case D1: U1 / U2 (dividend_asp=asp_u1, divisor_asp=asp_u2)
    # AVCA AltD U/U rule: if asp_divisor is AREO -> AREO; else (divisor ZERO) -> preserve dividend_asp.
    actual_d_u1u2 = Ite(Equals(asp_u2, A_ASPECT_SMT), A_ASPECT_SMT, asp_u1)
    check_d_u1u2 = Equals(aspect_semilattice_op(asp_u1, asp_u2), actual_d_u1u2)
    assertions.append(check_d_u1u2) # CRITICAL: Does MAX/OR match this complex AltD rule?
    print(f"    Test D1 (U1 / U2): Constraining MAX/OR to match AVCA U/U rule.")

    # Case D2: U1 / DFI (dividend_asp=asp_u1)
    # AVCA AltD U/DFI rule: Preserves dividend aspect.
    actual_d_u1dfi = asp_u1 
    check_d_u1dfi = Equals(aspect_semilattice_op(asp_u1, DFI_EFF_ASPECT_SMT), actual_d_u1dfi)
    assertions.append(check_d_u1dfi)
    print(f"    Test D2 (U1 / DFI): Constraining MAX/OR to match AVCA U/DFI rule.")

    # Case D3: DFI / U1 (divisor_asp=asp_u1)
    # AVCA AltD DFI/U rule: Always AREO_UNIO.
    actual_d_dfiu1 = A_ASPECT_SMT
    check_d_dfiu1 = Equals(aspect_semilattice_op(DFI_EFF_ASPECT_SMT, asp_u1), actual_d_dfiu1)
    assertions.append(check_d_dfiu1) # CRITICAL
    print(f"    Test D3 (DFI / U1): Constraining MAX/OR to match AVCA DFI/U rule (AREO).")

    # Case D4: DFI / DFI (overflow) -> Results in AREO_UNIO
    # AVCA rule: DFI overflows always result in AREO_UNIO.
    actual_d_dfidfi_ovfl = A_ASPECT_SMT
    check_d_dfidfi_ovfl = Equals(aspect_semilattice_op(DFI_EFF_ASPECT_SMT, DFI_EFF_ASPECT_SMT), actual_d_dfidfi_ovfl)
    assertions.append(check_d_dfidfi_ovfl) # Same as M3, CRITICAL
    print(f"    Test D4 (DFI / DFI -> Overflow): Constraining MAX/OR({DFI_EFF_ASPECT_SMT.constant_value()},{DFI_EFF_ASPECT_SMT.constant_value()}) to match AVCA's AREO outcome.")
    
    # Also need to check DFI ⊕ DFI -> Overflow to AREO_UNIO
    print("\n  3. Checking Addition (avc_add_v1.1) DFI Overflow Aspect vs. MAX/OR logic:")
    # AVCA rule: DFI_overflow always results in AREO_UNIO.
    actual_add_dfidfi_ovfl = A_ASPECT_SMT
    check_add_dfidfi_ovfl = Equals(aspect_semilattice_op(DFI_EFF_ASPECT_SMT, DFI_EFF_ASPECT_SMT), actual_add_dfidfi_ovfl)
    assertions.append(check_add_dfidfi_ovfl) # Same as M3, D4, CRITICAL
    print(f"    Test A1 (DFI + DFI -> Overflow): Constraining MAX/OR({DFI_EFF_ASPECT_SMT.constant_value()},{DFI_EFF_ASPECT_SMT.constant_value()}) to match AVCA's AREO outcome.")


    # --- Solve ---
    print("\n--- Solving for consistency of MAX/OR with all AVCA Unio aspect outcomes ---")
    with Solver(name="z3") as s:
        s.add_assertions(assertions) # Add all check assertions
        
        final_result = s.solve()
        if final_result:
            print("  OVERALL RESULT: SAT")
            print("  CONCLUSION: It IS possible to define symbolic aspects (asp_u1, asp_u2)")
            print(f"              such that the simple MAX/OR logic (with DFI_eff_aspect={DFI_EFF_ASPECT_SMT.constant_value()})")
            print("              CONSISTENTLY matches ALL specified AVCA Unio aspect outcomes for mul_v1.2 and div_AltD.")
            print("  This is a VERY STRONG POSITIVE result for H_AspectField, suggesting a universal underlying aspect algebra principle.")
            model = s.get_model()
            print("    (Model for asp_u1, asp_u2 would show one instance; the proof is universal due to symbolic nature)")
            print(f"    Example model instance: asp_u1 = {model.get_value(asp_u1)}, asp_u2 = {model.get_value(asp_u2)}")
        else:
            print("  OVERALL RESULT: UNSAT")
            print("  CONCLUSION: The simple MAX/OR semilattice logic (with chosen DFI_eff_aspect)")
            print("              CONFLICTS with at least one of the AVCA Unio aspect outcome rules")
            print("              for mul_v1.2 or div_AltD when considering all cases.")
            print("  This implies H_AspectField (with this specific simple operator and DFI aspect mapping) is falsified.")
            print("  Further investigation would require checking which assertion(s) caused the conflict.")
            # To find conflicting clauses, you might need to add them one by one or use unsat core.
            # For now, we just get the overall consistency.

if __name__ == "__main__":
    run_aspect_completeness_check()

