# Script R5.1: Computational Verification of |inv_DFI(a)| = a_val & Inverse Set Listing
# Mathematical Obligation: R5 from math LLM's refined deliverables.
# (Prove formula |inv_DFI(a)| = a_val for all Ω, all DFI a).
# This script provides computational verification and lists inverse sets.

from typing import Union, List, Tuple, Any, Literal, Set

# --- Core AVCA Components (adapted from AVCA Core DraftV4 Appendix A) ---
# Renaming to avoid potential conflicts if multiple R-scripts are combined later.
_Omega_R5: int = 0

class Unio_R5:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"): # Sanity check
            raise ValueError("Unio_R5 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_R5) # Algebraic equivalence
    def __hash__(self) -> int:
        return hash(type(self)) # All Unio objects hash same
    def __repr__(self) -> str:
        return f"Unio_R5('{self.aspect}')"

ZERO_UNIO_R5 = Unio_R5("zero")
AREO_UNIO_R5 = Unio_R5("areo") # DFI+DFI overflow in v1.1 add yields AREO_UNIO
AVCVal_R5 = Union[int, Unio_R5]

def set_avca_omega_r5(omega_value: int):
    global _Omega_R5
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_R5 = omega_value
    # print(f"\nGlobal Omega for R5.1 set to: {_Omega_R5}")

def _check_val_r5(x: AVCVal_R5, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter ({current_omega}) for {var_name} must be an integer >= 1.")
    if isinstance(x, Unio_R5):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Expected int or Unio_R5. Omega={current_omega}")
    if current_omega == 1:
        # DFI is empty for Omega = 1. Integer inputs are invalid.
        raise ValueError(f"Invalid DFI Value for {var_name} for Omega=1: {x}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value for {var_name}: {x}. For Omega={current_omega}, DFI must be in range [1, {current_omega - 1}].")

# Standard AVCA Add (⊕_v1.1 logic from AVCA Core DraftV4 Appendix A)
def avc_add_v1_1_r5(a: AVCVal_R5, b: AVCVal_R5, current_omega: int) -> AVCVal_R5:
    # Check inputs using the current_omega for this operation context
    _check_val_r5(a, current_omega, "operand 'a'")
    _check_val_r5(b, current_omega, "operand 'b'")

    if isinstance(a, Unio_R5): return b
    if isinstance(b, Unio_R5): return a
    
    # Both a and b are DFI integers at this point
    # Their validity (1 <= val < current_omega) was confirmed by _check_val_r5
    standard_sum: int = a + b # type: ignore
    
    if standard_sum < current_omega:
        return standard_sum  # Result is DFI
    else: # standard_sum >= current_omega (DFI additive overflow)
        return AREO_UNIO_R5 # v1.1 refinement: overflow yields AREO_UNIO

# --- Inverse Calculation and Verification Function ---
def verify_dfi_inverse_structure(max_omega_to_test: int):
    print(f"--- R5.1: Computational Verification of |inv_DFI(a)| = a_val (for ⊕_v1.1) ---")
    print(f"--- Testing for Ω from 2 up to {max_omega_to_test} ---")
    print("Recall: Additive identity is algebraic Unio.")
    print("        For DFI a, DFI x: a ⊕ x ~ Unio means a + x ≥ Ω (result is AREO_UNIO_R5).")

    overall_verification_passed = True

    for current_omega_val in range(2, max_omega_to_test + 1):
        set_avca_omega_r5(current_omega_val)
        print(f"\n--- Verifying for Ω = {current_omega_val} ---")
        
        dfi_range = list(range(1, current_omega_val))
        if not dfi_range:
            print("  DFI is empty. No DFI inverses to check.")
            continue

        for a_val in dfi_range: # a_val is the integer value of DFI element 'a'
            dfi_inverses_of_a: Set[int] = set()
            
            for x_val in dfi_range: # x_val is the integer value of DFI element 'x'
                try:
                    # Ensure global _Omega_R5 is set for the context of avc_add_v1_1_r5
                    # set_avca_omega_r5(current_omega_val) # Already set at the start of outer loop
                    result = avc_add_v1_1_r5(a_val, x_val, current_omega_val)
                    
                    if isinstance(result, Unio_R5): # Check if result is algebraically Unio
                        dfi_inverses_of_a.add(x_val)
                except Exception as e:
                    print(f"    ERROR during computation for a={a_val}, x={x_val}, Ω={current_omega_val}: {e}")
                    overall_verification_passed = False
                    continue
            
            count_of_dfi_inverses = len(dfi_inverses_of_a)
            expected_count = a_val
            verification_match = (count_of_dfi_inverses == expected_count)

            print(f"  DFI Element a = {a_val}:")
            print(f"    Set of DFI inverses {{x_val | a_val ⊕ x_val ~ Unio}}: {sorted(list(dfi_inverses_of_a))}")
            print(f"    Count of DFI inverses |inv_DFI({a_val})|: {count_of_dfi_inverses}")
            print(f"    Expected count (a_val): {expected_count}")
            print(f"    Verification |inv_DFI({a_val})| == a_val: {verification_match}")
            
            if not verification_match:
                overall_verification_passed = False
                print(f"      MISMATCH FOUND for Ω={current_omega_val}, a_val={a_val}!")

    print("\n--- R5.1 Summary ---")
    if overall_verification_passed:
        print("Overall verification for tested Ω range: PASSED. (|inv_DFI(a)| = a_val holds).")
    else:
        print("Overall verification for tested Ω range: FAILED. At least one mismatch found (see details above).")

# --- Main Execution ---
if __name__ == "__main__":
    # As per AVCA Core DraftV4 Appendix D.2 and test_additive_inverses_refined.py,
    # the property |inv(a)|=a_val was computationally confirmed for Ω=1-7.
    # For DFI elements, Ω must be at least 2.
    # Let's test Ω from 2 to 7 to align with previous computational work.
    max_omega_for_r5_1 = 7 
    
    verify_dfi_inverse_structure(max_omega_for_r5_1)
    
    print("\n====== R5.1 Script Finished ======")