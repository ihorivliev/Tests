# Script B.1: Extended DFI Inverse Count Verification (Ω=2 to 12)
# Mathematical Obligation: Item from math LLM's "Check-off list before publication"
# "Inverse-count enumeration up to Ω = 12 (B.1) Run once; should be all PASS."
# This script extends R5.1 to verify |inv_DFI(a)| = a_val for Ω up to 12.

from typing import Union, List, Tuple, Any, Literal, Set

# --- Core AVCA Components (adapted from AVCA Core DraftV4 Appendix A) ---
# Using _sB1 suffix for clarity in this script's context.
_Omega_sB1: int = 0

class Unio_sB1:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"): # Sanity check
            raise ValueError("Unio_sB1 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_sB1) # Algebraic equivalence
    def __hash__(self) -> int:
        return hash(f"Unio_sB1_Algebraic_Singleton") # All Unio objects hash same
    def __repr__(self) -> str:
        return f"Unio_sB1('{self.aspect}')"
    def __lt__(self, other): # For sorting, not strictly necessary for logic
        if isinstance(other, Unio_sB1): return False
        if isinstance(other, int): return True # Unio considered "less than" DFI for sorting
        return NotImplemented

ZERO_UNIO_sB1 = Unio_sB1("zero")
AREO_UNIO_sB1 = Unio_sB1("areo") # DFI+DFI overflow in v1.1 add yields AREO_UNIO
AVCVal_sB1 = Union[int, Unio_sB1]

def set_avca_omega_sB1(omega_value: int):
    global _Omega_sB1
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_sB1 = omega_value
    # print(f"\nGlobal Omega for sB1 set to: {_Omega_sB1}")

def _check_val_sB1(x: AVCVal_sB1, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter ({current_omega}) for {var_name} must be an integer >= 1.")
    if isinstance(x, Unio_sB1):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Expected int or Unio_sB1. Omega={current_omega}")
    if current_omega == 1:
        # DFI is empty for Omega = 1. Integer inputs are invalid.
        raise ValueError(f"Invalid DFI Value for {var_name} for Omega=1: {x}. DFI is empty.")
    if not (1 <= x < current_omega): # DFI is [1, current_omega-1]
        raise ValueError(f"Invalid DFI Value for {var_name}: {x}. For Omega={current_omega}, DFI must be in range [1, {current_omega - 1}].")

# Standard AVCA Add (⊕_v1.1 logic from AVCA Core DraftV4 Appendix A)
def avc_add_v1_1_sB1(a: AVCVal_sB1, b: AVCVal_sB1, current_omega: int) -> AVCVal_sB1:
    _check_val_sB1(a, current_omega, "operand 'a'")
    _check_val_sB1(b, current_omega, "operand 'b'")

    if isinstance(a, Unio_sB1): return b
    if isinstance(b, Unio_sB1): return a
    
    # Both a and b are DFI integers at this point
    standard_sum: int = a + b # type: ignore
    
    if standard_sum < current_omega:
        return standard_sum  # Result is DFI
    else: # standard_sum >= current_omega (DFI additive overflow)
        return AREO_UNIO_sB1 # v1.1 refinement: overflow yields AREO_UNIO [cite: 1]

# --- Inverse Calculation and Verification Function ---
def verify_dfi_inverse_structure_extended(max_omega_to_test: int):
    print(f"--- Script B.1: Extended Computational Verification of |inv_DFI(a)| = a_val (for ⊕_v1.1) ---")
    print(f"--- Testing for Ω from 2 up to {max_omega_to_test} ---")
    print("Recall: Additive identity is algebraic Unio.")
    print("        For DFI a, DFI x: a ⊕ x ~ Unio means a + x ≥ Ω (result is AREO_UNIO_sB1).")

    overall_verification_passed = True

    for current_omega_val in range(2, max_omega_to_test + 1):
        set_avca_omega_sB1(current_omega_val)
        print(f"\n--- Verifying for Ω = {current_omega_val} ---")
        
        dfi_range = list(range(1, current_omega_val))
        if not dfi_range:
            print("  DFI is empty. No DFI inverses to check.")
            continue

        omega_passed = True
        for a_val in dfi_range: # a_val is the integer value of DFI element 'a'
            dfi_inverses_of_a: Set[int] = set()
            
            for x_val in dfi_range: # x_val is the integer value of DFI element 'x'
                try:
                    result = avc_add_v1_1_sB1(a_val, x_val, current_omega_val)
                    
                    if isinstance(result, Unio_sB1): # Check if result is algebraically Unio
                        dfi_inverses_of_a.add(x_val)
                except Exception as e:
                    print(f"    ERROR during computation for a={a_val}, x={x_val}, Ω={current_omega_val}: {e}")
                    overall_verification_passed = False
                    omega_passed = False
                    continue
            
            count_of_dfi_inverses = len(dfi_inverses_of_a)
            expected_count = a_val # This is the formula |inv_DFI(a)| = a_val
            verification_match = (count_of_dfi_inverses == expected_count)

            # Limit printing for larger Omega to keep output manageable,
            # but print if there's a mismatch or for smaller Omega.
            if current_omega_val <= 5 or not verification_match:
                print(f"  DFI Element a = {a_val}:")
                print(f"    Set of DFI inverses {{x_val | a_val ⊕ x_val ~ Unio}}: {sorted(list(dfi_inverses_of_a))}")
                print(f"    Count of DFI inverses |inv_DFI({a_val})|: {count_of_dfi_inverses}")
                print(f"    Expected count (a_val): {expected_count}")
                print(f"    Verification |inv_DFI({a_val})| == a_val: {verification_match}")
            
            if not verification_match:
                overall_verification_passed = False
                omega_passed = False
                print(f"      MISMATCH FOUND for Ω={current_omega_val}, a_val={a_val}!")
        
        if omega_passed and current_omega_val > 5:
             print(f"  All DFI elements in Ω={current_omega_val} passed the |inv_DFI(a)| = a_val check.")


    print("\n--- B.1 Summary ---")
    if overall_verification_passed:
        print(f"Overall verification for tested Ω range (2 to {max_omega_to_test}): PASSED. (|inv_DFI(a)| = a_val holds).")
    else:
        print(f"Overall verification for tested Ω range (2 to {max_omega_to_test}): FAILED. At least one mismatch found (see details above).")

# --- Main Execution ---
if __name__ == "__main__":
    max_omega_for_b1 = 12 # As requested by math LLM
    
    verify_dfi_inverse_structure_extended(max_omega_for_b1)
    
    print("\n====== B.1 Script Finished ======")