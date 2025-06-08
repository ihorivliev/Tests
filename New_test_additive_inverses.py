# test_additive_inverses.py
# Purpose: To inspect the additive inverse structure for avc_add (v1.1 logic)
# in AVCA Core v1.2b for Omega = 1 through 7.
# Checks for uniqueness of inverses and lists all found inverses.

import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable, Set

# --- Unio Class Definition (Copied directly from Appendix A of AVCA Core DraftV3) ---
class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio aspect must be 'zero' or 'areo'.")
        self.aspect = aspect
    def __eq__(self, other: object) -> bool: # Checks for algebraic equivalence
        return isinstance(other, Unio)
    def __hash__(self) -> int:
        return hash(type(self)) # All Unio objects hash the same
    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"

# --- Canonical Unio Instances ---
ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")

# --- Type Alias for AVCA Values ---
AVCVal = Union[int, Unio]

# --- Global Omega Parameter ---
Omega: int = 0

# --- Domain Enforcement and Input Validation ---
def _check_val(x: AVCVal, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter must be an integer >= 1. Got: {current_omega}")
    if isinstance(x, Unio): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")
    if current_omega == 1:
        if isinstance(x, int):
            raise ValueError(f"Invalid DFI Value for Omega=1: {x}. DFI is empty when Omega=1.")
    elif not (1 <= x < current_omega):
            raise ValueError(f"Invalid DFI Value: {x}. For Omega={current_omega}, DFI integers must be in range [1, {current_omega - 1}].")

# --- AVCA Operations (v1.2b logic from Appendix A of AVCA Core DraftV3) ---
def avc_add(a: AVCVal, b: AVCVal) -> AVCVal: # ⊕_v1.1 logic
    global Omega
    if Omega == 0: raise ValueError("Global Omega not set.")
    _check_val(a, Omega); _check_val(b, Omega)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < Omega else AREO_UNIO # v1.1 DFI overflow to AREO_UNIO

# --- Helper for setting Omega for testing ---
def set_avca_omega(omega_value: int):
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega must be an integer >= 1.")
    Omega = omega_value

# --- Helper to compare AVCA values (respecting Unio's algebraic equivalence) ---
# The additive identity element is algebraically Unio.
# We can use ZERO_UNIO as the canonical identity representation for checking.
ADDITIVE_IDENTITY_REPR = ZERO_UNIO 

def avca_equals(val1: AVCVal, val2: AVCVal) -> bool:
    if isinstance(val1, Unio) and isinstance(val2, Unio):
        return True 
    return val1 == val2

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Additive Inverse Structure Tests (AVCA Core v1.2b, Add v1.1) ---\n")
    
    omegas_to_test = list(range(1, 8)) # Omega = 1 through 7

    for omega_val in omegas_to_test:
        set_avca_omega(omega_val)
        print(f"--- Testing with Omega = {omega_val} ---")
        
        s_omega: List[AVCVal] = []
        # For generating inputs 'a' and potential inverses 'x',
        # we should include both ZERO_UNIO and AREO_UNIO as distinct Python objects
        # to test their behavior thoroughly, plus DFI elements.
        s_omega_elements_for_iteration: List[AVCVal] = [ZERO_UNIO, AREO_UNIO]
        if omega_val > 1:
            s_omega_elements_for_iteration.extend(list(range(1, omega_val)))
        
        print(f"  Carrier set S_Omega (elements for iteration, size {len(s_omega_elements_for_iteration)}): {[repr(el) for el in s_omega_elements_for_iteration]}")

        all_elements_pass_uniqueness_check = True

        for a in s_omega_elements_for_iteration:
            inverses_found_for_a: List[AVCVal] = []
            for x in s_omega_elements_for_iteration:
                try:
                    result = avc_add(a, x)
                    if avca_equals(result, ADDITIVE_IDENTITY_REPR): # Check if a+x == Unio (algebraic identity)
                        inverses_found_for_a.append(x)
                except Exception as e:
                    print(f"    ERROR during avc_add({a!r}, {x!r}): {e}")
                    # This case should ideally not happen if _check_val and totality are correct
            
            # Analyze uniqueness based on *algebraically distinct* inverses
            algebraically_distinct_inverses: Set[AVCVal] = set()
            if inverses_found_for_a:
                # To count algebraically distinct inverses, we can't just use a Python set of DFI ints
                # because Unio('zero') and Unio('areo') are distinct objects but same algebraic Unio.
                # However, if an inverse is DFI, it's distinct from other DFI values.
                # If an inverse is Unio, it's algebraically just "Unio".
                
                has_unio_inverse = any(isinstance(inv, Unio) for inv in inverses_found_for_a)
                dfi_inverses = {inv for inv in inverses_found_for_a if isinstance(inv, int)}

                num_algebraically_distinct = len(dfi_inverses)
                if has_unio_inverse:
                    num_algebraically_distinct += 1 
                    # Add Unio class itself to represent algebraic Unio for set uniqueness
                    # This isn't perfect for the set, better to count manually.
                
                # Simplified count for algebraic uniqueness:
                # Create a list of representatives: DFI ints as themselves, any Unio as just "Unio_algebraic"
                algebraic_reps = []
                seen_algebraic_unio = False
                for inv in inverses_found_for_a:
                    if isinstance(inv, Unio):
                        if not seen_algebraic_unio:
                            algebraic_reps.append("Unio_algebraic_rep") # Use a string token
                            seen_algebraic_unio = True
                    else: # DFI int
                        algebraic_reps.append(inv)
                
                num_algebraically_distinct_actual = len(set(algebraic_reps))


            print(f"    Element a = {a!r}: Found inverse objects = {[repr(inv) for inv in inverses_found_for_a]}")
            
            is_unique_expected = (omega_val <= 2)
            is_unique_observed = (num_algebraically_distinct_actual == 1) if inverses_found_for_a else False # No inverse means not unique for this check

            status = "OK"
            if not inverses_found_for_a:
                status = "FAIL (No inverse found!)" # Should not happen for a loop
                all_elements_pass_uniqueness_check = False
            elif is_unique_expected != is_unique_observed:
                status = f"FAIL (Uniqueness mismatch: Expected_unique={is_unique_expected}, Observed_unique={is_unique_observed})"
                all_elements_pass_uniqueness_check = False
            
            print(f"      Number of algebraically distinct inverses: {num_algebraically_distinct_actual}. Unique: {is_unique_observed}. Expected unique: {is_unique_expected}. Status: {status}")

        if all_elements_pass_uniqueness_check:
            print(f"  Omega={omega_val}: Inverse uniqueness pattern matches expectation.")
        else:
            print(f"  Omega={omega_val}: Inverse uniqueness pattern DOES NOT match expectation for one or more elements.")
        print("-" * 70)

    print(f"\n--- Additive Inverse Structure Tests Completed ---")

if __name__ == "__main__":
    run_all_tests()