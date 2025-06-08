# test_additive_inverses_refined.py
# Purpose: To inspect the additive inverse structure for avc_add (v1.1 logic)
# in AVCA Core v1.2b for Omega = 1 through 7, using refined expectations
# for the number of inverses based on math LLM feedback.

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
ADDITIVE_IDENTITY_REPR = ZERO_UNIO 

def avca_equals(val1: AVCVal, val2: AVCVal) -> bool:
    if isinstance(val1, Unio) and isinstance(val2, Unio):
        return True 
    return val1 == val2

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Additive Inverse Structure Tests (Refined Expectations) ---\n")
    print("    (AVCA Core v1.2b, Add v1.1 logic)\n")
    
    omegas_to_test = list(range(1, 8)) # Omega = 1 through 7

    for omega_val in omegas_to_test:
        set_avca_omega(omega_val)
        print(f"--- Testing with Omega = {omega_val} ---")
        
        s_omega_elements_for_iteration: List[AVCVal] = [ZERO_UNIO, AREO_UNIO]
        if omega_val > 1:
            s_omega_elements_for_iteration.extend(list(range(1, omega_val)))
        
        print(f"  Iterating 'a' over: {[repr(el) for el in s_omega_elements_for_iteration]}")
        print(f"  Iterating 'x' over: {[repr(el) for el in s_omega_elements_for_iteration]}")

        all_elements_in_omega_behave_as_expected = True
        system_has_universal_unique_inverses_observed = True 

        for a in s_omega_elements_for_iteration:
            inverses_found_for_a_objects: List[AVCVal] = []
            for x in s_omega_elements_for_iteration:
                try:
                    result = avc_add(a, x)
                    if avca_equals(result, ADDITIVE_IDENTITY_REPR): # a+x == Unio
                        inverses_found_for_a_objects.append(x)
                except Exception as e:
                    print(f"    ERROR during avc_add({a!r}, {x!r}): {e}")
                    all_elements_in_omega_behave_as_expected = False
            
            # Calculate number of algebraically distinct inverses found
            algebraic_reps_of_inverses = []
            seen_algebraic_unio_inv = False
            for inv_obj in inverses_found_for_a_objects:
                if isinstance(inv_obj, Unio):
                    if not seen_algebraic_unio_inv:
                        algebraic_reps_of_inverses.append("Unio_algebraic_inv_rep")
                        seen_algebraic_unio_inv = True
                else: # DFI int
                    algebraic_reps_of_inverses.append(inv_obj)
            num_alg_distinct_inverses_found = len(set(algebraic_reps_of_inverses))

            # Determine expected number of algebraically distinct inverses based on refined theory
            expected_num_alg_distinct_inverses = 0
            if isinstance(a, Unio):
                expected_num_alg_distinct_inverses = 1 # Unio's inverse is Unio itself
            else: # 'a' is DFI
                a_val = a 
                # According to math LLM, a DFI 'a' has 'a_val' DFI inverses.
                # Unio objects are not inverses for DFI 'a'.
                expected_num_alg_distinct_inverses = a_val 

            # Check if found count matches expected count for this 'a'
            element_matches_expectation = (num_alg_distinct_inverses_found == expected_num_alg_distinct_inverses)
            
            print(f"    Element a = {a!r}:")
            print(f"      Found inverse objects: {[repr(inv) for inv in inverses_found_for_a_objects]}")
            print(f"      Num algebraically distinct inverses found: {num_alg_distinct_inverses_found}")
            print(f"      Expected num algebraically distinct inverses (per refined theory): {expected_num_alg_distinct_inverses}")
            
            if element_matches_expectation:
                print(f"      Status for element {a!r}: PASS (Observed count matches refined theory)")
            else:
                print(f"      Status for element {a!r}: FAIL (Observed count {num_alg_distinct_inverses_found} != Expected {expected_num_alg_distinct_inverses})")
                all_elements_in_omega_behave_as_expected = False

            if num_alg_distinct_inverses_found != 1:
                system_has_universal_unique_inverses_observed = False
        
        # Overall check for this Omega based on original expectation for the *system*
        system_uniqueness_expected = (omega_val <= 2)
        if system_uniqueness_expected == system_has_universal_unique_inverses_observed:
            print(f"  Omega={omega_val}: System-level uniqueness property (Unique iff Omega<=2) is CONSISTENT with observations.")
        else:
            print(f"  Omega={omega_val}: System-level uniqueness property (Unique iff Omega<=2) is INCONSISTENT. Expected_universal_unique={system_uniqueness_expected}, Observed_universal_unique={system_has_universal_unique_inverses_observed}.")
        
        if not all_elements_in_omega_behave_as_expected:
             print(f"  Omega={omega_val}: One or more elements FAILED the refined count expectation.")
        print("-" * 70)

    print(f"\n--- Additive Inverse Structure Tests (Refined Expectations) Completed ---")

if __name__ == "__main__":
    run_all_tests()