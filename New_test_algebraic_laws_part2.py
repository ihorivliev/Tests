# test_algebraic_laws_part2.py
# Purpose: To exhaustively test distributivity (mul over add) and
# additive cancellation for AVCA Core v1.2b operations for small Omega values.

import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

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
        return hash(type(self))
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
    return standard_sum if standard_sum < Omega else AREO_UNIO

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal: # ⊗_v1.2 logic
    global Omega
    if Omega == 0: raise ValueError("Global Omega not set.")
    _check_val(a, Omega); _check_val(b, Omega)
    a_is_unio = isinstance(a, Unio); b_is_unio = isinstance(b, Unio)
    if a_is_unio or b_is_unio:
        is_any_areo = (a_is_unio and a.aspect == "areo") or \
                      (b_is_unio and b.aspect == "areo") # type: ignore
        return AREO_UNIO if is_any_areo else ZERO_UNIO
    else: # Both DFI
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < Omega else AREO_UNIO

# --- Helper for setting Omega for testing ---
def set_avca_omega(omega_value: int):
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega must be an integer >= 1.")
    Omega = omega_value

# --- Helper to compare AVCA values (respecting Unio's algebraic equivalence) ---
def avca_equals(val1: AVCVal, val2: AVCVal) -> bool:
    if isinstance(val1, Unio) and isinstance(val2, Unio):
        return True # All Unio objects are algebraically equal
    # Handle comparison of Unio object with its representative integer 0 for tests if necessary,
    # but direct comparison val1 == val2 should work due to Unio.__eq__ handling only Unio types.
    return val1 == val2

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Algebraic Law Tests (Distributivity, Cancellation - AVCA Core v1.2b) ---\n")
    
    omegas_to_test_n3 = [1, 2, 3] # N^3 complexity laws

    overall_results = {}

    # Test Distributivity of avc_mul over avc_add (Left: a*(b+c) == (a*b)+(a*c))
    print("## Testing Left Distributivity of Mul (v1.2) over Add (v1.1) ##")
    print("## a * (b + c) == (a * b) + (a * c) ##")
    for omega_val in omegas_to_test_n3:
        set_avca_omega(omega_val)
        s_omega: List[AVCVal] = [ZERO_UNIO, AREO_UNIO] + list(range(1, omega_val)) if omega_val > 1 else [ZERO_UNIO, AREO_UNIO]
        
        law_holds = True
        counterexample = None
        checked_triplets = 0
        for a, b, c in itertools.product(s_omega, s_omega, s_omega):
            checked_triplets += 1
            try:
                # LHS: a * (b + c)
                b_plus_c = avc_add(b, c)
                lhs = avc_mul(a, b_plus_c)
                
                # RHS: (a * b) + (a * c)
                a_mul_b = avc_mul(a, b)
                a_mul_c = avc_mul(a, c)
                rhs = avc_add(a_mul_b, a_mul_c)
                
                if not avca_equals(lhs, rhs):
                    law_holds = False
                    counterexample = (a,b,c,lhs,rhs)
                    break
            except Exception as e:
                law_holds = False
                counterexample = (a,b,c, "Exception", str(e))
                break
            if not law_holds: break # Inner loop break
        status = "Holds" if law_holds else f"FAILS (Counterexample: a={counterexample[0]!r}, b={counterexample[1]!r}, c={counterexample[2]!r} -> a(b+c)={counterexample[3]!r}, (ab)+(ac)={counterexample[4]!r})"
        overall_results[f"Distributivity_MulOverAdd_Omega_{omega_val}"] = status
        print(f"  Omega={omega_val}: {status} (Checked up to {checked_triplets} triplets)")
    print("-" * 70)

    # Test Additive Cancellation Law ((a + x == b + x) => a == b)
    print("\n## Testing Additive Cancellation Law for Add (v1.1) ##")
    print("## (a + x == b + x) => a == b ##")
    for omega_val in omegas_to_test_n3:
        set_avca_omega(omega_val)
        s_omega: List[AVCVal] = [ZERO_UNIO, AREO_UNIO] + list(range(1, omega_val)) if omega_val > 1 else [ZERO_UNIO, AREO_UNIO]

        law_holds = True
        counterexample = None
        checked_triplets = 0
        # Iterate a, b, x from S_omega
        # Check if a+x == b+x. If so, then check if a == b.
        # If the first is true and the second is false, cancellation fails.
        for a, b, x in itertools.product(s_omega, s_omega, s_omega):
            checked_triplets += 1
            try:
                aplusx = avc_add(a, x)
                bplusx = avc_add(b, x)

                if avca_equals(aplusx, bplusx): # If (a + x == b + x)
                    if not avca_equals(a,b):   # Check if a != b
                        law_holds = False
                        counterexample = (a,b,x,aplusx) # aplusx and bplusx are the same
                        break 
            except Exception as e:
                law_holds = False # Treat exception as failure for this test structure
                counterexample = (a,b,x, "Exception: " + str(e))
                break
            if not law_holds: break # Inner loop break
        
        status_detail = ""
        if not law_holds and counterexample:
            if isinstance(counterexample[3], str) and "Exception" in counterexample[3]:
                 status_detail = f"FAILS (Unexpected Exception with a={counterexample[0]!r}, b={counterexample[1]!r}, x={counterexample[2]!r} -> {counterexample[3]})"
            else:
                 status_detail = f"FAILS (Counterexample: a={counterexample[0]!r}, b={counterexample[1]!r}, x={counterexample[2]!r} -> both sums are {counterexample[3]!r}, but a != b)"
        
        status = "Holds" if law_holds else status_detail
        overall_results[f"AdditiveCancellation_Omega_{omega_val}"] = status
        print(f"  Omega={omega_val}: {status} (Checked up to {checked_triplets} triplets)")
    print("-" * 70)

    print("\n--- Algebraic Law Tests (Part 2) Completed ---")

if __name__ == "__main__":
    run_all_tests()