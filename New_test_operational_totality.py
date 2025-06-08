# test_operational_totality.py
# Purpose: To exhaustively test the operational totality (closure) of all four
# AVCA Core v1.2b operations for various Omega values.
# Ensures that for every pair of valid inputs (a,b) from S_Omega, op(a,b)
# produces a result that is also a valid member of S_Omega and raises no unexpected errors.

import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- Unio Class Definition (Copied directly from Appendix A of AVCA Core DraftV3) ---
class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio aspect must be 'zero' or 'areo'.")
        self.aspect = aspect
    def __eq__(self, other: object) -> bool:
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
def _check_val(x: AVCVal, current_omega: int): #
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter must be an integer >= 1. Got: {current_omega}")
    if isinstance(x, Unio):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")
    if current_omega == 1:
        if isinstance(x, int): # Integers are not allowed if Omega is 1, as DFI is empty
            raise ValueError(f"Invalid DFI Value for Omega=1: {x}. DFI is empty when Omega=1.")
    elif not (1 <= x < current_omega): # x must be DFI if it's an int and Omega > 1
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

def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal: # ⊖_v1.0 logic
    global Omega
    if Omega == 0: raise ValueError("Global Omega not set.")
    _check_val(a, Omega); _check_val(b, Omega)
    if isinstance(b, Unio): return a
    if isinstance(a, Unio): return AREO_UNIO
    # Both a and b are DFI integers
    return (a - b) if a > b else AREO_UNIO # type: ignore

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

def avc_div(a: AVCVal, b: AVCVal) -> AVCVal: # ⊘_v1.2B logic
    global Omega
    if Omega == 0: raise ValueError("Global Omega not set.")
    _check_val(a, Omega); _check_val(b, Omega)
    if isinstance(b, Unio): return AREO_UNIO # Rule B1
    if isinstance(a, Unio): # Rule B2 (b must be DFI here)
        return ZERO_UNIO if a.aspect == "zero" else AREO_UNIO # type: ignore
    # Rule B3: Both DFI
    quotient, remainder = divmod(a, b) # type: ignore
    return quotient if remainder == 0 and (1 <= quotient < Omega) else AREO_UNIO

# --- Helper for setting Omega for testing ---
def set_avca_omega(omega_value: int):
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega must be an integer >= 1.")
    Omega = omega_value

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Operational Totality (Closure) Tests (AVCA Core v1.2b) ---\n")
    
    omegas_to_test = [1, 2, 3, 4, 5] # User can extend this list, e.g., to include 7
    operations: Dict[str, Callable[[AVCVal, AVCVal], AVCVal]] = {
        "avc_add": avc_add,
        "avc_sub": avc_sub,
        "avc_mul": avc_mul,
        "avc_div": avc_div,
    }

    total_ops_checked = 0
    total_errors_found = 0

    for omega_val in omegas_to_test:
        set_avca_omega(omega_val)
        print(f"--- Testing with Omega = {omega_val} ---")
        
        s_omega: List[AVCVal] = []
        if omega_val == 1:
            s_omega = [ZERO_UNIO, AREO_UNIO] # Test both aspects as distinct inputs
        else:
            s_omega = [ZERO_UNIO, AREO_UNIO] + list(range(1, omega_val))
        
        print(f"  Carrier set S_Omega (for inputs, size {len(s_omega)}): {s_omega}")

        for op_name, op_func in operations.items():
            print(f"  Testing operation: {op_name}")
            errors_for_current_op_omega = 0
            ops_for_current_op_omega = 0

            for op_a, op_b in itertools.product(s_omega, s_omega):
                ops_for_current_op_omega += 1
                total_ops_checked += 1
                try:
                    result = op_func(op_a, op_b)
                    # Now, validate the result using _check_val
                    _check_val(result, omega_val) 
                    # If _check_val doesn't raise an error, the result is valid.
                except Exception as e:
                    print(f"    FAIL: {op_name}({op_a!r}, {op_b!r}) for Omega={omega_val}")
                    print(f"      Unexpected ERROR: {type(e).__name__} - {e}")
                    errors_for_current_op_omega += 1
                    total_errors_found += 1
            
            if errors_for_current_op_omega == 0:
                print(f"    PASS: {op_name} is total and closed for Omega={omega_val} ({ops_for_current_op_omega} input pairs checked).")
            else:
                print(f"    SUMMARY for {op_name}, Omega={omega_val}: {errors_for_current_op_omega} errors in {ops_for_current_op_omega} pairs.")
        print("-" * 70)

    print(f"\n--- Operational Totality (Closure) Tests Completed ---")
    print(f"Overall Summary: {total_ops_checked} operations checked across all Omegas.")
    if total_errors_found == 0:
        print("  ALL OPERATIONS ARE TOTAL AND CLOSED for the tested Omega values.")
    else:
        print(f"  TOTAL ERRORS FOUND: {total_errors_found}.")

if __name__ == "__main__":
    run_all_tests()