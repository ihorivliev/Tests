# test_avc_sub_specific_cases.py
# Purpose: To test specific cases of the avc_sub (original v1.0 logic)
# operation from AVCA Core v1.2b for various Omega values.
# Focus: Unio as subtrahend identity, Unio as minuend ("Stuck-at-Areo"),
# DFI subtractions including underflow/cancellation to AREO_UNIO.

from typing import Literal, Union, Any, Tuple, List, Dict

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
def _check_val(x: AVCVal, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter must be an integer >= 1. Got: {current_omega}")
    if isinstance(x, Unio):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI Value for Omega=1: {x}. DFI is empty when Omega=1.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value: {x}. For Omega={current_omega}, DFI integers must be in range [1, {current_omega - 1}].")

# --- avc_sub (⊖_v1.0 logic from Appendix A of AVCA Core DraftV3) ---
def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal:
    """
    ⊖ : S_Ω × S_Ω → S_Ω (Asymmetric Subtraction - Original v1.0 Logic)
    - Unio (any aspect object) as subtrahend acts as identity (X - Unio -> X).
    - Unio (any aspect object) as minuend with DFI subtrahend (Unio - DFI_k -> AREO_UNIO).
    - DFI - DFI: Standard difference if > 0; result is AREO_UNIO if difference ≤ 0.
    """
    global Omega
    if Omega == 0:
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    _check_val(a, Omega)
    _check_val(b, Omega)

    if isinstance(b, Unio): # Rule 1: X ⊖ U → X
        return a
    
    if isinstance(a, Unio): # Rule 2: U ⊖ DFI_k → AREO_UNIO (since b must be DFI here)
        return AREO_UNIO
    
    # Both a and b are DFI integers (Rule 3)
    # Types are guaranteed to be int by here due to _check_val and preceding checks
    if a > b: # type: ignore
        return a - b # type: ignore      
    else: # a <= b
        return AREO_UNIO     # DFI subtractive underflow/cancellation yields AREO_UNIO

# --- Helper for setting Omega for testing ---
def set_avca_omega(omega_value: int):
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega must be an integer >= 1.")
    Omega = omega_value

# --- Test Cases Definition ---
TestCasesType = List[Tuple[AVCVal, AVCVal, AVCVal, Union[str, None]]]

tests_omega_1: TestCasesType = [
    # Rule 1 (b is Unio, returns a)
    (ZERO_UNIO, ZERO_UNIO, ZERO_UNIO, 'zero'),
    (ZERO_UNIO, AREO_UNIO, ZERO_UNIO, 'zero'),
    (AREO_UNIO, ZERO_UNIO, AREO_UNIO, 'areo'),
    (AREO_UNIO, AREO_UNIO, AREO_UNIO, 'areo'),
]

tests_omega_2: TestCasesType = [
    # Rule 1 (b is Unio, returns a)
    (1, ZERO_UNIO, 1, None),
    (1, AREO_UNIO, 1, None),
    (ZERO_UNIO, ZERO_UNIO, ZERO_UNIO, 'zero'), # a is Unio, b is Unio -> returns a
    # Rule 2 (a is Unio, b is DFI -> AREO_UNIO)
    (ZERO_UNIO, 1, AREO_UNIO, 'areo'),
    (AREO_UNIO, 1, AREO_UNIO, 'areo'),
    # Rule 3 (DFI - DFI), DFI={1}
    (1, 1, AREO_UNIO, 'areo'), # 1 <= 1 (cancellation) -> AREO_UNIO
]

tests_omega_3: TestCasesType = [
    # Rule 1
    (1, ZERO_UNIO, 1, None),
    (2, AREO_UNIO, 2, None),
    # Rule 2
    (ZERO_UNIO, 1, AREO_UNIO, 'areo'),
    (ZERO_UNIO, 2, AREO_UNIO, 'areo'),
    (AREO_UNIO, 1, AREO_UNIO, 'areo'),
    (AREO_UNIO, 2, AREO_UNIO, 'areo'),
    # Rule 3 (DFI - DFI), DFI={1,2}
    (2, 1, 1, None),                 # 2 > 1 -> 2-1=1
    (1, 1, AREO_UNIO, 'areo'),       # 1 <= 1 (cancellation)
    (2, 2, AREO_UNIO, 'areo'),       # 2 <= 2 (cancellation)
    (1, 2, AREO_UNIO, 'areo'),       # 1 <= 2 (underflow)
]

tests_omega_5: TestCasesType = [
    # Rule 1
    (4, ZERO_UNIO, 4, None),
    (1, AREO_UNIO, 1, None),
    # Rule 2
    (ZERO_UNIO, 1, AREO_UNIO, 'areo'),
    (ZERO_UNIO, 4, AREO_UNIO, 'areo'),
    (AREO_UNIO, 2, AREO_UNIO, 'areo'),
    # Rule 3 (DFI - DFI), DFI={1,2,3,4}
    (4, 1, 3, None),                 # 4 > 1 -> 3
    (3, 2, 1, None),                 # 3 > 2 -> 1
    (4, 3, 1, None),                 # 4 > 3 -> 1
    (2, 1, 1, None),                 # 2 > 1 -> 1
    (1, 1, AREO_UNIO, 'areo'),       # cancellation
    (4, 4, AREO_UNIO, 'areo'),       # cancellation
    (1, 4, AREO_UNIO, 'areo'),       # underflow
    (2, 3, AREO_UNIO, 'areo'),       # underflow
    (3, 4, AREO_UNIO, 'areo'),       # underflow
]

# --- Test Runner (Identical to test_avc_add_specific_cases.py's runner) ---
def run_all_tests():
    print("--- Starting avc_sub (v1.0 logic) Specific Case Tests (AVCA Core v1.2b) ---\n")
    
    test_suite: Dict[int, TestCasesType] = {
        1: tests_omega_1,
        2: tests_omega_2,
        3: tests_omega_3,
        5: tests_omega_5,
    }

    overall_passed = 0
    overall_failed = 0

    for omega_val, test_cases in test_suite.items():
        set_avca_omega(omega_val)
        print(f"--- Testing with Omega = {omega_val} ---")
        passed_count = 0
        failed_count = 0

        for i, (op_a, op_b, expected_val, expected_aspect) in enumerate(test_cases):
            test_id = f"Test {omega_val}.{i+1}"
            try:
                result = avc_sub(op_a, op_b)
                
                match = False
                # Check if result is Unio
                if isinstance(result, Unio):
                    # If expected_val is also Unio, check aspect
                    if isinstance(expected_val, Unio) and result.aspect == expected_aspect:
                        match = True
                # Check if result is int (DFI)
                elif isinstance(result, int):
                    # If expected_val is also int and matches, and no aspect was expected
                    if result == expected_val and expected_aspect is None:
                        match = True
                
                if match:
                    print(f"  {test_id}: PASS - avc_sub({op_a!r}, {op_b!r}) == {result!r}")
                    passed_count += 1
                else:
                    expected_repr = f"{expected_val!r}"
                    if isinstance(expected_val, Unio) and expected_aspect:
                         expected_repr = f"Unio('{expected_aspect}') (algebraically {expected_val!r})"
                    elif expected_aspect is not None and not isinstance(expected_val, Unio): 
                        expected_repr = f"DFI({expected_val}) (Error in test case: aspect {expected_aspect} unexpected)"

                    print(f"  {test_id}: FAIL - avc_sub({op_a!r}, {op_b!r})")
                    print(f"    Expected: {expected_repr}")
                    print(f"    Actual:   {result!r}")
                    failed_count += 1

            except Exception as e:
                print(f"  {test_id}: ERROR - avc_sub({op_a!r}, {op_b!r}) raised an unexpected exception: {e}")
                failed_count += 1
        
        print(f"  Omega={omega_val} Summary: {passed_count} passed, {failed_count} failed.")
        overall_passed += passed_count
        overall_failed += failed_count
        print("-" * 60)

    print(f"\n--- avc_sub (v1.0 logic) Specific Case Tests Completed ---")
    print(f"Overall Summary: {overall_passed} passed, {overall_failed} failed.")

if __name__ == "__main__":
    run_all_tests()