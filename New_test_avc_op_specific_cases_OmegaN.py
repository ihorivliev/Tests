# test_avc_add_specific_cases.py
# Purpose: To test specific cases of the avc_add (avc_add_v1_1 logic)
# operation from AVCA Core v1.2b for various Omega values.
# Focus: Unio identity, DFI sums, and DFI additive overflow to AREO_UNIO.

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

# --- avc_add (⊕_v1.1 logic from Appendix A of AVCA Core DraftV3) ---
def avc_add(a: AVCVal, b: AVCVal) -> AVCVal:
    """
    ⊕ : S_Ω × S_Ω → S_Ω (Cyclical Addition - v1.1 Refinement Logic)
    - Unio (any aspect object) is the universal additive identity.
    - DFI + DFI: Standard sum if < Ω; result is AREO_UNIO if sum ≥ Ω.
    """
    global Omega
    if Omega == 0: # Should be caught by _check_val if called from within other ops, but good for direct calls
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    _check_val(a, Omega)
    _check_val(b, Omega)

    if isinstance(a, Unio):
        return b  # Unio + X -> X
    if isinstance(b, Unio):
        return a  # X + Unio -> X

    # Both a and b are DFI integers
    standard_sum = a + b # type: ignore # Asserted to be int by _check_val
    if standard_sum < Omega:
        return standard_sum  # Result is DFI
    else:
        return AREO_UNIO     # DFI additive overflow yields AREO_UNIO (v1.1 refinement)

# --- Helper for setting Omega for testing ---
def set_avca_omega(omega_value: int):
    """Sets the global Omega parameter for AVCA operations."""
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega must be an integer >= 1.")
    Omega = omega_value
    # print(f"AVCA Omega set to: {Omega}") # Optional: for debugging

# --- Test Cases Definition ---
# Each test case: (operand_a, operand_b, expected_value, expected_aspect_if_unio or None)
TestCasesType = List[Tuple[AVCVal, AVCVal, AVCVal, Union[str, None]]]

tests_omega_1: TestCasesType = [
    (ZERO_UNIO, ZERO_UNIO, ZERO_UNIO, 'zero'), # U(z) + U(z) -> U(z) (result is b)
    (ZERO_UNIO, AREO_UNIO, AREO_UNIO, 'areo'), # U(z) + U(a) -> U(a)
    (AREO_UNIO, ZERO_UNIO, ZERO_UNIO, 'zero'), # U(a) + U(z) -> U(z)
    (AREO_UNIO, AREO_UNIO, AREO_UNIO, 'areo'), # U(a) + U(a) -> U(a)
]

tests_omega_2: TestCasesType = [
    # Unio identity
    (ZERO_UNIO, 1, 1, None),
    (1, ZERO_UNIO, 1, None),
    (AREO_UNIO, 1, 1, None),
    (1, AREO_UNIO, 1, None),
    (ZERO_UNIO, ZERO_UNIO, ZERO_UNIO, 'zero'),
    (ZERO_UNIO, AREO_UNIO, AREO_UNIO, 'areo'),
    # DFI + DFI (DFI={1})
    (1, 1, AREO_UNIO, 'areo'), # 1+1=2 >= Omega=2, overflow to AREO_UNIO
]

tests_omega_3: TestCasesType = [
    # Unio identity
    (ZERO_UNIO, 1, 1, None), (1, ZERO_UNIO, 1, None),
    (ZERO_UNIO, 2, 2, None), (2, ZERO_UNIO, 2, None),
    (AREO_UNIO, 1, 1, None), (1, AREO_UNIO, 1, None),
    (AREO_UNIO, 2, 2, None), (2, AREO_UNIO, 2, None),
    # DFI + DFI (DFI={1,2})
    (1, 1, 2, None),                      # 1+1=2 < 3
    (1, 2, AREO_UNIO, 'areo'),            # 1+2=3 >= Omega=3
    (2, 1, AREO_UNIO, 'areo'),            # 2+1=3 >= Omega=3
    (2, 2, AREO_UNIO, 'areo'),            # 2+2=4 >= Omega=3
]

tests_omega_5: TestCasesType = [
    # Unio identity
    (ZERO_UNIO, 1, 1, None), (1, ZERO_UNIO, 1, None),
    (AREO_UNIO, 4, 4, None), (4, AREO_UNIO, 4, None),
    # DFI + DFI (DFI={1,2,3,4})
    (1, 1, 2, None), (1, 2, 3, None), (1, 3, 4, None),
    (2, 2, 4, None),
    (1, 4, AREO_UNIO, 'areo'),            # 1+4=5 >= Omega=5
    (2, 3, AREO_UNIO, 'areo'),            # 2+3=5 >= Omega=5
    (3, 2, AREO_UNIO, 'areo'),            # 3+2=5 >= Omega=5
    (4, 1, AREO_UNIO, 'areo'),            # 4+1=5 >= Omega=5
    (2, 4, AREO_UNIO, 'areo'),            # 2+4=6 >= Omega=5
    (3, 3, AREO_UNIO, 'areo'),            # 3+3=6 >= Omega=5
    (3, 4, AREO_UNIO, 'areo'),            # 3+4=7 >= Omega=5
    (4, 4, AREO_UNIO, 'areo'),            # 4+4=8 >= Omega=5
]

# --- Test Runner ---
def run_all_tests():
    print("--- Starting avc_add (v1.1 logic) Specific Case Tests (AVCA Core v1.2b) ---\n")
    
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
                result = avc_add(op_a, op_b)
                
                match = False
                if isinstance(result, Unio):
                    if isinstance(expected_val, Unio) and result.aspect == expected_aspect:
                        match = True
                    # If expected_val is Unio but aspect is None, it implies algebraic Unio.
                    # Or if expected_val is not Unio but result is Unio (error).
                    # For simplicity in this test, we expect explicit aspect for Unio results.
                    elif isinstance(expected_val, Unio) and expected_aspect is None:
                         # This case means expected_val is an algebraic Unio, and result is Unio
                         # We need to check if expected_val.aspect matches result.aspect if we were stricter.
                         # However, the primary check is that it *is* Unio.
                         # For v1.1 add, DFI overflow *always* gives AREO_UNIO.
                         # If U+U->U, aspect is b.aspect.
                         # So if expected_val is Unio, expected_aspect should NOT be None.
                         # Let's refine test cases: if expected_val is Unio, expected_aspect must be 'zero' or 'areo'.
                         # For now, assume if expected_val is Unio, expected_aspect is correctly specified.
                         pass # Will fail below if aspects don't match.
                elif isinstance(result, int):
                    if result == expected_val and expected_aspect is None:
                        match = True
                
                if match:
                    print(f"  {test_id}: PASS - avc_add({op_a!r}, {op_b!r}) == {result!r}")
                    passed_count += 1
                else:
                    # Detailed failure message
                    expected_repr = f"{expected_val!r}"
                    if isinstance(expected_val, Unio) and expected_aspect:
                         expected_repr = f"Unio('{expected_aspect}') (algebraically {expected_val!r})"
                    elif expected_aspect is not None and not isinstance(expected_val, Unio): # DFI expected but aspect given
                        expected_repr = f"DFI({expected_val}) (Error in test case: aspect {expected_aspect} unexpected)"

                    print(f"  {test_id}: FAIL - avc_add({op_a!r}, {op_b!r})")
                    print(f"    Expected: {expected_repr}")
                    print(f"    Actual:   {result!r}")
                    failed_count += 1

            except Exception as e:
                print(f"  {test_id}: ERROR - avc_add({op_a!r}, {op_b!r}) raised an unexpected exception: {e}")
                failed_count += 1
        
        print(f"  Omega={omega_val} Summary: {passed_count} passed, {failed_count} failed.")
        overall_passed += passed_count
        overall_failed += failed_count
        print("-" * 60)

    print(f"\n--- avc_add (v1.1 logic) Specific Case Tests Completed ---")
    print(f"Overall Summary: {overall_passed} passed, {overall_failed} failed.")

if __name__ == "__main__":
    run_all_tests()