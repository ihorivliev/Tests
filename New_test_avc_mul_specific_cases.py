# test_avc_mul_specific_cases.py
# Purpose: To test specific cases of the avc_mul (v1.2 refinement logic)
# operation from AVCA Core v1.2b for various Omega values.
# Focus: Symmetric Unio aspect handling (Areo dominates), DFI products,
# and DFI multiplicative overflow to AREO_UNIO.

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

# --- avc_mul (⊗_v1.2 logic from Appendix A of AVCA Core DraftV3) ---
def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal:
    """
    ⊗ : S_Ω × S_Ω → S_Ω (Symmetric Aspect-Aware Multiplication - v1.2 Refinement Logic)
    - Unio-involved: AREO_UNIO if any Unio operand is Areo-aspected, else ZERO_UNIO.
    - DFI * DFI: Standard product if valid DFI (1 <= p < Ω); else AREO_UNIO.
    """
    global Omega
    if Omega == 0:
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    _check_val(a, Omega)
    _check_val(b, Omega)

    a_is_unio = isinstance(a, Unio)
    b_is_unio = isinstance(b, Unio)

    if a_is_unio or b_is_unio: # Rule 1: At least one operand is Unio
        # v1.2 Symmetric Rule: AREO_UNIO if any Unio factor is Areo-aspected, otherwise ZERO_UNIO.
        is_any_areo_aspected = (a_is_unio and a.aspect == "areo") or \
                               (b_is_unio and b.aspect == "areo") # type: ignore
        if is_any_areo_aspected:
            return AREO_UNIO
        else: # All Unio operands involved must be Zero-aspected
            return ZERO_UNIO
    else: # Rule 2: Both a and b are DFI integers
        # Types are guaranteed to be int by here
        standard_product = a * b # type: ignore
        # DFI product must be > 0 because DFI elements are >= 1.
        if 1 <= standard_product < Omega:
            return standard_product # Result is DFI
        else: # Multiplicative overflow (product >= Omega)
            return AREO_UNIO

# --- Helper for setting Omega for testing ---
def set_avca_omega(omega_value: int):
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega must be an integer >= 1.")
    Omega = omega_value

# --- Test Cases Definition ---
TestCasesType = List[Tuple[AVCVal, AVCVal, AVCVal, Union[str, None]]]

tests_omega_1: TestCasesType = [
    # Rule 1 (v1.2 Symmetric Unio aspect)
    (ZERO_UNIO, ZERO_UNIO, ZERO_UNIO, 'zero'), # ZU*ZU -> ZU
    (ZERO_UNIO, AREO_UNIO, AREO_UNIO, 'areo'), # ZU*AU -> AU (Areo dominates)
    (AREO_UNIO, ZERO_UNIO, AREO_UNIO, 'areo'), # AU*ZU -> AU (Areo dominates)
    (AREO_UNIO, AREO_UNIO, AREO_UNIO, 'areo'), # AU*AU -> AU
]

tests_omega_2: TestCasesType = [
    # Rule 1 (Unio-involved, v1.2 Symmetric Unio aspect)
    (ZERO_UNIO, 1, ZERO_UNIO, 'zero'),   # ZU * DFI -> ZU
    (1, ZERO_UNIO, ZERO_UNIO, 'zero'),   # DFI * ZU -> ZU
    (AREO_UNIO, 1, AREO_UNIO, 'areo'),   # AU * DFI -> AU
    (1, AREO_UNIO, AREO_UNIO, 'areo'),   # DFI * AU -> AU
    (ZERO_UNIO, AREO_UNIO, AREO_UNIO, 'areo'), # ZU * AU -> AU
    (AREO_UNIO, ZERO_UNIO, AREO_UNIO, 'areo'), # AU * ZU -> AU
    # Rule 2 (DFI * DFI), DFI={1}
    (1, 1, 1, None),                     # 1*1=1 < Omega=2
]

tests_omega_3: TestCasesType = [
    # Rule 1
    (ZERO_UNIO, 1, ZERO_UNIO, 'zero'),
    (1, ZERO_UNIO, ZERO_UNIO, 'zero'),
    (ZERO_UNIO, 2, ZERO_UNIO, 'zero'),
    (2, ZERO_UNIO, ZERO_UNIO, 'zero'),
    (AREO_UNIO, 1, AREO_UNIO, 'areo'),
    (1, AREO_UNIO, AREO_UNIO, 'areo'),
    (AREO_UNIO, 2, AREO_UNIO, 'areo'),
    (2, AREO_UNIO, AREO_UNIO, 'areo'),
    # Rule 2 (DFI * DFI), DFI={1,2}
    (1, 1, 1, None),                     # 1*1=1 < 3
    (1, 2, 2, None),                     # 1*2=2 < 3
    (2, 1, 2, None),                     # 2*1=2 < 3
    (2, 2, AREO_UNIO, 'areo'),            # 2*2=4 >= Omega=3 (overflow to AREO_UNIO)
]

tests_omega_5: TestCasesType = [
    # Rule 1
    (ZERO_UNIO, 3, ZERO_UNIO, 'zero'),
    (4, ZERO_UNIO, ZERO_UNIO, 'zero'),
    (AREO_UNIO, 3, AREO_UNIO, 'areo'),
    (4, AREO_UNIO, AREO_UNIO, 'areo'),
    # Rule 2 (DFI * DFI), DFI={1,2,3,4}
    (1, 4, 4, None),                     # 1*4=4 < 5
    (2, 2, 4, None),                     # 2*2=4 < 5
    (2, 3, AREO_UNIO, 'areo'),            # 2*3=6 >= Omega=5
    (3, 2, AREO_UNIO, 'areo'),            # 3*2=6 >= Omega=5
    (3, 3, AREO_UNIO, 'areo'),            # 3*3=9 >= Omega=5
    (4, 2, AREO_UNIO, 'areo'),            # 4*2=8 >= Omega=5
    (4, 4, AREO_UNIO, 'areo'),            # 4*4=16 >= Omega=5
]

# --- Test Runner (Identical to previous test scripts' runner) ---
def run_all_tests():
    print("--- Starting avc_mul (v1.2 logic) Specific Case Tests (AVCA Core v1.2b) ---\n")
    
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
                result = avc_mul(op_a, op_b)
                
                match = False
                if isinstance(result, Unio):
                    if isinstance(expected_val, Unio) and result.aspect == expected_aspect:
                        match = True
                elif isinstance(result, int):
                    if result == expected_val and expected_aspect is None:
                        match = True
                
                if match:
                    print(f"  {test_id}: PASS - avc_mul({op_a!r}, {op_b!r}) == {result!r}")
                    passed_count += 1
                else:
                    expected_repr = f"{expected_val!r}"
                    if isinstance(expected_val, Unio) and expected_aspect:
                         expected_repr = f"Unio('{expected_aspect}') (algebraically {expected_val!r})"
                    elif expected_aspect is not None and not isinstance(expected_val, Unio): 
                        expected_repr = f"DFI({expected_val}) (Error in test case: aspect {expected_aspect} unexpected)"

                    print(f"  {test_id}: FAIL - avc_mul({op_a!r}, {op_b!r})")
                    print(f"    Expected: {expected_repr}")
                    print(f"    Actual:   {result!r}")
                    failed_count += 1

            except Exception as e:
                print(f"  {test_id}: ERROR - avc_mul({op_a!r}, {op_b!r}) raised an unexpected exception: {e}")
                failed_count += 1
        
        print(f"  Omega={omega_val} Summary: {passed_count} passed, {failed_count} failed.")
        overall_passed += passed_count
        overall_failed += failed_count
        print("-" * 60)

    print(f"\n--- avc_mul (v1.2 logic) Specific Case Tests Completed ---")
    print(f"Overall Summary: {overall_passed} passed, {overall_failed} failed.")

if __name__ == "__main__":
    run_all_tests()