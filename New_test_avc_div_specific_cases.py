# test_avc_div_specific_cases.py
# Purpose: To test specific and exhaustive cases of the avc_div (v1.2 Variant B logic)
# operation from AVCA Core v1.2b for various Omega values.
# Focus: Rules B1 (Divisor Unio), B2 (Dividend Unio/DFI), and B3 (DFI/DFI all cases).

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

# --- avc_div (⊘_v1.2B logic from Appendix A of AVCA Core DraftV3) ---
def avc_div(a: AVCVal, b: AVCVal) -> AVCVal:
    """
    ⊘ : S_Ω × S_Ω → S_Ω (Symmetric Aspect-Aware Division - v1.2 Variant B Refinement Logic)
    - Rule B1: Divisor b is Unio (any aspect object) -> AREO_UNIO.
    - Rule B2: Dividend a is Unio (any aspect) AND Divisor b is DFI -> Preserves Dividend's Unio aspect.
    - Rule B3: DFI / DFI -> Standard quotient if exact and valid DFI; else AREO_UNIO.
    """
    global Omega
    if Omega == 0:
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    _check_val(a, Omega)
    _check_val(b, Omega)

    # Rule B1: Divisor b is Unio (any aspect object)
    if isinstance(b, Unio):
        return AREO_UNIO

    # Rule B2: Dividend a is Unio (any aspect object) AND Divisor b is DFI
    # (This rule is only reached if b is not Unio, so b must be DFI here)
    if isinstance(a, Unio):
        if a.aspect == "zero": # type: ignore
            return ZERO_UNIO # Preserves "0 / k = 0"
        else: # a.aspect == "areo"
            return AREO_UNIO

    # Rule B3: Both a and b are DFI integers
    # At this point, a and b are guaranteed to be DFI integers by _check_val and preceding checks.
    # b_val is also guaranteed to be >= 1 by _check_val (for Omega > 1).
    
    quotient, remainder = divmod(a, b) # type: ignore

    if remainder == 0 and (1 <= quotient < Omega):
        return quotient # Result is a valid DFI element
    else:
        # Non-exact division, or quotient is 0, or quotient >= Omega
        return AREO_UNIO
        
# --- Helper for setting Omega for testing ---
def set_avca_omega(omega_value: int):
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega must be an integer >= 1.")
    Omega = omega_value

# --- Test Cases Definition ---
TestCasesType = List[Tuple[AVCVal, AVCVal, AVCVal, Union[str, None]]]

def generate_dfi_test_cases(omega: int) -> TestCasesType:
    if omega <= 1:
        return []
    
    dfi_elements = list(range(1, omega))
    dfi_tests: TestCasesType = []

    for a_val in dfi_elements:
        for b_val in dfi_elements:
            q, r = divmod(a_val, b_val)
            if r == 0 and (1 <= q < omega):
                dfi_tests.append((a_val, b_val, q, None))
            else:
                dfi_tests.append((a_val, b_val, AREO_UNIO, 'areo'))
    return dfi_tests

# --- Test Runner ---
def run_all_tests():
    print("--- Starting avc_div (v1.2 Variant B logic) Specific Case Tests (AVCA Core v1.2b) ---\n")
    
    # Omega values to test
    omegas_to_test = [1, 2, 3, 4, 5] 
    # Could add more, e.g., a prime like 7 for more DFI variety

    overall_passed = 0
    overall_failed = 0

    for omega_val in omegas_to_test:
        set_avca_omega(omega_val)
        print(f"--- Testing with Omega = {omega_val} ---")
        passed_count = 0
        failed_count = 0
        
        current_test_cases: TestCasesType = []
        dfi_vals = list(range(1, omega_val))

        # Category 1: Rule B1 (Divisor is Unio)
        rule_b1_tests: TestCasesType = []
        operands_for_a_rule_b1 = dfi_vals[:1] + [ZERO_UNIO, AREO_UNIO] # Sample DFI, ZU, AU
        if not dfi_vals: # For Omega=1, DFI is empty
            operands_for_a_rule_b1 = [ZERO_UNIO, AREO_UNIO]

        for op_a_b1 in operands_for_a_rule_b1:
            rule_b1_tests.append((op_a_b1, ZERO_UNIO, AREO_UNIO, 'areo'))
            rule_b1_tests.append((op_a_b1, AREO_UNIO, AREO_UNIO, 'areo'))
        
        current_test_cases.extend(rule_b1_tests)

        # Category 2: Rule B2 (Dividend Unio, Divisor DFI)
        rule_b2_tests: TestCasesType = []
        if dfi_vals: # Only if DFI exists
            for dfi_b_b2 in dfi_vals:
                rule_b2_tests.append((ZERO_UNIO, dfi_b_b2, ZERO_UNIO, 'zero'))
                rule_b2_tests.append((AREO_UNIO, dfi_b_b2, AREO_UNIO, 'areo'))
        current_test_cases.extend(rule_b2_tests)

        # Category 3: Rule B3 (DFI / DFI) - Exhaustive for small Omega
        rule_b3_tests = generate_dfi_test_cases(omega_val)
        current_test_cases.extend(rule_b3_tests)


        for i, (op_a, op_b, expected_val, expected_aspect) in enumerate(current_test_cases):
            test_id = f"Test {omega_val}.{i+1}"
            # Determine rule being tested (for logging clarity, approximate)
            rule_tag = "Unknown"
            if isinstance(op_b, Unio):
                rule_tag = "B1 (Divisor Unio)"
            elif isinstance(op_a, Unio) and isinstance(op_b, int):
                rule_tag = "B2 (Dividend Unio, Divisor DFI)"
            elif isinstance(op_a, int) and isinstance(op_b, int):
                rule_tag = "B3 (DFI/DFI)"

            try:
                result = avc_div(op_a, op_b)
                
                match = False
                if isinstance(result, Unio):
                    if isinstance(expected_val, Unio) and result.aspect == expected_aspect:
                        match = True
                elif isinstance(result, int):
                    if result == expected_val and expected_aspect is None:
                        match = True
                
                if match:
                    print(f"  {test_id} [{rule_tag}]: PASS - avc_div({op_a!r}, {op_b!r}) == {result!r}")
                    passed_count += 1
                else:
                    expected_repr = f"{expected_val!r}"
                    if isinstance(expected_val, Unio) and expected_aspect:
                         expected_repr = f"Unio('{expected_aspect}') (algebraically {expected_val!r})"
                    elif expected_aspect is not None and not isinstance(expected_val, Unio): 
                        expected_repr = f"DFI({expected_val}) (Error in test case: aspect {expected_aspect} unexpected)"

                    print(f"  {test_id} [{rule_tag}]: FAIL - avc_div({op_a!r}, {op_b!r})")
                    print(f"    Expected: {expected_repr}")
                    print(f"    Actual:   {result!r}")
                    failed_count += 1

            except Exception as e:
                print(f"  {test_id} [{rule_tag}]: ERROR - avc_div({op_a!r}, {op_b!r}) raised an unexpected exception: {e}")
                failed_count += 1
        
        print(f"  Omega={omega_val} Summary: {passed_count} passed, {failed_count} failed.")
        overall_passed += passed_count
        overall_failed += failed_count
        print("-" * 70) # Wider separator

    print(f"\n--- avc_div (v1.2 Variant B logic) Specific Case Tests Completed ---")
    print(f"Overall Summary: {overall_passed} passed, {overall_failed} failed.")

if __name__ == "__main__":
    run_all_tests()