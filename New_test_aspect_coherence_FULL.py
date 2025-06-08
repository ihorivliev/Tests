# test_aspect_coherence.py
# Purpose: To exhaustively test the aspect-coherence rules for Unio results
# in AVCA Core v1.2b operations (add overflow, mul, div).
# This script checks for *exact object identity* (ZERO_UNIO or AREO_UNIO).

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
def run_tests():
    print("--- Starting Aspect-Coherence Tests (AVCA Core v1.2b) ---\n")
    
    omegas_to_test = [1, 2, 3, 5] 
    test_results: Dict[str, bool] = {"overall_status": True}

    def check(condition, testname, details=""):
        if not condition:
            print(f"  FAIL: {testname} - {details}")
            test_results["overall_status"] = False
            test_results[testname] = False # Mark specific test as failed
        elif testname not in test_results : # Only mark pass if not already failed
             test_results[testname] = True


    for omega_val in omegas_to_test:
        set_avca_omega(omega_val)
        print(f"--- Testing with Omega = {omega_val} ---")
        
        dfi_elements: List[int] = list(range(1, omega_val))
        unio_operands: List[Unio] = [ZERO_UNIO, AREO_UNIO]
        # For DFI operands, use a sample if DFI exists, or a placeholder if not critical
        sample_dfi1 = dfi_elements[0] if dfi_elements else 1 # Default to 1, _check_val will catch if Omega=1
        sample_dfi2 = dfi_elements[-1] if len(dfi_elements) > 1 else sample_dfi1

        # 1. Overflow in ⊕ (avc_add_v1_1) should always yield AREO_UNIO object
        print("  Section 1: Additive Overflow (DFI + DFI -> AREO_UNIO)")
        if omega_val > 1:
            # Case: sum == Omega
            if omega_val > 1 : # Ensure at least one DFI exists
                a1, b1 = 1, omega_val - 1
                if omega_val == 2 : a1, b1 = 1,1 # Special case for Omega=2, 1+1=2
                res_add_exact = avc_add(a1, b1)
                test_name_add_exact = f"Add_O{omega_val}_ExactOverflow ({a1}+{b1})"
                check(res_add_exact is AREO_UNIO, test_name_add_exact, f"Actual: {res_add_exact!r}")

            # Case: sum > Omega
            if len(dfi_elements) >= 2 : # e.g. Omega=3, DFI={1,2}, 2+2=4 > 3
                 a2, b2 = dfi_elements[-1], dfi_elements[-1] # Max_DFI + Max_DFI
                 res_add_over = avc_add(a2, b2)
                 test_name_add_over = f"Add_O{omega_val}_ClearOverflow ({a2}+{b2})"
                 check(res_add_over is AREO_UNIO, test_name_add_over, f"Actual: {res_add_over!r}")
            elif omega_val == 2: # Only 1+1 already tested for exact overflow
                pass # Already covered
            elif dfi_elements: # Only one DFI, e.g. Omega=2, use it for itself
                 a2, b2 = dfi_elements[0], dfi_elements[0]
                 if a2+b2 >= omega_val: # This will be true for O=2, 1+1=2
                    res_add_over = avc_add(a2, b2) # Already checked by exact for O=2
                    # test_name_add_over = f"Add_O{omega_val}_DFI0_SelfOverflow ({a2}+{b2})"
                    # check(res_add_over is AREO_UNIO, test_name_add_over, f"Actual: {res_add_over!r}")
        else: # Omega = 1
            print("    Skipping DFI additive overflow for Omega=1 (no DFI).")


        # 2. Multiplication (avc_mul_v1_2) Aspect Rules
        print("\n  Section 2: Multiplication Aspect Rules")
        # Rule 2.1: Any AREO_UNIO operand -> AREO_UNIO result
        ops_for_areo_dom = [(AREO_UNIO, AREO_UNIO), (AREO_UNIO, ZERO_UNIO), (ZERO_UNIO, AREO_UNIO)]
        if dfi_elements:
            ops_for_areo_dom.extend([(AREO_UNIO, sample_dfi1), (sample_dfi1, AREO_UNIO)])
        
        for op_a, op_b in ops_for_areo_dom:
            res_mul_au = avc_mul(op_a, op_b)
            tn_mul_au = f"Mul_O{omega_val}_AreoDominance ({op_a!r}*{op_b!r})"
            check(res_mul_au is AREO_UNIO, tn_mul_au, f"Actual: {res_mul_au!r}")

        # Rule 2.2: Else if any Unio (must be ZU) -> ZERO_UNIO result
        ops_for_zero_dom = [(ZERO_UNIO, ZERO_UNIO)]
        if dfi_elements:
            ops_for_zero_dom.extend([(ZERO_UNIO, sample_dfi1), (sample_dfi1, ZERO_UNIO)])

        for op_a, op_b in ops_for_zero_dom:
            res_mul_zu = avc_mul(op_a, op_b)
            tn_mul_zu = f"Mul_O{omega_val}_ZeroDominance ({op_a!r}*{op_b!r})"
            check(res_mul_zu is ZERO_UNIO, tn_mul_zu, f"Actual: {res_mul_zu!r}")
            
        # DFI * DFI overflow -> AREO_UNIO
        if omega_val > 1: # Requires DFI
            # Example: Omega=3, DFI={1,2}. 2*2=4 >= 3.
            # Example: Omega=5, DFI={1..4}. 2*3=6 >= 5.
            dfi_overflow_pairs = []
            if omega_val == 3: dfi_overflow_pairs = [(2,2)]
            if omega_val == 5: dfi_overflow_pairs = [(2,3), (3,3), (4,4)]
            # For a general case, find first pair that overflows
            found_dfi_mul_overflow = False
            if not dfi_overflow_pairs and len(dfi_elements) > 0:
                 for d1, d2 in itertools.product(dfi_elements, dfi_elements):
                     if d1 * d2 >= omega_val:
                         dfi_overflow_pairs.append((d1,d2))
                         found_dfi_mul_overflow = True
                         break
                     if found_dfi_mul_overflow: break
            
            for op_a, op_b in dfi_overflow_pairs:
                 res_mul_dfi_ov = avc_mul(op_a, op_b) # type: ignore
                 tn_mul_dfi_ov = f"Mul_O{omega_val}_DFIOverflow ({op_a!r}*{op_b!r})"
                 check(res_mul_dfi_ov is AREO_UNIO, tn_mul_dfi_ov, f"Actual: {res_mul_dfi_ov!r}")


        # 3. Division (avc_div_v1_2_variantB) Aspect Rules
        print("\n  Section 3: Division Aspect Rules (Variant B)")
        # Rule 3.1: Divisor is Unio -> AREO_UNIO result
        div_by_unio_dividends = [ZERO_UNIO, AREO_UNIO]
        if dfi_elements: div_by_unio_dividends.append(sample_dfi1)
        
        for op_a in div_by_unio_dividends:
            res_div_by_zu = avc_div(op_a, ZERO_UNIO)
            tn_div_by_zu = f"Div_O{omega_val}_DivByZU ({op_a!r}/{ZERO_UNIO!r})"
            check(res_div_by_zu is AREO_UNIO, tn_div_by_zu, f"Actual: {res_div_by_zu!r}")

            res_div_by_au = avc_div(op_a, AREO_UNIO)
            tn_div_by_au = f"Div_O{omega_val}_DivByAU ({op_a!r}/{AREO_UNIO!r})"
            check(res_div_by_au is AREO_UNIO, tn_div_by_au, f"Actual: {res_div_by_au!r}")

        # Rule 3.2: Else if Dividend is Unio (and divisor k is DFI) -> preserves dividend's aspect
        if dfi_elements:
            k = sample_dfi1 # Use a sample DFI as divisor
            
            res_zu_div_dfi = avc_div(ZERO_UNIO, k)
            tn_zu_div_dfi = f"Div_O{omega_val}_ZUDivDFI ({ZERO_UNIO!r}/{k!r})"
            check(res_zu_div_dfi is ZERO_UNIO, tn_zu_div_dfi, f"Actual: {res_zu_div_dfi!r}")

            res_au_div_dfi = avc_div(AREO_UNIO, k)
            tn_au_div_dfi = f"Div_O{omega_val}_AUDivDFI ({AREO_UNIO!r}/{k!r})"
            check(res_au_div_dfi is AREO_UNIO, tn_au_div_dfi, f"Actual: {res_au_div_dfi!r}")
            
        # DFI / DFI non-exact or out-of-range quotient -> AREO_UNIO
        if omega_val > 1: # Requires DFI
            dfi_div_problem_pairs = []
            # Non-exact cases
            if omega_val == 3: dfi_div_problem_pairs = [(1,2)] # 1/2 -> q=0, r=1
            if omega_val == 4: dfi_div_problem_pairs = [(1,2), (1,3), (2,3), (3,2)]
            if omega_val == 5: dfi_div_problem_pairs = [(1,2), (1,3), (1,4), (2,3), (2,4), (3,2), (3,4), (4,3)]
            # For a general case, find some pairs
            found_dfi_div_problem = False
            if not dfi_div_problem_pairs and len(dfi_elements) >= 2:
                d1, d2 = dfi_elements[0], dfi_elements[1] # e.g. 1, 2
                if d1 < d2 : # To get q=0 or non-exact
                    dfi_div_problem_pairs.append((d1,d2))
                elif len(dfi_elements) > 1 and d2 > 1: # Try d2/d1 if d1 is not 1 and d2<d1 for non-exact
                     if d1 % d2 != 0 : dfi_div_problem_pairs.append((d1,d2))


            for op_a, op_b in dfi_div_problem_pairs:
                res_div_dfi_prob = avc_div(op_a, op_b) # type: ignore
                tn_div_dfi_prob = f"Div_O{omega_val}_DFIProblem ({op_a!r}/{op_b!r})"
                check(res_div_dfi_prob is AREO_UNIO, tn_div_dfi_prob, f"Actual: {res_div_dfi_prob!r}")
        print("-" * 70)

    print("\n--- Aspect-Coherence Tests Completed ---")
    num_total_tests = len(test_results) -1 # -1 for 'overall_status'
    num_failed_tests = sum(1 for testname, passed in test_results.items() if testname != "overall_status" and not passed)

    if test_results["overall_status"]:
        print(f"ALL {num_total_tests} ASPECT-COHERENCE CHECKS PASSED.")
    else:
        print(f"ASPECT-COHERENCE FAILURES DETECTED: {num_failed_tests} out of {num_total_tests} checks failed.")
        print("Failed tests details:")
        for testname, passed in test_results.items():
            if testname != "overall_status" and not passed:
                # The script already printed failure details
                print(f"  - Recall failure for: {testname}")


if __name__ == "__main__":
    run_tests()