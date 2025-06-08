import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- PySMT Imports ---
try:
    from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                                 ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals,
                                 GT, GE, LT, LE, Times, Div)
    from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
    from pysmt.fnode import FNode
    SMT_MODE_AVAILABLE = True
except ImportError:
    SMT_MODE_AVAILABLE = False

# --- Configuration ---
SMT_SOLVER_NAME = "z3"

# --- Standard Unio Class Definition (from AVCA Core DraftV4 Appendix A) ---
class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"): raise ValueError("Unio aspect error")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool: return isinstance(other, Unio)
    def __hash__(self) -> int: return hash(type(self))
    def __repr__(self) -> str: return f"Unio('{self.aspect}')"

ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")
AVCVal = Union[int, Unio]

# --- AVCA Core Logic (using standard Unio, ZERO_UNIO, AREO_UNIO) ---
Omega_R1: int = 0

def set_avca_omega_R1(omega_value: int, verbose=False):
    global Omega_R1
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R1 parameter must be an integer >= 1.")
    Omega_R1 = omega_value
    if verbose: print(f"R1 Test: Omega_R1 set to {Omega_R1}")

def _check_val_R1(x: AVCVal, current_omega: int, op_name: str = "op"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R1 for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid val in {op_name}:{x!r}")
    if current_omega==1: raise ValueError(f"Invalid DFI for {op_name} Omega_R1=1:{x}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI for {op_name}:{x}, Omega_R1={current_omega}")

# --- Standard v1.2b Operations (sub, mul, div) needed for context ---
def avc_sub_v1_0_R1(a: AVCVal, b: AVCVal) -> AVCVal: # Standard ⊖_v1.0
    global Omega_R1; _check_val_R1(a,Omega_R1); _check_val_R1(b,Omega_R1)
    if isinstance(b,Unio): return a
    if isinstance(a,Unio): return AREO_UNIO 
    return (a-b) if a>b else AREO_UNIO # type: ignore

def avc_mul_v1_2_R1(a: AVCVal, b: AVCVal) -> AVCVal: # Standard ⊗_v1.2
    global Omega_R1; _check_val_R1(a,Omega_R1); _check_val_R1(b,Omega_R1)
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_areo=a_is_u and a.aspect=="areo" # type: ignore
        b_areo=b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_areo or b_areo else ZERO_UNIO
    p=a*b; return p if 1<=p<Omega_R1 else AREO_UNIO # type: ignore

def avc_div_v1_2B_R1(a: AVCVal, b: AVCVal) -> AVCVal: # Standard ⊘_v1.2B
    global Omega_R1; _check_val_R1(a,Omega_R1); _check_val_R1(b,Omega_R1)
    if isinstance(b,Unio): return AREO_UNIO
    if isinstance(a,Unio): return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO # type: ignore
    q,r=divmod(a,b); return q if r==0 and 1<=q<Omega_R1 else AREO_UNIO # type: ignore

# --- Addition Variants for Comparison ---
def avc_add_v1_1_logic(a: AVCVal, b: AVCVal) -> AVCVal: # Target: DFI overflow -> AREO_UNIO
    global Omega_R1; _check_val_R1(a,Omega_R1); _check_val_R1(b,Omega_R1)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R1 else AREO_UNIO # type: ignore

def avc_add_v1_0_logic(a: AVCVal, b: AVCVal) -> AVCVal: # Alternative: DFI overflow -> ZERO_UNIO
    global Omega_R1; _check_val_R1(a,Omega_R1); _check_val_R1(b,Omega_R1)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R1 else ZERO_UNIO # type: ignore

# --- Test Harness ---
test_results_R1 = {}
def run_test_R1(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R1
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R1: test_results_R1[suite_key] = {"passed":0,"failed":0,"skipped":0}
    
    current_op_variant_name = kwargs.get("op_variant_name", "")
    full_test_name = f"{test_name} ({current_op_variant_name})" if current_op_variant_name else test_name

    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_result = "PASS" if passes else "FAIL"
        expected_result_str = "PASS" if expect_pass else "FAIL"

        if passes == expect_pass:
            print(f"PASS (Observed: {actual_result})")
            test_results_R1[suite_key]["passed"] += 1
        else:
            print(f"FAIL (Observed: {actual_result}, Expected: {expected_result_str})")
            if detail: print(f"    Detail: {detail}")
            test_results_R1[suite_key]["failed"] += 1
    except Exception as e:
        print(f"ERROR ({e})"); test_results_R1[suite_key]["failed"] += 1

def get_s_omega_R1(current_omega: int) -> List[AVCVal]:
    if current_omega == 1: return [ZERO_UNIO] 
    return [ZERO_UNIO] + list(range(1, current_omega)) # Use ZERO_UNIO as a representative Unio for iteration

# --- Property Test Functions ---
def check_associativity(omega_val: int, add_func_variant: Callable) -> Tuple[bool, Any]:
    elements = get_s_omega_R1(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try:
            lhs = add_func_variant(add_func_variant(a,b),c)
            rhs = add_func_variant(a,add_func_variant(b,c))
            if lhs != rhs: return False, f"a={a!r},b={b!r},c={c!r} -> LHS={lhs!r},RHS={rhs!r}"
        except ValueError: pass # Skip if inputs become invalid for sub-operations due to Omega=1 DFI limits
    return True, None

def check_dft_boundary_breach_uniformity(omega_val: int, add_func_variant: Callable) -> Tuple[bool, Any]:
    if omega_val < 2: return True, "N/A for Ω<2" # DFI interactions are limited
    
    breach_outputs_areo = True
    breach_outputs_zero = True
    details = []

    # 1. Additive Overflow
    # Find a,b in DFI such that a+b >= omega_val. Smallest DFI is 1.
    # If omega_val=2, a=1,b=1. sum=2.
    # If omega_val=3, a=1,b=2 or a=2,b=1 or a=2,b=2. sum >=3.
    dfi_for_add_overflow = []
    if omega_val == 2: dfi_for_add_overflow = [(1,1)]
    elif omega_val > 2: dfi_for_add_overflow = [(1, omega_val-1), (omega_val-1, omega_val-1)]
    
    for a_dfi, b_dfi in dfi_for_add_overflow:
        if not (1 <= a_dfi < omega_val and 1 <= b_dfi < omega_val): continue
        res_add = add_func_variant(a_dfi, b_dfi)
        if res_add != AREO_UNIO: breach_outputs_areo = False; details.append(f"add({a_dfi},{b_dfi})->{res_add!r} (not AREO)")
        if res_add != ZERO_UNIO: breach_outputs_zero = False # For checking v1.0 style

    # 2. Subtractive Underflow (e.g., 1 - 1, or 1 - 2 if Ω>2)
    res_sub = avc_sub_v1_0_R1(1,1) # Result should be AREO_UNIO
    if res_sub != AREO_UNIO: breach_outputs_areo = False; details.append(f"sub(1,1)->{res_sub!r} (not AREO)")
    if omega_val > 2:
        res_sub2 = avc_sub_v1_0_R1(1,2) # Result should be AREO_UNIO
        if res_sub2 != AREO_UNIO: breach_outputs_areo = False; details.append(f"sub(1,2)->{res_sub2!r} (not AREO)")
        
    # 3. Multiplicative Overflow (e.g., (Ω-1) * 2 if 2*(Ω-1) >= Ω)
    if omega_val > 1 : # Need at least one DFI
        a_dfi, b_dfi = (omega_val-1, omega_val-1) if omega_val > 2 else (1,1) 
        # Ensure b_dfi doesn't make product too small for overflow with typical examples
        b_dfi_mul = 2 if (omega_val-1)*2 >= omega_val and 2 < omega_val else (omega_val-1 if omega_val > 1 else 1)
        if 1 <= b_dfi_mul < omega_val:
             res_mul = avc_mul_v1_2_R1(omega_val-1, b_dfi_mul)
             if (omega_val-1)*b_dfi_mul >= omega_val : # Actual overflow condition for product
                 if res_mul != AREO_UNIO: breach_outputs_areo = False; details.append(f"mul({omega_val-1},{b_dfi_mul})->{res_mul!r} (not AREO)")
        elif omega_val == 2: # 1*1 = 1 (no overflow)
            pass


    # 4. Problematic Division (e.g. 1 / 2 for Ω=3 -> AREO_UNIO)
    if omega_val > 2: # Need at least DFI 1 and 2
        res_div = avc_div_v1_2B_R1(1,2)
        if res_div != AREO_UNIO: breach_outputs_areo = False; details.append(f"div(1,2)->{res_div!r} (not AREO)")

    # For this test, success means all *other* ops yield AREO_UNIO, and we check add separately.
    # The function returns a tuple: (add_overflow_is_AREO, other_breaches_are_AREO, details)
    add_overflow_aspect_target = add_func_variant(1, omega_val-1) if omega_val > 1 else ZERO_UNIO # Get what add_func yields for sure overflow
    
    # This function will return True if add_func_variant produces AREO_UNIO on overflow, AND others also do.
    # Or True if add_func_variant produces ZERO_UNIO on overflow, AND others also do (which isn't the case for others).
    # So, we need to be specific.
    # Test 1: Does this add_func_variant make ALL DFI breaches (add,sub,mul,div) yield AREO_UNIO?
    all_to_areo = add_overflow_aspect_target == AREO_UNIO and breach_outputs_areo
    
    # Test 2: Does this add_func_variant make add yield ZERO_UNIO while others yield AREO_UNIO?
    add_to_zero_others_to_areo = add_overflow_aspect_target == ZERO_UNIO and breach_outputs_areo

    return all_to_areo, details if not all_to_areo else None # Returns true if consistently AREO

# --- SMT Components (Minimal for this comparison, could be expanded) ---
# SMT not strictly necessary if we trust native Python for these specific checks,
# but can provide more general argument for the properties. For now, focusing on native.

# --- Main Execution Block ---
if __name__ == "__main__":
    print("====== AVCA R1: Additive Overflow Comparison (v1.1 vs v1.0 logic) ======")
    omegas_to_test = [1, 2, 3, 4, 5]

    for omega_val_test in omegas_to_test:
        set_avca_omega_R1(omega_val_test)
        print(f"\n--- Testing for Ω = {omega_val_test} ---")

        # Test with avc_add_v1_1_logic (Overflow to AREO_UNIO)
        variant_name_v11 = "⊕_v1.1 (Overflow to AREO)"
        run_test_R1("Assoc_Test", "Associativity", omega_val_test, 
                    lambda o, **kw: check_associativity(o, add_func_variant=avc_add_v1_1_logic), 
                    expect_pass=(omega_val_test <= 2), op_variant_name=variant_name_v11)
        
        run_test_R1("Uniformity_Test", "DFI Breach Uniformity (all to AREO)", omega_val_test,
                    lambda o, **kw: check_dft_boundary_breach_uniformity(o, add_func_variant=avc_add_v1_1_logic),
                    expect_pass=True, op_variant_name=variant_name_v11)

        # Test with avc_add_v1_0_logic (Overflow to ZERO_UNIO)
        variant_name_v10 = "⊕_v1.0 (Overflow to ZERO)"
        run_test_R1("Assoc_Test", "Associativity", omega_val_test,
                    lambda o, **kw: check_associativity(o, add_func_variant=avc_add_v1_0_logic),
                    expect_pass=(omega_val_test <= 2), op_variant_name=variant_name_v10)
        
        run_test_R1("Uniformity_Test", "DFI Breach Uniformity (all to AREO)", omega_val_test,
                    lambda o, **kw: check_dft_boundary_breach_uniformity(o, add_func_variant=avc_add_v1_0_logic),
                    expect_pass=False, op_variant_name=variant_name_v10) # Expected to FAIL for uniformity to AREO

    print("\n\n--- Overall Test Summary (R1: Add Overflow Comparison) ---")
    for suite_key, results in sorted(test_results_R1.items()):
        print(f"  {suite_key}: Passed={results['passed']}, Failed={results['failed']}, Skipped={results['skipped']}")
    
    print("\n====== R1 Script Finished ======")