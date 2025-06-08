import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- PySMT Imports (Included for completeness if SMT were added, but not used in this native script) ---
# try:
#     from pysmt.shortcuts import Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff
#     from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
#     from pysmt.fnode import FNode
#     SMT_MODE_AVAILABLE = True
# except ImportError:
#     SMT_MODE_AVAILABLE = False

# --- Standard Unio Class Definition (from AVCA Core DraftV4 Appendix A) ---
class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"): raise ValueError("Unio aspect error")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool: # Algebraic equivalence
        return isinstance(other, Unio)
    def __hash__(self) -> int: return hash(type(self))
    def __repr__(self) -> str: return f"Unio('{self.aspect}')"

ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")
AVCVal = Union[int, Unio]

# --- AVCA Core Logic (using standard Unio, ZERO_UNIO, AREO_UNIO) ---
Omega_R1_Refined: int = 0

def set_avca_omega_R1_Refined(omega_value: int, verbose=False):
    global Omega_R1_Refined
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R1_Refined parameter must be an integer >= 1.")
    Omega_R1_Refined = omega_value
    if verbose: print(f"R1 Refined Test: Omega_R1_Refined set to {Omega_R1_Refined}")

def _check_val_R1_Refined(x: AVCVal, current_omega: int, op_name: str = "op"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R1_Refined for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid val in {op_name}:{x!r}")
    if current_omega==1: raise ValueError(f"Invalid DFI for {op_name} Omega_R1_Refined=1:{x}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI for {op_name}:{x}, Omega_R1_Refined={current_omega}")

# --- Standard v1.2b Operations (sub, mul, div) needed for context ---
def avc_sub_v1_0_R1_Refined(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R1_Refined; _check_val_R1_Refined(a,Omega_R1_Refined); _check_val_R1_Refined(b,Omega_R1_Refined)
    if isinstance(b,Unio): return a
    if isinstance(a,Unio): return AREO_UNIO 
    return (a-b) if a>b else AREO_UNIO # type: ignore

def avc_mul_v1_2_R1_Refined(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R1_Refined; _check_val_R1_Refined(a,Omega_R1_Refined); _check_val_R1_Refined(b,Omega_R1_Refined)
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_areo=a_is_u and a.aspect=="areo" # type: ignore
        b_areo=b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_areo or b_areo else ZERO_UNIO
    p=a*b; return p if 1<=p<Omega_R1_Refined else AREO_UNIO # type: ignore

def avc_div_v1_2B_R1_Refined(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R1_Refined; _check_val_R1_Refined(a,Omega_R1_Refined); _check_val_R1_Refined(b,Omega_R1_Refined)
    if isinstance(b,Unio): return AREO_UNIO
    if isinstance(a,Unio): return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO # type: ignore
    q,r=divmod(a,b); return q if r==0 and 1<=q<Omega_R1_Refined else AREO_UNIO # type: ignore

# --- Addition Variants for Comparison ---
def avc_add_v1_1_logic_refined(a: AVCVal, b: AVCVal) -> AVCVal: # Target: DFI overflow -> AREO_UNIO
    global Omega_R1_Refined; _check_val_R1_Refined(a,Omega_R1_Refined); _check_val_R1_Refined(b,Omega_R1_Refined)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R1_Refined else AREO_UNIO # type: ignore

def avc_add_v1_0_logic_refined(a: AVCVal, b: AVCVal) -> AVCVal: # Alternative: DFI overflow -> ZERO_UNIO
    global Omega_R1_Refined; _check_val_R1_Refined(a,Omega_R1_Refined); _check_val_R1_Refined(b,Omega_R1_Refined)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R1_Refined else ZERO_UNIO # type: ignore

# --- Test Harness ---
test_results_R1_refined = {}
def run_test_R1_refined(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R1_refined
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R1_refined: test_results_R1_refined[suite_key] = {"passed":0,"failed":0,"skipped":0}
    
    current_op_variant_name = kwargs.get("op_variant_name", "")
    full_test_name = f"{test_name} ({current_op_variant_name})" if current_op_variant_name else test_name

    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_result_str = "PASS" if passes else "FAIL"
        expected_result_str = "PASS" if expect_pass else "FAIL"

        if passes == expect_pass:
            print(f"PASS (Observed: {actual_result_str})")
            test_results_R1_refined[suite_key]["passed"] += 1
        else:
            print(f"FAIL (Observed: {actual_result_str}, Expected: {expected_result_str})")
            if detail: print(f"    Detail: {detail}")
            test_results_R1_refined[suite_key]["failed"] += 1
    except Exception as e:
        print(f"ERROR ({e})"); test_results_R1_refined[suite_key]["failed"] += 1

def get_s_omega_R1_refined(current_omega: int) -> List[AVCVal]:
    if current_omega == 1: return [ZERO_UNIO] 
    return [ZERO_UNIO] + list(range(1, current_omega))

# --- Property Test Functions ---
def check_associativity_refined(omega_val: int, add_func_variant: Callable) -> Tuple[bool, Any]:
    elements = get_s_omega_R1_refined(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try: # Added try-except for potential _check_val issues with Omega=1 fixed elements
            lhs = add_func_variant(add_func_variant(a,b),c)
            rhs = add_func_variant(a,add_func_variant(b,c))
            if lhs != rhs: # Uses Unio.__eq__ for algebraic equivalence
                return False, f"a={a!r},b={b!r},c={c!r} -> LHS={lhs!r},RHS={rhs!r}"
        except ValueError as e: # Catch _check_val errors, e.g. DFI for Omega=1
            if omega_val == 1 and isinstance(a,Unio) and isinstance(b,Unio) and isinstance(c,Unio):
                pass # U+U+U is fine for Omega=1
            else:
                return False, f"ValueError during associativity: a={a!r},b={b!r},c={c!r} -> {e}"
    return True, None

def check_dft_boundary_breach_STRICT_OBJECT_uniformity_to_AREO(omega_val: int, add_func_variant: Callable) -> Tuple[bool, Any]:
    if omega_val < 2:
        return True, "N/A or vacuously true for Ω<2 (limited/no DFI breaches)"

    all_breaches_are_strictly_AREO = True
    details = []
    add_op_name = add_func_variant.__name__

    # 1. Additive Overflow (from the variant being tested)
    dfi_add_pairs_for_overflow = []
    if omega_val == 2: dfi_add_pairs_for_overflow.append((1,1))
    elif omega_val > 2: 
        dfi_add_pairs_for_overflow.extend([(1, omega_val-1), (omega_val-1, omega_val-1)])
        if omega_val == 3: dfi_add_pairs_for_overflow.append((2,2)) # Ensure multiple diverse overflows

    for a_dfi, b_dfi in dfi_add_pairs_for_overflow:
        if not (1 <= a_dfi < omega_val and 1 <= b_dfi < omega_val): continue
        res_add = add_func_variant(a_dfi, b_dfi)
        if not (res_add is AREO_UNIO): # Strict object identity check
            all_breaches_are_strictly_AREO = False
            details.append(f"{add_op_name}({a_dfi},{b_dfi}) -> {res_add!r} (IS NOT object AREO_UNIO)")
            # No break, collect all add discrepancies for this variant
    
    # If the add variant itself fails the strict AREO_UNIO output for its overflows,
    # then the overall strict uniformity property is already false.
    if not all_breaches_are_strictly_AREO:
        return False, ", ".join(details)

    # 2. Subtractive Underflow/Cancellation (standard avc_sub_v1_0_R1_Refined)
    # These should always yield the AREO_UNIO object by v1.0 spec.
    dfi_sub_pairs_breach = []
    if omega_val == 2: dfi_sub_pairs_breach.append((1,1))
    elif omega_val > 2: dfi_sub_pairs_breach.extend([(1,1), (1,2), (omega_val-1, omega_val-1)])
    
    for a_dfi, b_dfi in dfi_sub_pairs_breach:
        if not (1 <= a_dfi < omega_val and 1 <= b_dfi < omega_val): continue
        res_sub = avc_sub_v1_0_R1_Refined(a_dfi, b_dfi)
        if not (res_sub is AREO_UNIO):
            all_breaches_are_strictly_AREO = False
            details.append(f"avc_sub_v1_0_R1_Refined({a_dfi},{b_dfi}) -> {res_sub!r} (not strictly AREO_UNIO)")
            break 
    if not all_breaches_are_strictly_AREO: return False, ", ".join(details)

    # 3. Multiplicative Overflow (standard avc_mul_v1_2_R1_Refined)
    dfi_mul_pairs_for_overflow = []
    if omega_val == 3: dfi_mul_pairs_for_overflow = [(2,2)] 
    elif omega_val == 4: dfi_mul_pairs_for_overflow = [(2,2), (2,3), (3,3)]
    elif omega_val == 5: dfi_mul_pairs_for_overflow = [(2,3), (3,2), (3,3), (4,2), (2,4), (4,3), (3,4), (4,4)]
    elif omega_val > 1 and (omega_val-1)*(omega_val-1) >= omega_val: # General large case
         if (omega_val-1, omega_val-1) not in dfi_mul_pairs_for_overflow :
            dfi_mul_pairs_for_overflow.append( (omega_val-1, omega_val-1) )
    
    for a_dfi, b_dfi in dfi_mul_pairs_for_overflow:
        if not (1 <= a_dfi < omega_val and 1 <= b_dfi < omega_val): continue
        if a_dfi * b_dfi < omega_val: continue # Only test actual overflow products
        res_mul = avc_mul_v1_2_R1_Refined(a_dfi, b_dfi)
        if not (res_mul is AREO_UNIO):
            all_breaches_are_strictly_AREO = False
            details.append(f"avc_mul_v1_2_R1_Refined({a_dfi},{b_dfi}) product {a_dfi*b_dfi} -> {res_mul!r} (not strictly AREO_UNIO)")
            break
    if not all_breaches_are_strictly_AREO: return False, ", ".join(details)

    # 4. Problematic Division (standard avc_div_v1_2B_R1_Refined)
    dfi_div_pairs_problematic = []
    if omega_val >= 3: dfi_div_pairs_problematic.append((1,2)) # q=0
    if omega_val >= 4: dfi_div_pairs_problematic.append((3,2)) # non-exact q=1, r=1
    if omega_val >= 5: dfi_div_pairs_problematic.append((2,4)) # q=0
    
    for a_dfi, b_dfi in dfi_div_pairs_problematic:
        if not (1 <= a_dfi < omega_val and 1 <= b_dfi < omega_val and b_dfi != 0): continue
        # Check if this case is indeed problematic (i.e. non-DFI result)
        q,r = divmod(a_dfi,b_dfi)
        if r == 0 and 1 <= q < omega_val: continue # Not a problematic case

        res_div = avc_div_v1_2B_R1_Refined(a_dfi, b_dfi)
        if not (res_div is AREO_UNIO):
            all_breaches_are_strictly_AREO = False
            details.append(f"avc_div_v1_2B_R1_Refined({a_dfi},{b_dfi}) -> {res_div!r} (not strictly AREO_UNIO)")
            break
    if not all_breaches_are_strictly_AREO: return False, ", ".join(details)
    
    return all_breaches_are_strictly_AREO, None # If all checks passed

# --- Main Execution Block ---
if __name__ == "__main__":
    print("====== AVCA R1 Refined: Additive Overflow & Strict Uniformity Comparison ======")
    omegas_to_test = [1, 2, 3, 4, 5]

    for omega_val_test in omegas_to_test:
        set_avca_omega_R1_Refined(omega_val_test)
        print(f"\n--- Testing for Ω = {omega_val_test} ---")

        # Test with avc_add_v1_1_logic_refined (Overflow to AREO_UNIO)
        variant_name_v11 = "⊕_v1.1 (Overflow to AREO)"
        run_test_R1_refined("Assoc_Test", "Associativity", omega_val_test, 
                            lambda o, **kw: check_associativity_refined(o, add_func_variant=avc_add_v1_1_logic_refined), 
                            expect_pass=(omega_val_test <= 2), op_variant_name=variant_name_v11)
        
        run_test_R1_refined("Strict_Uniformity_Test", "DFI Breach STRICT Uniformity (all object IS AREO_UNIO)", omega_val_test,
                            lambda o, **kw: check_dft_boundary_breach_STRICT_OBJECT_uniformity_to_AREO(o, add_func_variant=avc_add_v1_1_logic_refined),
                            expect_pass=True, op_variant_name=variant_name_v11)

        # Test with avc_add_v1_0_logic_refined (Overflow to ZERO_UNIO)
        variant_name_v10 = "⊕_v1.0 (Overflow to ZERO)"
        run_test_R1_refined("Assoc_Test", "Associativity", omega_val_test,
                            lambda o, **kw: check_associativity_refined(o, add_func_variant=avc_add_v1_0_logic_refined),
                            expect_pass=(omega_val_test <= 2), op_variant_name=variant_name_v10)
        
        run_test_R1_refined("Strict_Uniformity_Test", "DFI Breach STRICT Uniformity (all object IS AREO_UNIO)", omega_val_test,
                            lambda o, **kw: check_dft_boundary_breach_STRICT_OBJECT_uniformity_to_AREO(o, add_func_variant=avc_add_v1_0_logic_refined),
                            expect_pass=False, op_variant_name=variant_name_v10) # Expected to FAIL for strict uniformity to AREO

    print("\n\n--- Overall Test Summary (R1 Refined: Add Overflow & Strict Uniformity) ---")
    for suite_key, results in sorted(test_results_R1_refined.items()):
        print(f"  {suite_key}: Passed={results['passed']}, Failed={results['failed']}, Skipped={results['skipped']}")
    
    print("\n====== R1 Refined Script Finished ======")