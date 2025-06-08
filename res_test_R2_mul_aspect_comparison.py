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

# --- Standard Unio Class Definition ---
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

# --- AVCA Core Logic Base ---
Omega_R2: int = 0

def set_avca_omega_R2(omega_value: int, verbose=False):
    global Omega_R2
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R2 parameter must be an integer >= 1.")
    Omega_R2 = omega_value
    if verbose: print(f"R2 Test: Omega_R2 set to {Omega_R2}")

def _check_val_R2(x: AVCVal, current_omega: int, op_name: str = "op"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R2 for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid val in {op_name}:{x!r}")
    if current_omega==1: raise ValueError(f"Invalid DFI for {op_name} Omega_R2=1:{x}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI for {op_name}:{x}, Omega_R2={current_omega}")

# --- Multiplication Variants for Comparison ---

# Standard DFI-DFI Multiplication Logic (used by all variants)
def _dfl_mul_logic(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal:
    product = a_dfi * b_dfi
    if 1 <= product < current_omega:
        return product
    else: # Overflow
        return AREO_UNIO

# R2.Ref: avc_mul_v1_2_logic (Current Specification: "Areo Dominates")
def avc_mul_v1_2_logic(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R2; _check_val_R2(a,Omega_R2,"mul_v12(a)"); _check_val_R2(b,Omega_R2,"mul_v12(b)")
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_areo = a_is_u and a.aspect=="areo" # type: ignore
        b_is_areo = b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_is_areo or b_is_areo else ZERO_UNIO
    return _dfl_mul_logic(a,b,Omega_R2) # type: ignore

# R2.AltA: "First Operand Priority" (Simplified v1.0-like)
def avc_mul_R2_AltA_FirstOp(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R2; _check_val_R2(a,Omega_R2,"mul_AltA(a)"); _check_val_R2(b,Omega_R2,"mul_AltA(b)")
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u: # First operand 'a' is Unio, its aspect determines output
        return AREO_UNIO if a.aspect=="areo" else ZERO_UNIO # type: ignore
    elif b_is_u: # First 'a' is DFI, second 'b' is Unio, b's aspect determines output
        return AREO_UNIO if b.aspect=="areo" else ZERO_UNIO # type: ignore
    return _dfl_mul_logic(a,b,Omega_R2) # type: ignore

# R2.AltB: "Zero Dominates"
def avc_mul_R2_AltB_ZeroDom(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R2; _check_val_R2(a,Omega_R2,"mul_AltB(a)"); _check_val_R2(b,Omega_R2,"mul_AltB(b)")
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_zero = a_is_u and a.aspect=="zero" # type: ignore
        b_is_zero = b_is_u and b.aspect=="zero" # type: ignore
        return ZERO_UNIO if a_is_zero or b_is_zero else AREO_UNIO
    return _dfl_mul_logic(a,b,Omega_R2) # type: ignore

# --- Test Harness ---
test_results_R2 = {}
def run_test_R2(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R2
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R2: test_results_R2[suite_key] = {"passed":0,"failed":0,"skipped":0}
    variant_name = kwargs.get("mul_variant_name", "N/A")
    full_test_name = f"{test_name} ({variant_name})"
    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_res_str = "PASS" if passes else "FAIL"
        exp_res_str = "PASS" if expect_pass else "FAIL"
        if passes == expect_pass:
            print(f"PASS (Observed: {actual_res_str})")
            test_results_R2[suite_key]["passed"] += 1
        else:
            print(f"FAIL (Observed: {actual_res_str}, Expected: {exp_res_str})")
            if detail: print(f"    Detail: {detail}")
            test_results_R2[suite_key]["failed"] += 1
    except Exception as e: print(f"ERROR ({e})"); test_results_R2[suite_key]["failed"] += 1

def get_s_omega_R2(current_omega: int) -> List[AVCVal]:
    if current_omega == 1: return [ZERO_UNIO, AREO_UNIO] # Ensure both aspects are available
    # For iteration, use specific objects for Unio to test aspect interactions
    # DFI elements are just integers
    return [ZERO_UNIO, AREO_UNIO] + list(range(1, current_omega))

# --- Native Python Property Test Functions ---
def check_mul_commutativity_algebraic(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R2(omega_val)
    for a,b in itertools.product(elements, repeat=2):
        try: # Catch potential _check_val errors if elements list is not perfectly filtered for Omega=1
            res1 = mul_func_variant(a,b)
            res2 = mul_func_variant(b,a)
            if res1 != res2: # Uses Unio.__eq__ for algebraic equivalence
                return False, f"Algebraic: {a!r}⊗{b!r}={res1!r} BUT {b!r}⊗{a!r}={res2!r}"
        except ValueError:
            if omega_val == 1 and isinstance(a,Unio) and isinstance(b,Unio): pass
            else: raise
    return True, None

def check_mul_associativity_algebraic(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R2(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try:
            lhs = mul_func_variant(mul_func_variant(a,b),c)
            rhs = mul_func_variant(a,mul_func_variant(b,c))
            if lhs != rhs: # Algebraic equivalence
                return False, f"Alg: ({a!r}⊗{b!r})⊗{c!r}={lhs!r} BUT {a!r}⊗({b!r}⊗{c!r})={rhs!r}"
        except ValueError: 
            if omega_val == 1: pass # All Unio ops are fine
            else: raise
    return True, None

def check_mul_output_aspect_symmetry(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    # Tests if U_Z ⊗ U_A yields the same Python object as U_A ⊗ U_Z
    try:
        res_ZA = mul_func_variant(ZERO_UNIO, AREO_UNIO)
        res_AZ = mul_func_variant(AREO_UNIO, ZERO_UNIO)
        if res_ZA is res_AZ: # Strict object identity for symmetry of output object
            return True, f"U_Z⊗U_A -> {res_ZA!r}, U_A⊗U_Z -> {res_AZ!r} (Objects ARE identical)"
        else:
            # Check if they are at least algebraically equivalent (both must be Unio)
            # and if their aspects are the same, even if not same object ID.
            if isinstance(res_ZA, Unio) and isinstance(res_AZ, Unio) and res_ZA.aspect == res_AZ.aspect:
                 return True, f"U_Z⊗U_A -> {res_ZA!r}, U_A⊗U_Z -> {res_AZ!r} (Objects differ, but aspects ARE identical)"
            return False, f"U_Z⊗U_A -> {res_ZA!r}, U_A⊗U_Z -> {res_AZ!r} (Object and/or aspect differs)"
    except ValueError:
        if omega_val == 1: return True, "Symmetry N/A for Ω=1 as only one effective Unio object can be formed if DFI empty and mul by DFI N/A"
        else: raise
    return True, None


def check_mul_overflow_aspect_consistency(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    # Test: (DFI_overflow_product_yielding_AREO) ⊗ ZERO_UNIO
    # Does it preserve the "areo" aspect from the overflow, or does ZERO_UNIO dominate/alter it?
    if omega_val < 3: # Need DFI elements that can robustly overflow to AREO_UNIO
        return True, "Test less meaningful for Ω<3 (limited DFI overflow scenarios to produce AREO_UNIO)"

    # Create an AREO_UNIO via DFI multiplication overflow
    # Example: For Ω=3, 2*2=4 -> AREO_UNIO. For Ω=4, 2*2=4 -> AREO_UNIO. For Ω=5, 2*3=6 -> AREO_UNIO
    dfi1, dfi2 = -1, -1
    if omega_val == 3: dfi1, dfi2 = 2, 2
    elif omega_val == 4: dfi1, dfi2 = 2, 2 # or 2,3 or 3,3
    elif omega_val >= 5: dfi1, dfi2 = omega_val-1, omega_val-1 # Guaranteed overflow if (O-1)^2 >= O
    
    if dfi1 == -1 : return True, "Could not find suitable DFI pair for overflow"

    try:
        _check_val_R2(dfi1, omega_val); _check_val_R2(dfi2, omega_val)
        U_from_overflow = _dfl_mul_logic(dfi1, dfi2, omega_val)
        if not (U_from_overflow is AREO_UNIO): # Ensure our setup works
             return False, f"Setup Error: {dfi1}x{dfi2} did not yield AREO_UNIO, got {U_from_overflow!r}"

        res_AU_ZU = mul_func_variant(U_from_overflow, ZERO_UNIO)
        res_ZU_AU = mul_func_variant(ZERO_UNIO, U_from_overflow)

        # Ideal for v1.2 ("Areo dominates"): res_AU_ZU should be AREO_UNIO
        # Ideal for AltB ("Zero dominates"): res_AU_ZU should be ZERO_UNIO
        # Ideal for AltA ("FirstOp"): res_AU_ZU=AREO_UNIO, res_ZU_AU=ZERO_UNIO
        
        # This test checks if the "areo" nature of U_from_overflow is preserved (i.e., result is AREO_UNIO)
        # when interacting with ZERO_UNIO, regardless of order for symmetric rules.
        # For this specific check, let's see if U_from_overflow (AREO_UNIO) x ZERO_UNIO results in AREO_UNIO.
        if res_AU_ZU is AREO_UNIO:
            return True, f"({dfi1}x{dfi2}→{U_from_overflow!r}) ⊗ ZU → {res_AU_ZU!r}. Areo aspect preserved."
        else:
            return False, f"({dfi1}x{dfi2}→{U_from_overflow!r}) ⊗ ZU → {res_AU_ZU!r}. Areo aspect NOT preserved to AREO_UNIO."

    except ValueError:
        if omega_val <3 : return True, "N/A for Ω<3" # Should be caught earlier
        else: raise
    return True, None


# --- SMT Components (Placeholders - full SMT harness is complex for one script) ---
# For this focused comparison, we'll rely heavily on native Python exhaustive tests.
# Full SMT would require defining SMT logic builders for each mul_variant.
# We can add a few illustrative SMT checks for key properties if needed,
# assuming the SMT builders for the variants are created.

# --- Main Execution Block ---
if __name__ == "__main__":
    print("====== AVCA R2: Multiplication Aspect Handling Comparison ======")
    omegas_to_test_native = [1, 2, 3, 4] # Add 1 for completeness
    # omegas_to_test_smt = [2, 3, 5] # If SMT tests were fully implemented here

    mul_variants = {
        "⊗_v1.2 (AreoDom)": avc_mul_v1_2_logic,
        "⊗_AltA (FirstOp)": avc_mul_R2_AltA_FirstOp,
        "⊗_AltB (ZeroDom)": avc_mul_R2_AltB_ZeroDom,
    }

    for omega_val_test in omegas_to_test_native:
        set_avca_omega_R2(omega_val_test)
        print(f"\n--- Native Tests for Ω = {omega_val_test} ---")

        for variant_name, mul_func in mul_variants.items():
            print(f"-- Variant: {variant_name} --")
            run_test_R2(variant_name, "Algebraic Commutativity of ⊗", omega_val_test,
                        check_mul_commutativity_algebraic, expect_pass=True, mul_func_variant=mul_func, mul_variant_name=variant_name)
            run_test_R2(variant_name, "Algebraic Associativity of ⊗", omega_val_test,
                        check_mul_associativity_algebraic, expect_pass=True, mul_func_variant=mul_func, mul_variant_name=variant_name)
            
            # Output Aspect Symmetry Test
            # Expected Pass for v1.2 and AltB (ZeroDom)
            # Expected Fail for AltA (FirstOp) for Ω > 1
            expect_aspect_symmetry_pass = True
            if variant_name == "⊗_AltA (FirstOp)" and omega_val_test > 1 : # Because UZ != UA
                 expect_aspect_symmetry_pass = False
            elif omega_val_test == 1 and variant_name == "⊗_AltA (FirstOp)": # UZ o U A -> aspect of UZ. UA o UZ -> aspect of UA. These are diff aspects.
                 # However for omega=1, ZERO_UNIO and AREO_UNIO are the only distinct Python inputs.
                 # res_ZA = AltA(ZERO_UNIO, AREO_UNIO) -> ZERO_UNIO object
                 # res_AZ = AltA(AREO_UNIO, ZERO_UNIO) -> AREO_UNIO object
                 # These objects are not `is` same. So expect_aspect_symmetry_pass should be False.
                 expect_aspect_symmetry_pass = False


            run_test_R2(variant_name, "Output Aspect Symmetry (ZU⊗UA vs UA⊗ZU)", omega_val_test,
                        check_mul_output_aspect_symmetry, expect_pass=expect_aspect_symmetry_pass, mul_func_variant=mul_func, mul_variant_name=variant_name)

            # Overflow Aspect Consistency Test
            # Expected Pass for v1.2 (AreoDom) for Ω>=3
            # Expected Fail for AltB (ZeroDom) for Ω>=3
            # Expected depends on order for AltA (FirstOp) for Ω>=3
            expect_overflow_consistency_pass = False # Default
            if omega_val_test < 3: # Test is less meaningful
                expect_overflow_consistency_pass = True # Vacuously true or test returns true
            elif variant_name == "⊗_v1.2 (AreoDom)":
                expect_overflow_consistency_pass = True
            elif variant_name == "⊗_AltB (ZeroDom)":
                expect_overflow_consistency_pass = False
            elif variant_name == "⊗_AltA (FirstOp)": # (AREO_from_overflow) ⊗ ZERO_UNIO -> AREO_UNIO
                expect_overflow_consistency_pass = True


            run_test_R2(variant_name, "Overflow Aspect Consistency ((DFIxDFI→AU)⊗ZU -> AU)", omega_val_test,
                        check_mul_overflow_aspect_consistency, expect_pass=expect_overflow_consistency_pass, mul_func_variant=mul_func, mul_variant_name=variant_name)

    print("\n\n--- Overall Native Test Summary (R2: Mul Aspect Comparison) ---")
    for suite_key, results in sorted(test_results_R2.items()):
        print(f"  {suite_key}: Passed={results['passed']}, Failed={results['failed']}, Skipped={results['skipped']}")
    
    print("\nNote: SMT tests for R2 variants would require specific SMT logic builders for each mul_variant and are omitted from this script for focus on native comparison of output objects/aspects.")
    print("\n====== R2 Script Finished ======")