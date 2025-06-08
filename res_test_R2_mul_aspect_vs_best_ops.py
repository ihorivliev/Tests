import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- Standard Unio Class Definition & Globals ---
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

Omega_R2_Revisited: int = 0

def set_avca_omega_R2_Revisited(omega_value: int, verbose=False):
    global Omega_R2_Revisited
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R2_Revisited parameter must be an integer >= 1.")
    Omega_R2_Revisited = omega_value
    if verbose: print(f"R2 Revisited Test: Omega_R2_Revisited set to {Omega_R2_Revisited}")

def _check_val_R2_Revisited(x: AVCVal, current_omega: int, op_name: str = "op", arg_name:str = "input"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R2_Revisited for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid {arg_name} for {op_name}:{x!r} (type {type(x)}) for Ω={current_omega}")
    if current_omega==1 and isinstance(x,int): raise ValueError(f"Invalid DFI {arg_name} for {op_name} Omega_R2_Revisited=1: {x!r}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI {arg_name} for {op_name}:{x!r}, Omega_R2_Revisited={current_omega}, DFI range [1, {current_omega-1}]")

# --- Context Operations (Fixed for these tests) ---
def avc_add_fixed_context(a: AVCVal, b: AVCVal) -> AVCVal: # Based on v1.1 logic
    global Omega_R2_Revisited
    _check_val_R2_Revisited(a,Omega_R2_Revisited,"add_fixed(a)","a"); _check_val_R2_Revisited(b,Omega_R2_Revisited,"add_fixed(b)","b")
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R2_Revisited else AREO_UNIO # type: ignore

# Standard DFI-DFI Multiplication Logic (used by all mul variants)
def _dfi_mul_logic_R2_Revisited(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal:
    product = a_dfi * b_dfi
    return product if 1 <= product < current_omega else AREO_UNIO

# --- Multiplication Variants for Comparison ---
def avc_mul_Spec_v1_2(a: AVCVal, b: AVCVal) -> AVCVal: # Current Specification: "Areo Dominates"
    global Omega_R2_Revisited
    _check_val_R2_Revisited(a,Omega_R2_Revisited,"mul_v12(a)","a"); _check_val_R2_Revisited(b,Omega_R2_Revisited,"mul_v12(b)","b")
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_areo = a_is_u and a.aspect=="areo" # type: ignore
        b_is_areo = b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_is_areo or b_is_areo else ZERO_UNIO
    return _dfi_mul_logic_R2_Revisited(a,b,Omega_R2_Revisited) # type: ignore

def avc_mul_AltA_FirstOp(a: AVCVal, b: AVCVal) -> AVCVal: # "First Operand Priority"
    global Omega_R2_Revisited
    _check_val_R2_Revisited(a,Omega_R2_Revisited,"mul_AltA(a)","a"); _check_val_R2_Revisited(b,Omega_R2_Revisited,"mul_AltA(b)","b")
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u: return AREO_UNIO if a.aspect=="areo" else ZERO_UNIO # type: ignore
    elif b_is_u: return AREO_UNIO if b.aspect=="areo" else ZERO_UNIO # type: ignore
    return _dfi_mul_logic_R2_Revisited(a,b,Omega_R2_Revisited) # type: ignore

def avc_mul_AltB_ZeroDom(a: AVCVal, b: AVCVal) -> AVCVal: # "Zero Dominates"
    global Omega_R2_Revisited
    _check_val_R2_Revisited(a,Omega_R2_Revisited,"mul_AltB(a)","a"); _check_val_R2_Revisited(b,Omega_R2_Revisited,"mul_AltB(b)","b")
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_zero = a_is_u and a.aspect=="zero" # type: ignore
        b_is_zero = b_is_u and b.aspect=="zero" # type: ignore
        return ZERO_UNIO if a_is_zero or b_is_zero else AREO_UNIO
    return _dfi_mul_logic_R2_Revisited(a,b,Omega_R2_Revisited) # type: ignore

# --- Test Harness ---
test_results_R2_Revisited = {}
def run_test_R2_Revisited(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R2_Revisited
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R2_Revisited: test_results_R2_Revisited[suite_key]={"p":0,"f":0,"s":0,"e":0}
    mul_var_name = kwargs.get("mul_variant_name", "N/A")
    op_name = kwargs.get("mul_func_variant", lambda:None).__name__
    full_test_name = f"{test_name} ({op_name} via {mul_var_name})"
    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_s="PASS" if passes else "FAIL"; exp_s="PASS" if expect_pass else "FAIL"
        if passes == expect_pass:
            print(f"PASS (Observed: {actual_s})"); test_results_R2_Revisited[suite_key]["p"]+=1
        else:
            print(f"FAIL (Observed: {actual_s}, Expected: {exp_s})")
            if detail: print(f"    Detail: {detail}")
            test_results_R2_Revisited[suite_key]["f"]+=1
    except Exception as e: print(f"ERROR ({type(e).__name__}: {e})"); test_results_R2_Revisited[suite_key]["e"]+=1

def get_s_omega_R2_Revisited(current_omega: int) -> List[AVCVal]:
    if current_omega == 1: return [ZERO_UNIO, AREO_UNIO] 
    elements = [ZERO_UNIO, AREO_UNIO] + list(range(1, current_omega))
    return list(set(elements))

# --- Native Python Property Test Functions for R2 Revisited ---
def check_mul_commutativity_alg_R2(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R2_Revisited(omega_val)
    for a,b in itertools.product(elements, repeat=2):
        try:
            if omega_val==1 and (isinstance(a,int) or isinstance(b,int)): continue
            res1=mul_func_variant(a,b); res2=mul_func_variant(b,a)
            if res1 != res2: return False, f"Alg: {a!r}⊗{b!r}={res1!r} != {b!r}⊗{a!r}={res2!r}"
        except ValueError: pass 
    return True, None

def check_mul_associativity_alg_R2(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R2_Revisited(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try:
            if omega_val==1 and any(isinstance(x,int) for x in [a,b,c]): continue
            lhs=mul_func_variant(mul_func_variant(a,b),c); rhs=mul_func_variant(a,mul_func_variant(b,c))
            if lhs != rhs: return False, f"Alg: ({a!r}⊗{b!r})⊗{c!r}={lhs!r} != {a!r}⊗({b!r}⊗{c!r})={rhs!r}"
        except ValueError: pass
    return True, None

def check_mul_output_aspect_symmetry_R2(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    if omega_val == 1: # Only Unio objects, ZU and AU
        res_ZA = mul_func_variant(ZERO_UNIO, AREO_UNIO)
        res_AZ = mul_func_variant(AREO_UNIO, ZERO_UNIO)
        # Check if the Python objects themselves are identical OR if their aspects are identical
        if (res_ZA is res_AZ) or (isinstance(res_ZA, Unio) and isinstance(res_AZ, Unio) and res_ZA.aspect == res_AZ.aspect):
            return True, f"ZU⊗AU→{res_ZA!r}, AU⊗ZU→{res_AZ!r} (Aspects Symmetric)"
        return False, f"ZU⊗AU→{res_ZA!r}, AU⊗ZU→{res_AZ!r} (Aspects NOT Symmetric)"

    # For Omega > 1, we also care about DFI interactions that might be non-symmetric
    # But the primary test is ZU vs AU interaction symmetry.
    # The _get_s_omega_R2_Revisited ensures ZU and AU are in elements if possible.
    elements = get_s_omega_R2_Revisited(omega_val)
    if ZERO_UNIO not in elements or AREO_UNIO not in elements: # Should not happen with current get_s_omega
        return True, "Skipped: ZU or AU not in elements for symmetry check (Omega issue?)"
        
    res_ZA = mul_func_variant(ZERO_UNIO, AREO_UNIO)
    res_AZ = mul_func_variant(AREO_UNIO, ZERO_UNIO)
    if (res_ZA is res_AZ) or (isinstance(res_ZA, Unio) and isinstance(res_AZ, Unio) and res_ZA.aspect == res_AZ.aspect):
        return True, f"ZU⊗AU→{res_ZA!r}, AU⊗ZU→{res_AZ!r} (Aspects Symmetric)"
    return False, f"ZU⊗AU→{res_ZA!r}, AU⊗ZU→{res_AZ!r} (Aspects NOT Symmetric)"


def check_mul_overflow_aspect_consistency_R2(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    if omega_val < 3: return True, "N/A for Ω<3 (robust DFIxDFI to AREO_UNIO hard to guarantee)"
    # Create an AREO_UNIO via DFI multiplication overflow using the variant's DFI logic part
    # For this test, we need a pair that reliably overflows to AREO_UNIO
    dfi_pair_for_overflow = None
    if omega_val == 3 and 2*2 >=3: dfi_pair_for_overflow = (2,2)
    elif omega_val == 4 and 2*2 >=4: dfi_pair_for_overflow = (2,2) # or (3,2), (3,3) etc
    elif omega_val >= 5 : dfi_pair_for_overflow = (omega_val-1, omega_val-1) # (O-1)^2 should be >= O

    if not dfi_pair_for_overflow: return True, f"Could not determine DFI pair for overflow for Ω={omega_val}"
    
    a_dfi, b_dfi = dfi_pair_for_overflow
    try:
        _check_val_R2_Revisited(a_dfi, omega_val); _check_val_R2_Revisited(b_dfi, omega_val)
    except ValueError: return True, f"DFI pair {a_dfi},{b_dfi} invalid for Ω={omega_val}"

    U_from_overflow = _dfi_mul_logic_R2_Revisited(a_dfi, b_dfi, omega_val)
    if not (U_from_overflow is AREO_UNIO): # DFI logic must yield AREO_UNIO for overflow
         return False, f"SETUP FAIL: {a_dfi}x{b_dfi} (DFI logic) -> {U_from_overflow!r}, expected AREO_UNIO"

    res_AU_ZU = mul_func_variant(U_from_overflow, ZERO_UNIO) # Test AREO_UNIO (from DFI ovfl) ⊗ ZERO_UNIO
    if res_AU_ZU is AREO_UNIO:
        return True, f"({a_dfi}x{b_dfi}→{U_from_overflow!r}) ⊗ ZU → {res_AU_ZU!r} (AREO aspect preserved/dominant)"
    else:
        return False, f"({a_dfi}x{b_dfi}→{U_from_overflow!r}) ⊗ ZU → {res_AU_ZU!r} (AREO aspect NOT preserved to AREO_UNIO)"

def check_left_distributivity_R2(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R2_Revisited(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try:
            if omega_val==1 and any(isinstance(x,int) for x in [a,b,c]): continue
            bpc = avc_add_fixed_context(b,c)
            lhs = mul_func_variant(a,bpc)
            amb = mul_func_variant(a,b)
            amc = mul_func_variant(a,c)
            rhs = avc_add_fixed_context(amb,amc)
            if lhs != rhs: return False, f"a({b}⊕{c})={lhs!r} != (a⊗{b})⊕(a⊗{c})={rhs!r} for a={a!r},b={b!r},c={c!r}"
        except ValueError: pass
    return True, None

# --- Main Execution Block ---
if __name__ == "__main__":
    print("====== AVCA R2 Revisited: Multiplication Aspect Handling vs Best Add/Div ======")
    omegas_to_test_native = [1, 2, 3, 4, 5]

    mul_variants_map = {
        "Spec(v1.2)": avc_mul_Spec_v1_2,
        "AltA(FirstOp)": avc_mul_AltA_FirstOp,
        "AltB(ZeroDom)": avc_mul_AltB_ZeroDom,
    }

    for omega_val_test in omegas_to_test_native:
        set_avca_omega_R2_Revisited(omega_val_test)
        print(f"\n--- Native Tests for Ω = {omega_val_test} ---")

        for variant_name_key, mul_func_actual in mul_variants_map.items():
            print(f"-- Variant: {variant_name_key} --")
            run_test_R2_Revisited(variant_name_key, "Alg. Commutativity ⊗", omega_val_test,
                                  check_mul_commutativity_alg_R2, expect_pass=True, 
                                  mul_func_variant=mul_func_actual, mul_variant_name=variant_name_key)
            run_test_R2_Revisited(variant_name_key, "Alg. Associativity ⊗", omega_val_test,
                                  check_mul_associativity_alg_R2, expect_pass=True, 
                                  mul_func_variant=mul_func_actual, mul_variant_name=variant_name_key)
            
            expect_aspect_symm = True
            if variant_name_key == "AltA(FirstOp)": expect_aspect_symm = False
            run_test_R2_Revisited(variant_name_key, "Output Aspect Symmetry ZU⊗AU", omega_val_test,
                                  check_mul_output_aspect_symmetry_R2, expect_pass=expect_aspect_symm,
                                  mul_func_variant=mul_func_actual, mul_variant_name=variant_name_key)

            expect_overflow_consist = False # Default to fail unless specified
            if omega_val_test < 3: expect_overflow_consist = True # Vacuously true as test is N/A
            elif variant_name_key == "Spec(v1.2)": expect_overflow_consist = True
            elif variant_name_key == "AltA(FirstOp)": expect_overflow_consist = True # AU_overflow is first operand
            elif variant_name_key == "AltB(ZeroDom)": expect_overflow_consist = False # ZU in AU⊗ZU makes result ZU
            run_test_R2_Revisited(variant_name_key, "Overflow Aspect Consist. (DFI²→AU)⊗ZU", omega_val_test,
                                  check_mul_overflow_aspect_consistency_R2, expect_pass=expect_overflow_consist,
                                  mul_func_variant=mul_func_actual, mul_variant_name=variant_name_key)
            
            run_test_R2_Revisited(variant_name_key, "Left Distributivity ⊗ over ⊕_v1.1", omega_val_test,
                                  check_left_distributivity_R2, expect_pass=(omega_val_test <= 2),
                                  mul_func_variant=mul_func_actual, mul_variant_name=variant_name_key)

    print("\n\n--- Overall Native Test Summary (R2 Revisited: Mul Aspect vs Best Add/Div) ---")
    for suite_key, results in sorted(test_results_R2_Revisited.items()):
        print(f"  {suite_key}: Passed={results['p']}, Failed={results['f']}, Skipped={results['s']}, Errors={results['e']}")
    
    print("\n====== R2 Revisited Script Finished ======")