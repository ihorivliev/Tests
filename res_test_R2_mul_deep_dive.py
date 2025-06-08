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

Omega_R2_DeepDive: int = 0

def set_avca_omega_R2_DeepDive(omega_value: int, verbose=False):
    global Omega_R2_DeepDive
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R2_DeepDive parameter must be an integer >= 1.")
    Omega_R2_DeepDive = omega_value
    if verbose: print(f"R2 DeepDive Test: Omega_R2_DeepDive set to {Omega_R2_DeepDive}")

def _check_val_R2_DeepDive(x: AVCVal, current_omega: int, op_name: str = "op", arg_name:str = "input"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R2_DeepDive for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid {arg_name} for {op_name}:{x!r} (type {type(x)}) for Ω={current_omega}")
    if current_omega==1 and isinstance(x,int): raise ValueError(f"Invalid DFI {arg_name} for {op_name} Omega_R2_DeepDive=1: {x!r}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI {arg_name} for {op_name}:{x!r}, Omega_R2_DeepDive={current_omega}, DFI range [1, {current_omega-1}]")

# --- Context Operations (Fixed: Add v1.1, Sub v1.0, Div AltD) ---
def avc_add_fixed_R2(a: AVCVal, b: AVCVal) -> AVCVal: # v1.1 logic
    global Omega_R2_DeepDive; _check_val_R2_DeepDive(a,Omega_R2_DeepDive); _check_val_R2_DeepDive(b,Omega_R2_DeepDive)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R2_DeepDive else AREO_UNIO # type: ignore

def _dfi_div_logic_R2_DeepDive(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal:
    if b_dfi == 0: raise ZeroDivisionError("DFI division by zero")
    q,r=divmod(a_dfi,b_dfi); return q if r==0 and 1<=q<current_omega else AREO_UNIO

def avc_div_AltD_fixed_R2(a: AVCVal, b: AVCVal) -> AVCVal: # AltD Logic
    global Omega_R2_DeepDive
    _check_val_R2_DeepDive(a,Omega_R2_DeepDive,"div_AltD(a)","a"); _check_val_R2_DeepDive(b,Omega_R2_DeepDive,"div_AltD(b)","b")
    if isinstance(b, int): 
        if a is ZERO_UNIO: return ZERO_UNIO      
        if a is AREO_UNIO: return AREO_UNIO      
        if isinstance(a, int): return _dfi_div_logic_R2_DeepDive(a,b,Omega_R2_DeepDive) 
    elif isinstance(b, Unio):
        if isinstance(a, int): return AREO_UNIO  
        elif isinstance(a, Unio): 
            if b.aspect == "areo": return AREO_UNIO 
            else: return a 
    raise RuntimeError(f"Internal logic error in avc_div_AltD_fixed_R2 with a={a!r}, b={b!r}")

# Standard DFI-DFI Multiplication Logic (used by all mul variants)
def _dfi_mul_logic_R2_Deep(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal:
    product = a_dfi * b_dfi
    return product if 1 <= product < current_omega else AREO_UNIO

# --- Multiplication Variants for Comparison ---
def avc_mul_Spec_v1_2(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R2_DeepDive; _check_val_R2_DeepDive(a,Omega_R2_DeepDive); _check_val_R2_DeepDive(b,Omega_R2_DeepDive)
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_areo = a_is_u and a.aspect=="areo"; b_is_areo = b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_is_areo or b_is_areo else ZERO_UNIO
    return _dfi_mul_logic_R2_Deep(a,b,Omega_R2_DeepDive) # type: ignore

def avc_mul_AltA_FirstOp(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R2_DeepDive; _check_val_R2_DeepDive(a,Omega_R2_DeepDive); _check_val_R2_DeepDive(b,Omega_R2_DeepDive)
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u: return AREO_UNIO if a.aspect=="areo" else ZERO_UNIO # type: ignore
    elif b_is_u: return AREO_UNIO if b.aspect=="areo" else ZERO_UNIO # type: ignore
    return _dfi_mul_logic_R2_Deep(a,b,Omega_R2_DeepDive) # type: ignore

def avc_mul_AltB_ZeroDom(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R2_DeepDive; _check_val_R2_DeepDive(a,Omega_R2_DeepDive); _check_val_R2_DeepDive(b,Omega_R2_DeepDive)
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_zero = a_is_u and a.aspect=="zero"; b_is_zero = b_is_u and b.aspect=="zero" # type: ignore
        return ZERO_UNIO if a_is_zero or b_is_zero else AREO_UNIO
    return _dfi_mul_logic_R2_Deep(a,b,Omega_R2_DeepDive) # type: ignore

# --- Test Harness & Helper ---
test_results_R2_DeepDive = {}
def run_test_R2_DeepDive(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R2_DeepDive
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R2_DeepDive: test_results_R2_DeepDive[suite_key]={"p":0,"f":0,"s":0,"e":0}
    mul_var_name = kwargs.get("mul_variant_name", "N/A")
    op_name = kwargs.get("mul_func_variant", lambda:None).__name__
    full_test_name = f"{test_name} ({op_name} via {mul_var_name})"
    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_s="PASS" if passes else "FAIL"; exp_s="PASS" if expect_pass else "FAIL"
        if passes == expect_pass:
            print(f"PASS (Observed: {actual_s})"); test_results_R2_DeepDive[suite_key]["p"]+=1
        else:
            print(f"FAIL (Observed: {actual_s}, Expected: {exp_s})")
            if detail: print(f"    Detail: {detail}")
            test_results_R2_DeepDive[suite_key]["f"]+=1
    except Exception as e: print(f"ERROR ({type(e).__name__}: {e})"); test_results_R2_DeepDive[suite_key]["e"]+=1

def get_s_omega_R2_DeepDive(current_omega: int) -> List[AVCVal]:
    if current_omega == 1: return [ZERO_UNIO, AREO_UNIO] 
    elements = [ZERO_UNIO, AREO_UNIO] + list(range(1, current_omega))
    return list(set(elements))

# --- Native Python Property Test Functions for R2 Deep Dive ---
def check_mul_commutativity_alg_R2_Deep(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R2_DeepDive(omega_val)
    for a,b in itertools.product(elements, repeat=2):
        try:
            if omega_val==1 and (isinstance(a,int) or isinstance(b,int)): continue
            res1=mul_func_variant(a,b); res2=mul_func_variant(b,a)
            if res1 != res2: return False, f"Alg: {a!r}⊗{b!r}={res1!r} != {b!r}⊗{a!r}={res2!r}"
        except ValueError: pass 
    return True, None

def check_mul_associativity_alg_R2_Deep(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R2_DeepDive(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try:
            if omega_val==1 and any(isinstance(x,int) for x in [a,b,c]): continue
            lhs=mul_func_variant(mul_func_variant(a,b),c); rhs=mul_func_variant(a,mul_func_variant(b,c))
            if lhs != rhs: return False, f"Alg: ({a!r}⊗{b!r})⊗{c!r}={lhs!r} != {a!r}⊗({b!r}⊗{c!r})={rhs!r}"
        except ValueError: pass
    return True, None

def check_mul_output_aspect_symmetry_R2_Deep(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    res_ZA = mul_func_variant(ZERO_UNIO, AREO_UNIO)
    res_AZ = mul_func_variant(AREO_UNIO, ZERO_UNIO)
    if (res_ZA is res_AZ) or (isinstance(res_ZA, Unio) and isinstance(res_AZ, Unio) and res_ZA.aspect == res_AZ.aspect):
        return True, f"ZU⊗AU→{res_ZA!r}, AU⊗ZU→{res_AZ!r} (Aspects Symmetric)"
    return False, f"ZU⊗AU→{res_ZA!r}, AU⊗ZU→{res_AZ!r} (Aspects NOT Symmetric)"

def check_mul_dfi_overflow_aspect_consistency_R2_Deep(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    if omega_val < 3: return True, "N/A for Ω<3"
    dfi_pairs_for_overflow = [(2,2) if omega_val==3 else (2,2) if omega_val==4 and 2*2>=4 else (omega_val-1, omega_val-1)] # simplified
    if not dfi_pairs_for_overflow : return True, f"No DFI pair for overflow for Ω={omega_val}"
    a_dfi, b_dfi = dfi_pairs_for_overflow[0]
    try: _check_val_R2_DeepDive(a_dfi, omega_val); _check_val_R2_DeepDive(b_dfi, omega_val)
    except ValueError: return True, f"DFI pair {a_dfi},{b_dfi} invalid for Ω={omega_val}"
    U_from_dfi_mul_overflow = _dfi_mul_logic_R2_Deep(a_dfi, b_dfi, omega_val)
    if not (U_from_dfi_mul_overflow is AREO_UNIO):
         return False, f"SETUP FAIL: {a_dfi}x{b_dfi}(DFI logic)->{U_from_dfi_mul_overflow!r}, exp AREO_UNIO"
    res_AU_ZU = mul_func_variant(U_from_dfi_mul_overflow, ZERO_UNIO)
    if res_AU_ZU is AREO_UNIO:
        return True, f"(DFI...→{U_from_dfi_mul_overflow!r})⊗ZU→{res_AU_ZU!r} (AREO preserved)"
    else:
        return False, f"(DFI...→{U_from_dfi_mul_overflow!r})⊗ZU→{res_AU_ZU!r} (AREO NOT preserved to AREO_UNIO)"

def check_left_distributivity_R2_Deep(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R2_DeepDive(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try:
            if omega_val==1 and any(isinstance(x,int) for x in [a,b,c]): continue
            bpc=avc_add_fixed_R2(b,c); lhs=mul_func_variant(a,bpc)
            amb=mul_func_variant(a,b); amc=mul_func_variant(a,c); rhs=avc_add_fixed_R2(amb,amc)
            if lhs != rhs: return False, f"a({b}⊕{c})={lhs!r} != (a⊗{b})⊕(a⊗{c})={rhs!r} for a={a!r},b={b!r},c={c!r}"
        except ValueError: pass
    return True, None

def check_mul_idempotence_R2_Deep(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    res_ZUZU = mul_func_variant(ZERO_UNIO, ZERO_UNIO)
    res_AUAU = mul_func_variant(AREO_UNIO, AREO_UNIO)
    zu_idempotent = (res_ZUZU is ZERO_UNIO)
    au_idempotent = (res_AUAU is AREO_UNIO)
    if zu_idempotent and au_idempotent: return True, f"ZU⊗ZU→{res_ZUZU!r}, AU⊗AU→{res_AUAU!r}"
    details = []
    if not zu_idempotent: details.append(f"ZU⊗ZU→{res_ZUZU!r} (not ZU)")
    if not au_idempotent: details.append(f"AU⊗AU→{res_AUAU!r} (not AU)")
    return False, ", ".join(details)

def check_interaction_with_div_AltD_outputs_R2_Deep(omega_val: int, mul_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    if omega_val < 2: return True, "N/A for Ω<2 (needs DFI for div cases)"
    # Case 1: Output from ZU ⊘_AltD ZU (which is ZU_obj)
    U_div_res1 = avc_div_AltD_fixed_R2(ZERO_UNIO, ZERO_UNIO) # Should be ZU
    if U_div_res1 is not ZERO_UNIO: return False, f"Setup: ZU⊘ZU (AltD) did not yield ZU, got {U_div_res1!r}"
    
    mul_res1a = mul_func_variant(U_div_res1, AREO_UNIO) # ZU ⊗ AU
    mul_res1b = mul_func_variant(U_div_res1, ZERO_UNIO) # ZU ⊗ ZU

    # Case 2: Output from ZU ⊘_AltD AU (which is AU_obj)
    U_div_res2 = avc_div_AltD_fixed_R2(ZERO_UNIO, AREO_UNIO) # Should be AU
    if U_div_res2 is not AREO_UNIO: return False, f"Setup: ZU⊘AU (AltD) did not yield AU, got {U_div_res2!r}"

    mul_res2a = mul_func_variant(U_div_res2, ZERO_UNIO) # AU ⊗ ZU
    mul_res2b = mul_func_variant(U_div_res2, AREO_UNIO) # AU ⊗ AU

    # Determine expected results for the mul_func_variant
    # v1.2: ZU⊗AU->AU, ZU⊗ZU->ZU, AU⊗ZU->AU, AU⊗AU->AU
    # AltA: ZU⊗AU->ZU, ZU⊗ZU->ZU, AU⊗ZU->AU, AU⊗AU->AU
    # AltB: ZU⊗AU->ZU, ZU⊗ZU->ZU, AU⊗ZU->ZU, AU⊗AU->AU

    expected_mul_res1a, expected_mul_res1b, expected_mul_res2a, expected_mul_res2b = None,None,None,None
    m_name = mul_func_variant.__name__
    if "Spec_v1_2" in m_name: # AreoDom
        expected_mul_res1a, expected_mul_res1b = AREO_UNIO, ZERO_UNIO
        expected_mul_res2a, expected_mul_res2b = AREO_UNIO, AREO_UNIO
    elif "AltA_FirstOp" in m_name:
        expected_mul_res1a, expected_mul_res1b = ZERO_UNIO, ZERO_UNIO # U_div_res1 (ZU) is first
        expected_mul_res2a, expected_mul_res2b = AREO_UNIO, AREO_UNIO # U_div_res2 (AU) is first
    elif "AltB_ZeroDom" in m_name:
        expected_mul_res1a, expected_mul_res1b = ZERO_UNIO, ZERO_UNIO # ZU involved in both
        expected_mul_res2a, expected_mul_res2b = ZERO_UNIO, AREO_UNIO # ZU involved in first, only AU in second
    
    passed = (mul_res1a is expected_mul_res1a) and \
             (mul_res1b is expected_mul_res1b) and \
             (mul_res2a is expected_mul_res2a) and \
             (mul_res2b is expected_mul_res2b)
    
    if passed: return True, f"DivRes1(ZU)⊗AU→{mul_res1a!r}, DivRes1(ZU)⊗ZU→{mul_res1b!r}; DivRes2(AU)⊗ZU→{mul_res2a!r}, DivRes2(AU)⊗AU→{mul_res2b!r}"
    else: return False, f"MISMATCH: DivRes1(ZU)⊗AU→{mul_res1a!r}(exp {expected_mul_res1a!r}), DivRes1(ZU)⊗ZU→{mul_res1b!r}(exp {expected_mul_res1b!r}); DivRes2(AU)⊗ZU→{mul_res2a!r}(exp {expected_mul_res2a!r}), DivRes2(AU)⊗AU→{mul_res2b!r}(exp {expected_mul_res2b!r})"

# --- Main Execution Block ---
if __name__ == "__main__":
    print("====== AVCA R2 Deep Dive: Multiplication Aspect Handling vs Best Add/Div ======")
    omegas_to_test = [1, 2, 3, 4, 5]
    mul_variants_map = {"Spec(v1.2)":avc_mul_Spec_v1_2, "AltA(FirstOp)":avc_mul_AltA_FirstOp, "AltB(ZeroDom)":avc_mul_AltB_ZeroDom}

    for omega_val_test in omegas_to_test:
        set_avca_omega_R2_DeepDive(omega_val_test)
        print(f"\n--- Native Tests for Ω = {omega_val_test} ---")
        for variant_key, mul_func in mul_variants_map.items():
            print(f"-- Variant: {variant_key} --")
            run_test_R2_DeepDive(variant_key,"Alg.Comm ⊗",omega_val_test,check_mul_commutativity_alg_R2_Deep,True,mul_func_variant=mul_func,mul_variant_name=variant_key)
            run_test_R2_DeepDive(variant_key,"Alg.Assoc ⊗",omega_val_test,check_mul_associativity_alg_R2_Deep,True,mul_func_variant=mul_func,mul_variant_name=variant_key)
            exp_symm=True if variant_key!="AltA(FirstOp)" else False
            if omega_val_test==1 and variant_key=="AltA(FirstOp)": exp_symm=False # Explicitly from R2 old output
            run_test_R2_DeepDive(variant_key,"OutAspSymmZU⊗AU",omega_val_test,check_mul_output_aspect_symmetry_R2_Deep,exp_symm,mul_func_variant=mul_func,mul_variant_name=variant_key)
            
            exp_ov_cons=False;
            if omega_val_test<3:exp_ov_cons=True # N/A
            elif variant_key=="Spec(v1.2)" or variant_key=="AltA(FirstOp)":exp_ov_cons=True
            run_test_R2_DeepDive(variant_key,"OvflwAspConsist(DFI²→AU)⊗ZU",omega_val_test,check_mul_dfi_overflow_aspect_consistency_R2_Deep,exp_ov_cons,mul_func_variant=mul_func,mul_variant_name=variant_key)
            
            run_test_R2_DeepDive(variant_key,"LDist(⊗/⊕v1.1)",omega_val_test,check_left_distributivity_R2_Deep,(omega_val_test<=2),mul_func_variant=mul_func,mul_variant_name=variant_key)
            
            exp_idem_zu=True; exp_idem_au=True # Generally Unios are idempotent for their own aspect
            if variant_key == "AltB(ZeroDom)" and omega_val_test > 1: # AU⊗AU -> AU
                pass
            run_test_R2_DeepDive(variant_key,"Idempotence UZ⊗UZ, AU⊗AU",omega_val_test,check_mul_idempotence_R2_Deep,True,mul_func_variant=mul_func,mul_variant_name=variant_key) # Both should be true for all
            
            run_test_R2_DeepDive(variant_key,"Interact w DivAltD Outputs",omega_val_test,check_interaction_with_div_AltD_outputs_R2_Deep,True,mul_func_variant=mul_func,mul_variant_name=variant_key)


    print("\n\n--- Overall Native Test Summary (R2 Deep Dive) ---")
    for sk, res_val in sorted(test_results_R2_DeepDive.items()): print(f"  {sk}: P={res_val['p']}, F={res_val['f']}, S={res_val['s']}, E={res_val['e']}")
    print("\n====== R2 Deep Dive Script Finished ======")