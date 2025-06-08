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

Omega_R3_MaxPlus: int = 0

def set_avca_omega_R3_MaxPlus(omega_value: int, verbose=False):
    global Omega_R3_MaxPlus
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R3_MaxPlus parameter must be an integer >= 1.")
    Omega_R3_MaxPlus = omega_value
    if verbose: print(f"R3 MaxPlus Test: Omega_R3_MaxPlus set to {Omega_R3_MaxPlus}")

def _check_val_R3_MaxPlus(x: AVCVal, current_omega: int, op_name: str = "op", arg_name:str = "input"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R3_MaxPlus for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid {arg_name} for {op_name}:{x!r} (type {type(x)}) for Ω={current_omega}")
    if current_omega==1 and isinstance(x,int): raise ValueError(f"Invalid DFI {arg_name} for {op_name} Omega_R3_MaxPlus=1: {x!r}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI {arg_name} for {op_name}:{x!r}, Omega_R3_MaxPlus={current_omega}, DFI range [1, {current_omega-1}]")

# --- Standard Multiplication (v1.2 "Areo Dominates") for Round-Trip Tests ---
def avc_mul_v1_2_R3_MaxPlus(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R3_MaxPlus
    _check_val_R3_MaxPlus(a,Omega_R3_MaxPlus,"mul_v12(a)","a"); _check_val_R3_MaxPlus(b,Omega_R3_MaxPlus,"mul_v12(b)","b")
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_areo = a_is_u and a.aspect=="areo" # type: ignore
        b_is_areo = b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_is_areo or b_is_areo else ZERO_UNIO
    product = a * b # type: ignore
    return product if 1 <= product < Omega_R3_MaxPlus else AREO_UNIO

# --- Division Variants for Comparison ---
def _dfi_div_logic_R3_MaxPlus(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal:
    if b_dfi == 0: raise ZeroDivisionError("DFI division by zero attempted in _dfi_div_logic_R3_MaxPlus")
    quotient, remainder = divmod(a_dfi, b_dfi)
    return quotient if remainder == 0 and (1 <= quotient < current_omega) else AREO_UNIO

def avc_div_Spec_v1_2B(a: AVCVal, b: AVCVal) -> AVCVal: # R3.Spec
    global Omega_R3_MaxPlus
    _check_val_R3_MaxPlus(a,Omega_R3_MaxPlus,"div_v12B(a)","a"); _check_val_R3_MaxPlus(b,Omega_R3_MaxPlus,"div_v12B(b)","b")
    if isinstance(b,Unio): return AREO_UNIO 
    if isinstance(a,Unio): return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO # type: ignore
    return _dfi_div_logic_R3_MaxPlus(a,b,Omega_R3_MaxPlus) # type: ignore

def avc_div_AltA_UnivSat(a: AVCVal, b: AVCVal) -> AVCVal: # R3.AltA
    global Omega_R3_MaxPlus
    _check_val_R3_MaxPlus(a,Omega_R3_MaxPlus,"div_AltA(a)","a"); _check_val_R3_MaxPlus(b,Omega_R3_MaxPlus,"div_AltA(b)","b")
    if isinstance(a,Unio) or isinstance(b,Unio): return AREO_UNIO
    return _dfi_div_logic_R3_MaxPlus(a,b,Omega_R3_MaxPlus) # type: ignore

def avc_div_AltC_V1_0_like(a: AVCVal, b: AVCVal) -> AVCVal: # R3.AltC
    global Omega_R3_MaxPlus
    _check_val_R3_MaxPlus(a,Omega_R3_MaxPlus,"div_AltC(a)","a"); _check_val_R3_MaxPlus(b,Omega_R3_MaxPlus,"div_AltC(b)","b")
    if isinstance(a,Unio): return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO # type: ignore
    elif isinstance(b,Unio): return AREO_UNIO
    return _dfi_div_logic_R3_MaxPlus(a,b,Omega_R3_MaxPlus) # type: ignore

def avc_div_AltD_Balanced(a: AVCVal, b: AVCVal) -> AVCVal: # R3.AltD
    global Omega_R3_MaxPlus
    _check_val_R3_MaxPlus(a,Omega_R3_MaxPlus,"div_AltD(a)","a"); _check_val_R3_MaxPlus(b,Omega_R3_MaxPlus,"div_AltD(b)","b")
    if isinstance(b, int): 
        if a is ZERO_UNIO: return ZERO_UNIO      
        if a is AREO_UNIO: return AREO_UNIO      
        if isinstance(a, int): return _dfi_div_logic_R3_MaxPlus(a,b,Omega_R3_MaxPlus) 
    elif isinstance(b, Unio):
        if isinstance(a, int): return AREO_UNIO  
        elif isinstance(a, Unio): 
            if b.aspect == "areo": return AREO_UNIO 
            else: return a 
    raise RuntimeError(f"Internal logic error in avc_div_AltD_Balanced with a={a!r}, b={b!r}")

def avc_div_AltE_DivisorAspectDet(a: AVCVal, b: AVCVal) -> AVCVal: # R3.AltE (New)
    global Omega_R3_MaxPlus
    _check_val_R3_MaxPlus(a,Omega_R3_MaxPlus,"div_AltE(a)","a"); _check_val_R3_MaxPlus(b,Omega_R3_MaxPlus,"div_AltE(b)","b")
    if isinstance(b, int): # Divisor is DFI
        if a is ZERO_UNIO: return ZERO_UNIO
        if a is AREO_UNIO: return AREO_UNIO
        if isinstance(a, int): return _dfi_div_logic_R3_MaxPlus(a,b,Omega_R3_MaxPlus)
    elif isinstance(b, Unio): # Divisor is Unio
        if isinstance(a, int): return AREO_UNIO # DFI / Unio -> AREO_UNIO
        elif isinstance(a, Unio): # Unio / Unio
            return ZERO_UNIO if b.aspect == "zero" else AREO_UNIO # Result aspect matches divisor aspect
    raise RuntimeError(f"Internal logic error in avc_div_AltE_DivisorAspectDet with a={a!r}, b={b!r}")

# --- Test Harness (same as before, using test_results_R3_MaxPlus) ---
test_results_R3_MaxPlus = {}
def run_test_R3_MaxPlus(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R3_MaxPlus
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R3_MaxPlus: test_results_R3_MaxPlus[suite_key] = {"passed":0,"failed":0,"skipped":0,"errors":0}
    variant_name = kwargs.get("div_variant_name", "N/A")
    current_op_variant_func_name = kwargs.get("div_func_variant", lambda: None).__name__ # For more descriptive test name
    full_test_name = f"{test_name} ({current_op_variant_func_name} via {variant_name})"

    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_res_str = "PASS" if passes else "FAIL"
        exp_res_str = "PASS" if expect_pass else "FAIL"
        if passes == expect_pass:
            print(f"PASS (Observed: {actual_res_str})")
            test_results_R3_MaxPlus[suite_key]["passed"] += 1
        else:
            print(f"FAIL (Observed: {actual_res_str}, Expected: {exp_res_str})")
            if detail: print(f"    Detail: {detail}")
            test_results_R3_MaxPlus[suite_key]["failed"] += 1
    except Exception as e:
        print(f"ERROR ({type(e).__name__}: {e})"); test_results_R3_MaxPlus[suite_key]["errors"] += 1

def get_s_omega_R3_MaxPlus(current_omega: int) -> List[AVCVal]: # Same as before
    if current_omega == 1: return [ZERO_UNIO, AREO_UNIO] 
    elements = [ZERO_UNIO, AREO_UNIO]
    elements.extend(list(range(1, current_omega)))
    return list(set(elements)) 

# --- Native Python Property Test Functions (same as before) ---
def check_div_totality_R3_MaxPlus(omega_val: int, div_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R3_MaxPlus(omega_val)
    for a in elements:
        for b in elements:
            try:
                if omega_val == 1 and (isinstance(a, int) or isinstance(b, int)): continue
                res = div_func_variant(a,b)
                _check_val_R3_MaxPlus(res, omega_val, op_name=div_func_variant.__name__, arg_name="result")
            except ValueError as ve: return False, f"ValueError for {a!r} ÷ {b!r}: {ve}"
            except ZeroDivisionError as zde: return False, f"ZeroDivisionError for {a!r} ÷ {b!r}: {zde}"
            except Exception as e: return False, f"Unexpected Error for {a!r} ÷ {b!r}: {type(e).__name__}({e})"
    return True, None

def check_div_specific_case_R3_MaxPlus(omega_val: int, div_func_variant: Callable, 
                                      a_in: AVCVal, b_in: AVCVal, expected_obj: AVCVal, **kwargs) -> Tuple[bool, Any]:
    case_name = kwargs.get("case_name", "Unknown Case")
    try:
        if isinstance(a_in, int): _check_val_R3_MaxPlus(a_in, omega_val, op_name=div_func_variant.__name__, arg_name=f"a_in for '{case_name}'")
        if isinstance(b_in, int): _check_val_R3_MaxPlus(b_in, omega_val, op_name=div_func_variant.__name__, arg_name=f"b_in for '{case_name}'")
    except ValueError:
        return True, f"N/A (Input {a_in!r} or {b_in!r} invalid for Ω={omega_val} in '{case_name}')"
    res = div_func_variant(a_in, b_in)
    if res is expected_obj: return True, None
    else: return False, f"{a_in!r} ÷ {b_in!r} -> {res!r} (Expected {expected_obj!r})"

def check_div_round_trip_case_R3_MaxPlus(omega_val: int, div_func_variant: Callable,
                                        a_in: AVCVal, b_in: AVCVal, expect_rt_law_to_hold_itself: bool, **kwargs) -> Tuple[bool, Any]:
    case_name = kwargs.get("case_name", "Unknown RT Case")
    try:
        if isinstance(a_in, int): _check_val_R3_MaxPlus(a_in, omega_val, "rt_a_in");
        if isinstance(b_in, int): _check_val_R3_MaxPlus(b_in, omega_val, "rt_b_in");
    except ValueError: return True, f"N/A (Input invalid for Ω={omega_val} for RT '{case_name}')"
    q = div_func_variant(a_in, b_in)
    lhs = avc_mul_v1_2_R3_MaxPlus(q, b_in)
    law_holds = (isinstance(lhs, Unio) and isinstance(a_in, Unio)) or (lhs == a_in)
    if law_holds == expect_rt_law_to_hold_itself:
        return True, f"Law itself observed: {law_holds}, as expected. LHS={lhs!r}, a_in={a_in!r}"
    else:
        return False, f"Law itself observed: {law_holds}, BUT EXPECTED: {expect_rt_law_to_hold_itself}. LHS={lhs!r}, a_in={a_in!r}"

# --- Test Execution ---
# --- Test Execution ---
if __name__ == "__main__":
    print("====== AVCA R3 Max Plus: Division Aspect Handling Comparison (Corrected) ======")
    omegas_to_test = [1, 2, 3, 5] 

    div_variants_map = {
        "Spec(v1.2B)": avc_div_Spec_v1_2B,
        "AltA(UnivSat)": avc_div_AltA_UnivSat,
        "AltC(V1.0Like)": avc_div_AltC_V1_0_like,
        "AltD(Balanced)": avc_div_AltD_Balanced,
        "AltE(DivAspDet)": avc_div_AltE_DivisorAspectDet,
    }

    # (a_in_token, b_in_token, 
    #  exp_obj_v12B, exp_obj_AltA, exp_obj_AltC, exp_obj_AltD, exp_obj_AltE, 
    #  test_name_suffix)
    test_case_definitions = [
        ("ZU", "DFI1", ZERO_UNIO, AREO_UNIO, ZERO_UNIO, ZERO_UNIO, ZERO_UNIO, "ZU/DFI1"),
        ("AU", "DFI1", AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "AU/DFI1"),
        ("DFI1", "ZU", AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "DFI1/ZU"),
        ("DFI1", "AU", AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "DFI1/AU"),
        ("ZU", "ZU", AREO_UNIO, AREO_UNIO, ZERO_UNIO, ZERO_UNIO, ZERO_UNIO, "ZU/ZU"),
        ("AU", "ZU", AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, ZERO_UNIO, "AU/ZU"),
        ("ZU", "AU", AREO_UNIO, AREO_UNIO, ZERO_UNIO, AREO_UNIO, AREO_UNIO, "ZU/AU"),
        ("AU", "AU", AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "AU/AU"),
        ("DFI1", "DFI2", AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "DFI1/DFI2 (q=0 type)"),
        ("DFI_OM1", "DFI2", AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "DFI(Ω-1)/DFI2 (non-exact type)"),
    ]

    rt_test_definitions = [
        # (a_in_token, b_in_token, 
        #  exp_rt_holds_v12B, exp_rt_holds_AltA, exp_rt_holds_AltC, exp_rt_holds_AltD, exp_rt_holds_AltE
        #  rt_test_name_suffix)
        ("DFI2", "DFI1", True, True, True, True, True, "(DFI2⊘DFI1)⊗DFI1==DFI2"),
        ("ZU", "DFI1", True, False, True, True, True, "(ZU⊘DFI1)⊗DFI1==ZU"),
        ("AU", "DFI1", True, True, True, True, True, "(AU⊘DFI1)⊗DFI1==AU"),
        ("DFI1", "ZU", False, False, False, False, False, "(DFI1⊘ZU)⊗ZU==DFI1"),
    ]

    for omega_val_test in omegas_to_test:
        set_avca_omega_R3_MaxPlus(omega_val_test)
        print(f"\n--- Native Tests for Ω = {omega_val_test} ---")
        dfi_map = {"DFI1":1 if omega_val_test>1 else None, "DFI2":2 if omega_val_test>2 else None,
                   "DFI_OM1":omega_val_test-1 if omega_val_test>1 else None, "ZU":ZERO_UNIO, "AU":AREO_UNIO}

        for variant_name_key, div_func_actual in div_variants_map.items():
            print(f"-- Variant: {variant_name_key} --")
            run_test_R3_MaxPlus(variant_name_key, f"Totality", omega_val_test,
                                lambda o, **kw: check_div_totality_R3_MaxPlus(o, div_func_variant=kw['dfv']),
                                expect_pass=True, div_variant_name=variant_name_key, dfv=div_func_actual)
            
            current_dfi_exact_scenarios = []
            if omega_val_test >= 3 and dfi_map["DFI2"] is not None and dfi_map["DFI1"] is not None:
                # Ensure division is actually exact and result is DFI2 for this test case.
                # Example: For Omega=3, DFI2=2, DFI1=1. 2/1 = 2.
                if divmod(dfi_map["DFI2"], dfi_map["DFI1"])[1] == 0 and \
                   divmod(dfi_map["DFI2"], dfi_map["DFI1"])[0] == dfi_map["DFI2"]:
                    current_dfi_exact_scenarios.append(
                        (dfi_map["DFI2"], dfi_map["DFI1"], dfi_map["DFI2"], f"DFI({dfi_map['DFI2']})/DFI({dfi_map['DFI1']}) exact")
                    )
            if omega_val_test == 2 and dfi_map["DFI1"] is not None:
                 # For Omega=2, DFI1=1. 1/1 = 1.
                 if divmod(dfi_map["DFI1"], dfi_map["DFI1"])[1] == 0 and \
                    divmod(dfi_map["DFI1"], dfi_map["DFI1"])[0] == dfi_map["DFI1"]:
                    current_dfi_exact_scenarios.append(
                        (dfi_map["DFI1"], dfi_map["DFI1"], dfi_map["DFI1"], f"DFI({dfi_map['DFI1']})/DFI({dfi_map['DFI1']}) exact")
                    )

            for a_val_cs, b_val_cs, exp_obj_cs, name_sfx_cs in current_dfi_exact_scenarios:
                 run_test_R3_MaxPlus(variant_name_key, f"Case: {name_sfx_cs}", omega_val_test,
                                lambda o, **kw: check_div_specific_case_R3_MaxPlus(o, div_func_variant=kw['dfv'], 
                                                                        a_in=kw['case_a'], b_in=kw['case_b'], 
                                                                        expected_obj=kw['exp_obj'], case_name=kw['c_name']),
                                expect_pass=True, div_variant_name=variant_name_key, dfv=div_func_actual,
                                case_a=a_val_cs, case_b=b_val_cs, exp_obj=exp_obj_cs, c_name=name_sfx_cs)

            for a_tok,b_tok,exp_b_obj,exp_a_obj,exp_c_obj,exp_d_obj,exp_e_obj,name_sfx in test_case_definitions:
                a_val,b_val = dfi_map.get(a_tok), dfi_map.get(b_tok)
                if (isinstance(a_tok,str)and "DFI" in a_tok and a_val is None) or \
                   (isinstance(b_tok,str)and "DFI" in b_tok and b_val is None): continue
                
                current_name_sfx = name_sfx
                if name_sfx == "DFI(Ω-1)/DFI2 (non-exact type)":
                    if a_val is None or b_val is None: continue
                    # Ensure it's actually non-exact or problematic for this Omega
                    q_temp, r_temp = divmod(a_val,b_val)
                    if r_temp == 0 and 1 <= q_temp < omega_val_test: 
                        continue # It's exact and DFI, skip this "non-exact type" test name
                    current_name_sfx = f"DFI({a_val})/DFI({b_val}) problematic" # More general name
                
                exp_map={"Spec(v1.2B)":exp_b_obj,"AltA(UnivSat)":exp_a_obj,
                         "AltC(V1.0Like)":exp_c_obj,"AltD(Balanced)":exp_d_obj,
                         "AltE(DivAspDet)":exp_e_obj}
                current_exp_obj = exp_map[variant_name_key]
                
                if isinstance(current_exp_obj,str)and "DFI" in current_exp_obj: 
                    resolved_dfi = dfi_map.get(current_exp_obj)
                    if resolved_dfi is None: continue 
                    current_exp_obj = resolved_dfi
                
                run_test_R3_MaxPlus(variant_name_key, f"Case: {current_name_sfx}", omega_val_test,
                                lambda o, **kw: check_div_specific_case_R3_MaxPlus(o, div_func_variant=kw['dfv'], 
                                                                        a_in=kw['case_a'], b_in=kw['case_b'], 
                                                                        expected_obj=kw['exp_obj'], case_name=kw['c_name']),
                                expect_pass=True, 
                                div_variant_name=variant_name_key, 
                                dfv=div_func_actual, 
                                case_a=a_val, case_b=b_val, exp_obj=current_exp_obj, c_name=current_name_sfx)
            
            print(f"  -- Round Trip Tests for {variant_name_key} --")
            for a_tok_rt,b_tok_rt,exp_rt_b_val,exp_rt_a_val,exp_rt_c_val,exp_rt_d_val,exp_rt_e_val,name_sfx_rt_val in rt_test_definitions:
                a_val_rt,b_val_rt = dfi_map.get(a_tok_rt), dfi_map.get(b_tok_rt)

                if (isinstance(a_tok_rt,str)and "DFI" in a_tok_rt and a_val_rt is None) or \
                   (isinstance(b_tok_rt,str)and "DFI" in b_tok_rt and b_val_rt is None):
                    run_test_R3_MaxPlus(variant_name_key,f"RT: {name_sfx_rt_val} SKIPPED",omega_val_test,
                                    lambda o,**kw:(True,"N/A DFI for this Omega"), # test_func returns tuple
                                    expect_pass=True,div_variant_name=variant_name_key,dfv=div_func_actual)
                    continue

                exp_rt_map={"Spec(v1.2B)":exp_rt_b_val,"AltA(UnivSat)":exp_rt_a_val,
                            "AltC(V1.0Like)":exp_rt_c_val,"AltD(Balanced)":exp_rt_d_val,
                            "AltE(DivAspDet)":exp_rt_e_val}
                # THIS IS THE LINE FROM THE TRACEBACK (approx line 274 in a combined script)
                current_exp_rt_law_holds = exp_rt_map[variant_name_key] # Corrected from current_expect_rt_law_holds

                run_test_R3_MaxPlus(variant_name_key, f"RT: {name_sfx_rt_val}", omega_val_test,
                                lambda o, **kw: check_div_round_trip_case_R3_MaxPlus(o, div_func_variant=kw['dfv'], 
                                                                          a_in=kw['case_a'], b_in=kw['case_b'], 
                                                                          expect_rt_law_to_hold_itself=kw['exp_rt_law'], case_name=kw['c_name']),
                                expect_pass=True, 
                                div_variant_name=variant_name_key, 
                                dfv=div_func_actual, 
                                case_a=a_val_rt, case_b=b_val_rt, exp_rt_law=current_exp_rt_law_holds, c_name=name_sfx_rt_val)

    print("\n\n--- Overall Native Test Summary (R3 MaxPlus: Div Aspect Comparison) ---")
    for suite_key, results in sorted(test_results_R3_MaxPlus.items()):
        print(f"  {suite_key}: Passed={results['passed']}, Failed={results['failed']}, Skipped={results['skipped']}, Errors={results['errors']}")
    print("\n====== R3 MaxPlus Script Finished ======")