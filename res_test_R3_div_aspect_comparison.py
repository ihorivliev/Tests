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

Omega_R3: int = 0

def set_avca_omega_R3(omega_value: int, verbose=False):
    global Omega_R3
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R3 parameter must be an integer >= 1.")
    Omega_R3 = omega_value
    if verbose: print(f"R3 Test: Omega_R3 set to {Omega_R3}")

def _check_val_R3(x: AVCVal, current_omega: int, op_name: str = "op", arg_name:str = "input"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R3 for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid {arg_name} for {op_name}:{x!r}")
    if current_omega==1: raise ValueError(f"Invalid DFI {arg_name} for {op_name} Omega_R3=1:{x}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI {arg_name} for {op_name}:{x}, Omega_R3={current_omega}")

# --- Standard Multiplication (v1.2 "Areo Dominates") for Round-Trip Tests ---
def avc_mul_v1_2_R3(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R3; _check_val_R3(a,Omega_R3,"mul_v12(a)","a"); _check_val_R3(b,Omega_R3,"mul_v12(b)","b")
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_areo = a_is_u and a.aspect=="areo" # type: ignore
        b_is_areo = b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_is_areo or b_is_areo else ZERO_UNIO
    # DFI * DFI
    product = a * b # type: ignore
    return product if 1 <= product < Omega_R3 else AREO_UNIO

# --- Division Variants for Comparison ---

# Common DFI/DFI division logic (problematic cases to AREO_UNIO)
def _dfi_div_logic_R3(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal:
    if b_dfi == 0: raise ZeroDivisionError("DFI division by zero attempted in _dfi_div_logic_R3")
    quotient, remainder = divmod(a_dfi, b_dfi)
    if remainder == 0 and (1 <= quotient < current_omega):
        return quotient
    else: # Non-exact, or quotient 0, or quotient >= current_omega
        return AREO_UNIO

# R3.Spec: avc_div_v1_2B_R3 (Current Specification)
def avc_div_v1_2B_R3(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R3
    _check_val_R3(a,Omega_R3,"div_v12B(a)","a"); _check_val_R3(b,Omega_R3,"div_v12B(b)","b")
    if isinstance(b,Unio): return AREO_UNIO # Rule B1: Divisor Unio -> AREO_UNIO
    if isinstance(a,Unio): # Rule B2: Dividend Unio, Divisor DFI
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO # type: ignore
    return _dfi_div_logic_R3(a,b,Omega_R3) # type: ignore

# R3.AltA: "Universal Saturation on Unio Involvement"
def avc_div_R3_AltA_UnivSat(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R3
    _check_val_R3(a,Omega_R3,"div_AltA(a)","a"); _check_val_R3(b,Omega_R3,"div_AltA(b)","b")
    if isinstance(a,Unio) or isinstance(b,Unio):
        return AREO_UNIO
    return _dfi_div_logic_R3(a,b,Omega_R3) # type: ignore

# R3.AltC: "v1.0-like Dividend Priority for U/U, DFI/U -> AREO_UNIO"
def avc_div_R3_AltC_V1_0_like(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega_R3
    _check_val_R3(a,Omega_R3,"div_AltC(a)","a"); _check_val_R3(b,Omega_R3,"div_AltC(b)","b")
    if isinstance(a,Unio): # Dividend is Unio
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO # type: ignore (Preserves dividend aspect)
    elif isinstance(b,Unio): # Divisor is Unio (and dividend 'a' is DFI)
        return AREO_UNIO
    return _dfi_div_logic_R3(a,b,Omega_R3) # type: ignore

# --- Test Harness ---
test_results_R3 = {}
def run_test_R3(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R3
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R3: test_results_R3[suite_key] = {"passed":0,"failed":0,"skipped":0,"errors":0}
    variant_name = kwargs.get("div_variant_name", "N/A")
    full_test_name = f"{test_name} ({variant_name})"
    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_res_str = "PASS" if passes else "FAIL"
        exp_res_str = "PASS" if expect_pass else "FAIL"
        if passes == expect_pass:
            print(f"PASS (Observed: {actual_res_str})")
            test_results_R3[suite_key]["passed"] += 1
        else:
            print(f"FAIL (Observed: {actual_res_str}, Expected: {exp_res_str})")
            if detail: print(f"    Detail: {detail}")
            test_results_R3[suite_key]["failed"] += 1
    except Exception as e:
        print(f"ERROR ({type(e).__name__}: {e})"); test_results_R3[suite_key]["errors"] += 1
        # import traceback
        # traceback.print_exc()


def get_s_omega_R3(current_omega: int) -> List[AVCVal]:
    if current_omega == 1: return [ZERO_UNIO, AREO_UNIO] 
    return [ZERO_UNIO, AREO_UNIO] + list(range(1, current_omega))

# --- Native Python Property Test Functions ---
def check_div_totality(omega_val: int, div_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R3(omega_val)
    # For Omega=1, elements might be [Unio('zero'), Unio('areo')]. DFI is empty.
    # _check_val_R3 will raise error if DFI arg is passed for Omega=1.
    # The get_s_omega_R3 returns DFI only if omega_val > 1.
    
    for a in elements:
        for b in elements:
            try:
                # Skip DFI inputs if Omega is 1, as _check_val will prevent them.
                if omega_val == 1 and (isinstance(a, int) or isinstance(b, int)):
                    continue
                res = div_func_variant(a,b)
                _check_val_R3(res, omega_val, op_name=div_func_variant.__name__, arg_name="result")
            except ValueError as ve: # Catch _check_val errors or other ValueErrors
                # This indicates an issue if an op tried to use/produce invalid DFI
                return False, f"ValueError for {a!r} ÷ {b!r}: {ve}"
            except ZeroDivisionError as zde: # Should be caught by AVCA logic
                return False, f"ZeroDivisionError for {a!r} ÷ {b!r}: {zde}"
            except Exception as e: # Catch any other unexpected errors
                return False, f"Unexpected Error for {a!r} ÷ {b!r}: {type(e).__name__}({e})"
    return True, None

def check_div_specific_case(omega_val: int, div_func_variant: Callable, 
                            a_in: AVCVal, b_in: AVCVal, expected_obj: AVCVal, **kwargs) -> Tuple[bool, Any]:
    if omega_val == 1: # Adjust for Omega=1 if DFI inputs are involved
        if isinstance(a_in, int) or isinstance(b_in, int):
            return True, "N/A (DFI input for Ω=1)" # Skip DFI cases for Ω=1

    # Ensure inputs are valid for the current Omega before calling the op
    try:
        _check_val_R3(a_in, omega_val, op_name=div_func_variant.__name__, arg_name="a_in")
        _check_val_R3(b_in, omega_val, op_name=div_func_variant.__name__, arg_name="b_in")
    except ValueError: # Input itself is invalid for this Omega (e.g. DFI 2 for Omega=2)
        return True, f"N/A (Input {a_in!r} or {b_in!r} invalid for Ω={omega_val})"

    res = div_func_variant(a_in, b_in)
    if res is expected_obj: # Strict object identity check
        return True, None
    else:
        return False, f"{a_in!r} ÷ {b_in!r} -> {res!r} (Expected {expected_obj!r})"

def check_div_round_trip_case(omega_val: int, div_func_variant: Callable,
                              a_in: AVCVal, b_in: AVCVal, expect_rt_holds: bool, **kwargs) -> Tuple[bool, Any]:
    if omega_val == 1:
        if isinstance(a_in, int) or isinstance(b_in, int):
            return True, "N/A (DFI input for Ω=1)"
    try:
        _check_val_R3(a_in, omega_val, "rt_a_in"); _check_val_R3(b_in, omega_val, "rt_b_in")
    except ValueError:
         return True, f"N/A (Input {a_in!r} or {b_in!r} invalid for Ω={omega_val} for RT)"

    q = div_func_variant(a_in, b_in)
    lhs = avc_mul_v1_2_R3(q, b_in) # Use standard mul for the check

    # Algebraic equality for the round-trip check
    if (isinstance(lhs, Unio) and isinstance(a_in, Unio)) or (lhs == a_in):
        return expect_rt_holds, None # Property holds if expected
    else:
        return not expect_rt_holds, f"({a_in!r}÷{b_in!r})⊗{b_in!r} = ({q!r})⊗{b_in!r} = {lhs!r} != {a_in!r}"


# --- Test Execution ---
if __name__ == "__main__":
    print("====== AVCA R3: Division Aspect Handling Comparison ======")
    # Ω=1 can be tricky due to no DFI, so test carefully. Focus on Ω >= 2 for DFI interactions.
    omegas_to_test = [1, 2, 3, 5] 

    div_variants = {
        "⊘_v1.2B (Spec)": avc_div_v1_2B_R3,
        "⊘_AltA (UnivSat)": avc_div_R3_AltA_UnivSat,
        "⊘_AltC (V1.0Like)": avc_div_R3_AltC_V1_0_like,
    }

    # Test Cases based on properties 1-10 (see thought process)
    # (a_in, b_in, expected_obj_for_v12B, expected_obj_for_AltA, expected_obj_for_AltC, test_name_suffix)
    # DFI values used: 1, 2, (Omega-1)
    # For Ω=1, DFI cases will be skipped by check_div_specific_case
    
    # Helper to get a DFI value if possible
    def get_dfi(val, omega): return val if omega > val and val >=1 else (1 if omega > 1 else None)

    for omega_val_test in omegas_to_test:
        set_avca_omega_R3(omega_val_test)
        print(f"\n--- Native Tests for Ω = {omega_val_test} ---")

        dfi1 = get_dfi(1, omega_val_test)
        dfi2 = get_dfi(2, omega_val_test)
        dfi_om_minus_1 = get_dfi(omega_val_test - 1, omega_val_test)

        test_scenarios = []
        # Property 1: Totality (covered by a dedicated test)

        # Property 2: DFI/DFI logic
        if dfi1 and dfi2 : # e.g. Ω=3+, 1/2 -> AU; Ω=5+, 2/4 -> AU (q=0)
             test_scenarios.append((dfi1, dfi2, AREO_UNIO, AREO_UNIO, AREO_UNIO, "DFI(1)/DFI(2) -> AU"))
        if dfi_om_minus_1 and dfi2 and omega_val_test >=4 : # e.g. Ω=4, 3/2 -> AU (non-exact)
            if divmod(dfi_om_minus_1, dfi2)[1] != 0 : # If truly non-exact
                 test_scenarios.append((dfi_om_minus_1, dfi2, AREO_UNIO, AREO_UNIO, AREO_UNIO, f"DFI({dfi_om_minus_1})/DFI({dfi2}) non-exact -> AU"))
        if dfi2 and dfi1: # e.g. Ω=3+, 2/1 -> 2
             test_scenarios.append((dfi2, dfi1, dfi2, dfi2, dfi2, "DFI(2)/DFI(1) -> DFI(2)"))


        # Property 3: ZERO_UNIO / DFI_k
        if dfi1: test_scenarios.append((ZERO_UNIO, dfi1, ZERO_UNIO, AREO_UNIO, ZERO_UNIO, "ZU/DFI(1)"))
        # Property 4: AREO_UNIO / DFI_k
        if dfi1: test_scenarios.append((AREO_UNIO, dfi1, AREO_UNIO, AREO_UNIO, AREO_UNIO, "AU/DFI(1)"))
        # Property 5: DFI_k / ZERO_UNIO
        if dfi1: test_scenarios.append((dfi1, ZERO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "DFI(1)/ZU"))
        # Property 6: DFI_k / AREO_UNIO
        if dfi1: test_scenarios.append((dfi1, AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "DFI(1)/AU"))
        
        # Property 7: ZERO_UNIO / ZERO_UNIO
        test_scenarios.append((ZERO_UNIO, ZERO_UNIO, AREO_UNIO, AREO_UNIO, ZERO_UNIO, "ZU/ZU"))
        # Property 8: AREO_UNIO / AREO_UNIO
        test_scenarios.append((AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "AU/AU"))
        # Property 9: ZERO_UNIO / AREO_UNIO
        test_scenarios.append((ZERO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, ZERO_UNIO, "ZU/AU"))
        # Property 10: AREO_UNIO / ZERO_UNIO
        test_scenarios.append((AREO_UNIO, ZERO_UNIO, AREO_UNIO, AREO_UNIO, AREO_UNIO, "AU/ZU"))


        for variant_name, div_func in div_variants.items():
            print(f"-- Variant: {variant_name} --")
            run_test_R3(variant_name, f"Totality of {variant_name}", omega_val_test,
                        lambda o, **kw: check_div_totality(o, div_func_variant=div_func), 
                        expect_pass=True, div_variant_name=variant_name)

            for a_in, b_in, exp_v12b, exp_alta, exp_altc, name_suffix in test_scenarios:
                expected_object_for_current_variant = None
                if variant_name == "⊘_v1.2B (Spec)": expected_object_for_current_variant = exp_v12b
                elif variant_name == "⊘_AltA (UnivSat)": expected_object_for_current_variant = exp_alta
                elif variant_name == "⊘_AltC (V1.0Like)": expected_object_for_current_variant = exp_altc
                
                if expected_object_for_current_variant is None and isinstance(a_in,int) and isinstance(b_in,int): # DFI/DFI cases where result is DFI
                    if divmod(a_in,b_in)[1] == 0 and 1 <= divmod(a_in,b_in)[0] < omega_val_test:
                        expected_object_for_current_variant = divmod(a_in,b_in)[0]


                run_test_R3(variant_name, f"Case: {name_suffix}", omega_val_test,
                            lambda o, **kw: check_div_specific_case(o, div_func_variant=div_func, 
                                                                    a_in=kw['case_a'], b_in=kw['case_b'], 
                                                                    expected_obj=kw['exp_obj']),
                            expect_pass=True, # The test passes if observed object IS expected_object
                            div_variant_name=variant_name, 
                            case_a=a_in, case_b=b_in, exp_obj=expected_object_for_current_variant)
            
            # Round Trip Tests
            print(f"  -- Round Trip Tests for {variant_name} --")
            # Case 1: Clean DFI
            if dfi2 and dfi1 and omega_val_test >=2 and divmod(dfi2,dfi1)[0] == 2 : # e.g. 2/1=2 for Omega >=3
                 # For (2⊘1)⊗1 = 2. All variants should make 2⊘1=2. Then 2⊗1=2. Should hold.
                run_test_R3(variant_name, "RT: (DFI(2)⊘DFI(1))⊗DFI(1)==DFI(2)", omega_val_test,
                            lambda o, **kw: check_div_round_trip_case(o, div_func_variant=div_func, a_in=dfi2, b_in=dfi1, expect_rt_holds=True),
                            expect_pass=True, div_variant_name=variant_name)
            
            # Case 2: ZU / DFI
            if dfi1:
                # v1.2B: (ZU/DFI1)⊗DFI1 = ZU⊗DFI1 = ZU. Holds.
                # AltA: (AU/DFI1)⊗DFI1 = AU⊗DFI1 = AU. Fails (AU != ZU).
                # AltC: (ZU/DFI1)⊗DFI1 = ZU⊗DFI1 = ZU. Holds.
                expect_rt_zu_dfi_pass = (variant_name != "⊘_AltA (UnivSat)")
                run_test_R3(variant_name, "RT: (ZU⊘DFI(1))⊗DFI(1)==ZU", omega_val_test,
                            lambda o, **kw: check_div_round_trip_case(o, div_func_variant=div_func, a_in=ZERO_UNIO, b_in=dfi1, expect_rt_holds=expect_rt_zu_dfi_pass),
                            expect_pass=expect_rt_zu_dfi_pass, div_variant_name=variant_name)

            # Case 3: DFI / ZU -> result U. Then U * ZU -> U (possibly ZU or AU). Original DFI != U. Fails.
            if dfi1:
                run_test_R3(variant_name, "RT: (DFI(1)⊘ZU)⊗ZU==DFI(1)", omega_val_test,
                            lambda o, **kw: check_div_round_trip_case(o, div_func_variant=div_func, a_in=dfi1, b_in=ZERO_UNIO, expect_rt_holds=False),
                            expect_pass=False, div_variant_name=variant_name)


    print("\n\n--- Overall Native Test Summary (R3: Div Aspect Comparison) ---")
    for suite_key, results in sorted(test_results_R3.items()):
        print(f"  {suite_key}: Passed={results['passed']}, Failed={results['failed']}, Skipped={results['skipped']}, Errors={results['errors']}")
    
    print("\nNote: SMT tests for R3 variants would require specific SMT logic builders for each div_variant and are omitted from this script for focus on native comparison of output objects/aspects.")
    print("\n====== R3 Script Finished ======")