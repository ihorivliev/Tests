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

Omega_R1_DeepDive: int = 0

def set_avca_omega_R1_DeepDive(omega_value: int, verbose=False):
    global Omega_R1_DeepDive
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R1_DeepDive parameter must be an integer >= 1.")
    Omega_R1_DeepDive = omega_value
    if verbose: print(f"R1 DeepDive Test: Omega_R1_DeepDive set to {Omega_R1_DeepDive}")

def _check_val_R1_DeepDive(x: AVCVal, current_omega: int, op_name: str = "op", arg_name:str = "input"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R1_DeepDive for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid {arg_name} for {op_name}:{x!r} (type {type(x)}) for Ω={current_omega}")
    if current_omega==1 and isinstance(x,int): raise ValueError(f"Invalid DFI {arg_name} for {op_name} Omega_R1_DeepDive=1: {x!r}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI {arg_name} for {op_name}:{x!r}, Omega_R1_DeepDive={current_omega}, DFI range [1, {current_omega-1}]")

# --- Context Operations for R1 Deep Dive ---
def avc_sub_fixed_R1(a: AVCVal, b: AVCVal) -> AVCVal: # Standard v1.0
    global Omega_R1_DeepDive; _check_val_R1_DeepDive(a,Omega_R1_DeepDive); _check_val_R1_DeepDive(b,Omega_R1_DeepDive)
    if isinstance(b,Unio): return a
    if isinstance(a,Unio): return AREO_UNIO 
    return (a-b) if a>b else AREO_UNIO # type: ignore

def avc_mul_fixed_R1(a: AVCVal, b: AVCVal) -> AVCVal: # Standard v1.2 "Areo Dominates"
    global Omega_R1_DeepDive; _check_val_R1_DeepDive(a,Omega_R1_DeepDive); _check_val_R1_DeepDive(b,Omega_R1_DeepDive)
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_areo = a_is_u and a.aspect=="areo"; b_is_areo = b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_is_areo or b_is_areo else ZERO_UNIO
    p=a*b; return p if 1<=p<Omega_R1_DeepDive else AREO_UNIO # type: ignore

def _dfi_div_logic_R1_DeepDive(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal:
    if b_dfi == 0: raise ZeroDivisionError("DFI division by zero")
    q,r=divmod(a_dfi,b_dfi); return q if r==0 and 1<=q<current_omega else AREO_UNIO

def avc_div_AltD_fixed_R1(a: AVCVal, b: AVCVal) -> AVCVal: # AltD Logic
    global Omega_R1_DeepDive
    _check_val_R1_DeepDive(a,Omega_R1_DeepDive,"div_AltD(a)","a"); _check_val_R1_DeepDive(b,Omega_R1_DeepDive,"div_AltD(b)","b")
    if isinstance(b, int): 
        if a is ZERO_UNIO: return ZERO_UNIO      
        if a is AREO_UNIO: return AREO_UNIO      
        if isinstance(a, int): return _dfi_div_logic_R1_DeepDive(a,b,Omega_R1_DeepDive) 
    elif isinstance(b, Unio):
        if isinstance(a, int): return AREO_UNIO  
        elif isinstance(a, Unio): 
            if b.aspect == "areo": return AREO_UNIO 
            else: return a 
    raise RuntimeError(f"Internal logic error in avc_div_AltD_fixed_R1 with a={a!r}, b={b!r}")

# --- Addition Variants for Comparison ---
def avc_add_v1_1_deep(a: AVCVal, b: AVCVal) -> AVCVal: # Overflow to AREO_UNIO
    global Omega_R1_DeepDive; _check_val_R1_DeepDive(a,Omega_R1_DeepDive); _check_val_R1_DeepDive(b,Omega_R1_DeepDive)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R1_DeepDive else AREO_UNIO # type: ignore

def avc_add_v1_0_deep(a: AVCVal, b: AVCVal) -> AVCVal: # Overflow to ZERO_UNIO
    global Omega_R1_DeepDive; _check_val_R1_DeepDive(a,Omega_R1_DeepDive); _check_val_R1_DeepDive(b,Omega_R1_DeepDive)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R1_DeepDive else ZERO_UNIO # type: ignore

# --- Test Harness & Helper ---
test_results_R1_DeepDive = {}
# ... (run_test_R1_DeepDive - same as run_test_R1_AltDContext, just change dict name) ...
def run_test_R1_DeepDive(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R1_DeepDive # Changed dict name
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R1_DeepDive: test_results_R1_DeepDive[suite_key] = {"passed":0,"failed":0,"skipped":0,"errors":0}
    op_var_name = kwargs.get("op_variant_name", "")
    full_test_name = f"{test_name} ({op_var_name})" if op_var_name else test_name
    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_res_str="PASS" if passes else "FAIL"; exp_res_str="PASS" if expect_pass else "FAIL"
        if passes == expect_pass:
            print(f"PASS (Observed: {actual_res_str})"); test_results_R1_DeepDive[suite_key]["passed"]+=1
        else:
            print(f"FAIL (Observed: {actual_res_str}, Expected: {exp_res_str})")
            if detail: print(f"    Detail: {detail}")
            test_results_R1_DeepDive[suite_key]["failed"]+=1
    except Exception as e: print(f"ERROR ({type(e).__name__}: {e})"); test_results_R1_DeepDive[suite_key]["errors"]+=1

def get_s_omega_R1_DeepDive(current_omega: int) -> List[AVCVal]: # Same
    if current_omega == 1: return [ZERO_UNIO] 
    return [ZERO_UNIO, AREO_UNIO] + list(range(1, current_omega)) # Add AREO for interaction tests

# --- Property Test Functions ---
def check_associativity_R1_Deep(omega_val: int, add_func_variant: Callable, **kwargs) -> Tuple[bool, Any]: # Same
    elements = get_s_omega_R1_DeepDive(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try:
            if omega_val==1 and any(isinstance(x,int) for x in [a,b,c]): continue
            lhs=add_func_variant(add_func_variant(a,b),c); rhs=add_func_variant(a,add_func_variant(b,c))
            if lhs != rhs: return False, f"a={a!r},b={b!r},c={c!r} -> LHS={lhs!r},RHS={rhs!r}"
        except ValueError as e:
            if omega_val==1 and isinstance(a,Unio) and isinstance(b,Unio) and isinstance(c,Unio): pass
            else: return False, f"ValueError: a={a!r},b={b!r},c={c!r} -> {e}"
    return True, None

def check_strict_uniformity_R1_Deep(omega_val: int, add_func_variant: Callable, **kwargs) -> Tuple[bool, Any]: # Same test logic
    if omega_val < 2: return True, "N/A or vacuously true for Ω<2"
    all_strictly_AREO = True; details = []; add_op_name = add_func_variant.__name__
    add_pairs=[(1,omega_val-1),(omega_val-1,omega_val-1)] if omega_val>2 else ([(1,1)] if omega_val==2 else [])
    if omega_val==3 and (2,2) not in add_pairs : add_pairs.append((2,2))
    for a,b in add_pairs:
        if not(1<=a<omega_val and 1<=b<omega_val):continue
        if not(add_func_variant(a,b) is AREO_UNIO): all_strictly_AREO=False;details.append(f"{add_op_name}({a},{b})->{add_func_variant(a,b)!r} (not IS AREO)");break
    if not all_strictly_AREO: return False, ", ".join(details)
    sub_pairs=[(1,1)]+([(1,2)] if omega_val>2 else [])
    for a,b in sub_pairs:
        if not(1<=a<omega_val and 1<=b<omega_val):continue
        if not(avc_sub_fixed_R1(a,b) is AREO_UNIO):all_strictly_AREO=False;details.append(f"Sub({a},{b})->{avc_sub_fixed_R1(a,b)!r}");break
    if not all_strictly_AREO: return False, ", ".join(details)
    mul_pairs=[];
    if omega_val==3: mul_pairs=[(2,2)]
    elif omega_val==4: mul_pairs=[(2,2),(2,3),(3,3)]
    elif omega_val>=5: mul_pairs=[(2,omega_val-1 if 2*(omega_val-1)>=omega_val else (omega_val+1)//2),( (omega_val+1)//2, (omega_val+1)//2 ) ]
    if omega_val>1 and (omega_val-1)*(omega_val-1)>=omega_val: 
        if (omega_val-1,omega_val-1) not in mul_pairs : mul_pairs.append((omega_val-1,omega_val-1))
    for a,b in list(set(mul_pairs)):
        if not(1<=a<omega_val and 1<=b<omega_val and a*b>=omega_val):continue
        if not(avc_mul_fixed_R1(a,b) is AREO_UNIO):all_strictly_AREO=False;details.append(f"Mul({a},{b})->{avc_mul_fixed_R1(a,b)!r}");break
    if not all_strictly_AREO: return False, ", ".join(details)
    div_pairs=[];
    if omega_val>=3:div_pairs.append((1,2))
    if omega_val>=4:div_pairs.append((3,2))
    for a,b in div_pairs:
        if not(1<=a<omega_val and 1<=b<omega_val and b!=0):continue
        q_t,r_t=divmod(a,b);
        if r_t==0 and 1<=q_t<omega_val:continue
        if not(avc_div_AltD_fixed_R1(a,b) is AREO_UNIO):all_strictly_AREO=False;details.append(f"DivAltD({a},{b})->{avc_div_AltD_fixed_R1(a,b)!r}");break
    if not all_strictly_AREO: return False, ", ".join(details)
    return True, None

# NEW: Chained Operation Semantic Tests
# NEW: Chained Operation Semantic Tests
# NEW: Chained Operation Semantic Tests
def check_chained_op_semantics(omega_val: int, add_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    if omega_val == 1: # No DFI available for dfi_x, dfi_y assignment
            return True, f"N/A for Ω=1 (no DFI for initial overflow to chain)"
    # For Omega=2, DFI_x=1, DFI_y=1. Sum = 2 (overflow).
    # For Omega>=3: DFI_x=1, DFI_y=Omega-1. Sum = Omega (overflow).
    dfi_x = 1
    dfi_y = 1 if omega_val == 2 else (omega_val - 1)
    
    # Ensure DFI values are valid for the current Omega before using them
    # This check is mostly for safety if omega_val was < 2, but handled by the first if.
    try:
        _check_val_R1_DeepDive(dfi_x, omega_val, "chained_op_dfi_x_setup", "dfi_x")
        _check_val_R1_DeepDive(dfi_y, omega_val, "chained_op_dfi_y_setup", "dfi_y")
    except ValueError: # Should not happen for omega_val >= 2 with these dfi_x, dfi_y
        return False, f"Setup error with DFI values for Ω={omega_val}"

    U_overflow = add_func_variant(dfi_x, dfi_y)
    
    res_mul_zero = avc_mul_fixed_R1(U_overflow, ZERO_UNIO)
    res_mul_areo = avc_mul_fixed_R1(U_overflow, AREO_UNIO)
    res_div_zero = avc_div_AltD_fixed_R1(U_overflow, ZERO_UNIO)
    res_div_areo = avc_div_AltD_fixed_R1(U_overflow, AREO_UNIO)

    # Corrected function names for comparison:
    if add_func_variant is avc_add_v1_1_deep: # CORRECTED NAME
        expected_U_overflow = AREO_UNIO
        expected_res_mul_zero = AREO_UNIO 
        expected_res_mul_areo = AREO_UNIO
        expected_res_div_zero = AREO_UNIO # AltD: AREO_UNIO / ZERO_UNIO -> AREO_UNIO
        expected_res_div_areo = AREO_UNIO # AltD: AREO_UNIO / AREO_UNIO -> AREO_UNIO
        
        if (U_overflow is expected_U_overflow) and \
           (res_mul_zero is expected_res_mul_zero) and \
           (res_mul_areo is expected_res_mul_areo) and \
           (res_div_zero is expected_res_div_zero) and \
           (res_div_areo is expected_res_div_areo):
            return True, f"v1.1 add: U_ov IS {U_overflow!r}. Chained results: ⊗ZU={res_mul_zero!r}, ⊗AU={res_mul_areo!r}, ⊘ZU={res_div_zero!r}, ⊘AU={res_div_areo!r} (All AREO as expected)"
        else:
            return False, f"v1.1 add MISMATCH: U_ov={U_overflow!r} (exp {expected_U_overflow!r}). Chained: ⊗ZU={res_mul_zero!r} (exp {expected_res_mul_zero!r}), ⊗AU={res_mul_areo!r} (exp {expected_res_mul_areo!r}), ⊘ZU={res_div_zero!r} (exp {expected_res_div_zero!r}), ⊘AU={res_div_areo!r} (exp {expected_res_div_areo!r})"
    
    elif add_func_variant is avc_add_v1_0_deep: # CORRECTED NAME
        expected_U_overflow = ZERO_UNIO
        expected_res_mul_zero = ZERO_UNIO # v1.2 mul: ZERO_UNIO ⊗ ZERO_UNIO -> ZERO_UNIO
        expected_res_mul_areo = AREO_UNIO # v1.2 mul: ZERO_UNIO ⊗ AREO_UNIO -> AREO_UNIO
        expected_res_div_zero = ZERO_UNIO # AltD: ZERO_UNIO ⊘ ZERO_UNIO -> ZERO_UNIO
        expected_res_div_areo = AREO_UNIO # AltD: ZERO_UNIO ⊘ AREO_UNIO -> AREO_UNIO

        if (U_overflow is expected_U_overflow) and \
           (res_mul_zero is expected_res_mul_zero) and \
           (res_mul_areo is expected_res_mul_areo) and \
           (res_div_zero is expected_res_div_zero) and \
           (res_div_areo is expected_res_div_areo):
            return True, f"v1.0 add: U_ov IS {U_overflow!r}. Chained results: ⊗ZU={res_mul_zero!r}, ⊗AU={res_mul_areo!r}, ⊘ZU={res_div_zero!r}, ⊘AU={res_div_areo!r} (Aspects propagate as expected)"
        else:
            return False, f"v1.0 add MISMATCH: U_ov={U_overflow!r} (exp {expected_U_overflow!r}). Chained: ⊗ZU={res_mul_zero!r} (exp {expected_res_mul_zero!r}), ⊗AU={res_mul_areo!r} (exp {expected_res_mul_areo!r}), ⊘ZU={res_div_zero!r} (exp {expected_res_div_zero!r}), ⊘AU={res_div_areo!r} (exp {expected_res_div_areo!r})"
    
    return False, f"Unknown add_func_variant '{add_func_variant.__name__}' in check_chained_op_semantics"


# --- Main Execution Block ---
if __name__ == "__main__":
    print("====== AVCA R1 Deep Dive: Add Overflow vs AltD Div & Chained Ops (Corrected) ======")
    omegas_to_test = [1, 2, 3, 4, 5]

    for omega_val_test in omegas_to_test:
        set_avca_omega_R1_DeepDive(omega_val_test)
        print(f"\n--- Testing for Ω = {omega_val_test} ---")

        # Test with avc_add_v1_1_deep (Overflow to AREO_UNIO)
        variant_name_v11 = "⊕_v1.1 (OvflwAREO)"
        run_test_R1_DeepDive("Assoc_Test", "Associativity", omega_val_test, 
                             lambda o, **kw: check_associativity_R1_Deep(o, add_func_variant=avc_add_v1_1_deep), # Corrected name
                             expect_pass=(omega_val_test <= 2), op_variant_name=variant_name_v11)
        run_test_R1_DeepDive("StrictUniformity_Test", "DFI Breach STRICT Uniformity (div=AltD)", omega_val_test,
                             lambda o, **kw: check_strict_uniformity_R1_Deep(o, add_func_variant=avc_add_v1_1_deep), # Corrected name
                             expect_pass=True, op_variant_name=variant_name_v11)
        run_test_R1_DeepDive("ChainedOp_Semantic_Test", "Chained Op Semantics", omega_val_test,
                             lambda o, **kw: check_chained_op_semantics(o, add_func_variant=avc_add_v1_1_deep), # Corrected name
                             expect_pass=True, op_variant_name=variant_name_v11)


        # Test with avc_add_v1_0_deep (Overflow to ZERO_UNIO)
        variant_name_v10 = "⊕_v1.0 (OvflwZERO)"
        run_test_R1_DeepDive("Assoc_Test", "Associativity", omega_val_test,
                             lambda o, **kw: check_associativity_R1_Deep(o, add_func_variant=avc_add_v1_0_deep), # Corrected name
                             expect_pass=(omega_val_test <= 2), op_variant_name=variant_name_v10)
        run_test_R1_DeepDive("StrictUniformity_Test", "DFI Breach STRICT Uniformity (div=AltD)", omega_val_test,
                             lambda o, **kw: check_strict_uniformity_R1_Deep(o, add_func_variant=avc_add_v1_0_deep), # Corrected name
                             expect_pass=False, op_variant_name=variant_name_v10)
        run_test_R1_DeepDive("ChainedOp_Semantic_Test", "Chained Op Semantics", omega_val_test,
                             lambda o, **kw: check_chained_op_semantics(o, add_func_variant=avc_add_v1_0_deep), # Corrected name
                             expect_pass=True, op_variant_name=variant_name_v10)


    print("\n\n--- Overall Test Summary (R1 Deep Dive: Add Overflow vs AltD Div & Chained Ops) ---")
    for suite_key, results in sorted(test_results_R1_DeepDive.items()):
        print(f"  {suite_key}: Passed={results['passed']}, Failed={results['failed']}, Skipped={results['skipped']}, Errors={results['errors']}")
    
    print("\n====== R1 Deep Dive Script Finished ======")