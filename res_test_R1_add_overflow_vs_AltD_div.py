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

Omega_R1_AltDContext: int = 0

def set_avca_omega_R1_AltDContext(omega_value: int, verbose=False):
    global Omega_R1_AltDContext
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_R1_AltDContext parameter must be an integer >= 1.")
    Omega_R1_AltDContext = omega_value
    if verbose: print(f"R1 vs AltD Test: Omega_R1_AltDContext set to {Omega_R1_AltDContext}")

def _check_val_R1_AltDContext(x: AVCVal, current_omega: int, op_name: str = "op", arg_name:str = "input"):
    if not isinstance(current_omega,int) or current_omega<1: raise ValueError(f"Omega_R1_AltDContext for {op_name} error")
    if isinstance(x,Unio): return
    if not isinstance(x,int): raise TypeError(f"Invalid {arg_name} for {op_name}:{x!r} (type {type(x)}) for Ω={current_omega}")
    if current_omega==1 and isinstance(x,int): raise ValueError(f"Invalid DFI {arg_name} for {op_name} Omega_R1_AltDContext=1: {x!r}")
    if not (1<=x<current_omega): raise ValueError(f"Invalid DFI {arg_name} for {op_name}:{x!r}, Omega_R1_AltDContext={current_omega}, DFI range [1, {current_omega-1}]")

# --- Standard Operations (sub, mul) and AltD Division ---
def avc_sub_v1_0_R1_AltD(a: AVCVal, b: AVCVal) -> AVCVal: 
    global Omega_R1_AltDContext; _check_val_R1_AltDContext(a,Omega_R1_AltDContext); _check_val_R1_AltDContext(b,Omega_R1_AltDContext)
    if isinstance(b,Unio): return a
    if isinstance(a,Unio): return AREO_UNIO 
    return (a-b) if a>b else AREO_UNIO # type: ignore

def avc_mul_v1_2_R1_AltD(a: AVCVal, b: AVCVal) -> AVCVal: 
    global Omega_R1_AltDContext; _check_val_R1_AltDContext(a,Omega_R1_AltDContext); _check_val_R1_AltDContext(b,Omega_R1_AltDContext)
    a_is_u=isinstance(a,Unio); b_is_u=isinstance(b,Unio)
    if a_is_u or b_is_u:
        a_is_areo = a_is_u and a.aspect=="areo" # type: ignore
        b_is_areo = b_is_u and b.aspect=="areo" # type: ignore
        return AREO_UNIO if a_is_areo or b_is_areo else ZERO_UNIO
    p=a*b; return p if 1<=p<Omega_R1_AltDContext else AREO_UNIO # type: ignore

def _dfi_div_logic_R1_AltD(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal:
    if b_dfi == 0: raise ZeroDivisionError("DFI division by zero")
    q,r=divmod(a_dfi,b_dfi); return q if r==0 and 1<=q<current_omega else AREO_UNIO

def avc_div_AltD_Balanced_R1(a: AVCVal, b: AVCVal) -> AVCVal: # AltD Logic
    global Omega_R1_AltDContext
    _check_val_R1_AltDContext(a,Omega_R1_AltDContext,"div_AltD(a)","a"); _check_val_R1_AltDContext(b,Omega_R1_AltDContext,"div_AltD(b)","b")
    if isinstance(b, int): 
        if a is ZERO_UNIO: return ZERO_UNIO      
        if a is AREO_UNIO: return AREO_UNIO      
        if isinstance(a, int): return _dfi_div_logic_R1_AltD(a,b,Omega_R1_AltDContext) 
    elif isinstance(b, Unio):
        if isinstance(a, int): return AREO_UNIO  
        elif isinstance(a, Unio): 
            if b.aspect == "areo": return AREO_UNIO 
            else: return a 
    raise RuntimeError(f"Internal logic error in avc_div_AltD_Balanced_R1 with a={a!r}, b={b!r}")

# --- Addition Variants for Comparison ---
def avc_add_v1_1_logic_R1_AltD(a: AVCVal, b: AVCVal) -> AVCVal: 
    global Omega_R1_AltDContext; _check_val_R1_AltDContext(a,Omega_R1_AltDContext); _check_val_R1_AltDContext(b,Omega_R1_AltDContext)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R1_AltDContext else AREO_UNIO # type: ignore

def avc_add_v1_0_logic_R1_AltD(a: AVCVal, b: AVCVal) -> AVCVal: 
    global Omega_R1_AltDContext; _check_val_R1_AltDContext(a,Omega_R1_AltDContext); _check_val_R1_AltDContext(b,Omega_R1_AltDContext)
    if isinstance(a,Unio): return b
    if isinstance(b,Unio): return a
    s=a+b; return s if s<Omega_R1_AltDContext else ZERO_UNIO # type: ignore

# --- Test Harness ---
test_results_R1_AltDContext = {}
def run_test_R1_AltDContext(test_suite_name: str, test_name: str, omega_val: int, test_func: Callable, expect_pass: bool = True, **kwargs):
    global test_results_R1_AltDContext
    suite_key = f"{test_suite_name}_O{omega_val}"
    if suite_key not in test_results_R1_AltDContext: test_results_R1_AltDContext[suite_key] = {"passed":0,"failed":0,"skipped":0,"errors":0}
    op_var_name = kwargs.get("op_variant_name", "")
    full_test_name = f"{test_name} ({op_var_name})" if op_var_name else test_name
    print(f"  TEST: '{full_test_name}' for Ω={omega_val} (Expect: {'PASS' if expect_pass else 'FAIL'})", end=" ... ")
    try:
        passes, detail = test_func(omega_val, **kwargs)
        actual_res_str="PASS" if passes else "FAIL"; exp_res_str="PASS" if expect_pass else "FAIL"
        if passes == expect_pass:
            print(f"PASS (Observed: {actual_res_str})"); test_results_R1_AltDContext[suite_key]["passed"]+=1
        else:
            print(f"FAIL (Observed: {actual_res_str}, Expected: {exp_res_str})")
            if detail: print(f"    Detail: {detail}")
            test_results_R1_AltDContext[suite_key]["failed"]+=1
    except Exception as e: print(f"ERROR ({type(e).__name__}: {e})"); test_results_R1_AltDContext[suite_key]["errors"]+=1

def get_s_omega_R1_AltDContext(current_omega: int) -> List[AVCVal]:
    if current_omega == 1: return [ZERO_UNIO] 
    return [ZERO_UNIO] + list(range(1, current_omega))

# --- Property Test Functions ---
def check_associativity_R1_AltD(omega_val: int, add_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    elements = get_s_omega_R1_AltDContext(omega_val)
    for a,b,c in itertools.product(elements, repeat=3):
        try:
            lhs=add_func_variant(add_func_variant(a,b),c); rhs=add_func_variant(a,add_func_variant(b,c))
            if lhs != rhs: return False, f"a={a!r},b={b!r},c={c!r} -> LHS={lhs!r},RHS={rhs!r}"
        except ValueError as e:
            if omega_val==1 and isinstance(a,Unio) and isinstance(b,Unio) and isinstance(c,Unio): pass
            else: return False, f"ValueError: a={a!r},b={b!r},c={c!r} -> {e}"
    return True, None

def check_strict_uniformity_to_AREO_with_AltD_div(omega_val: int, add_func_variant: Callable, **kwargs) -> Tuple[bool, Any]:
    if omega_val < 2: return True, "N/A or vacuously true for Ω<2"
    
    all_strictly_AREO = True; details = []
    add_op_name = add_func_variant.__name__

    # 1. Additive Overflow
    add_pairs = [(1,omega_val-1), (omega_val-1,omega_val-1)] if omega_val > 2 else ([(1,1)] if omega_val==2 else [])
    for a,b in add_pairs:
        if not(1<=a<omega_val and 1<=b<omega_val): continue
        res = add_func_variant(a,b)
        if not (res is AREO_UNIO): all_strictly_AREO=False; details.append(f"{add_op_name}({a},{b})->{res!r} (not IS AREO_UNIO)"); break
    if not all_strictly_AREO: return False, ", ".join(details)

    # 2. Subtractive Underflow
    sub_pairs = [(1,1)] + ([(1,2)] if omega_val > 2 else [])
    for a,b in sub_pairs:
        if not(1<=a<omega_val and 1<=b<omega_val): continue
        res = avc_sub_v1_0_R1_AltD(a,b)
        if not (res is AREO_UNIO): all_strictly_AREO=False; details.append(f"Sub({a},{b})->{res!r}"); break
    if not all_strictly_AREO: return False, ", ".join(details)

    # 3. Multiplicative Overflow
    mul_pairs = []
    if omega_val==3: mul_pairs=[(2,2)]
    elif omega_val==4: mul_pairs=[(2,2),(2,3),(3,3)]
    elif omega_val>=5: mul_pairs=[(2,omega_val-1 if 2*(omega_val-1)>=omega_val else (omega_val+1)//2), ( (omega_val+1)//2, (omega_val+1)//2 ) ] # Heuristic
    if omega_val > 1 and (omega_val-1)*(omega_val-1) >= omega_val: mul_pairs.append((omega_val-1,omega_val-1))

    for a,b in list(set(mul_pairs)): # Unique pairs
        if not(1<=a<omega_val and 1<=b<omega_val and a*b >= omega_val): continue
        res = avc_mul_v1_2_R1_AltD(a,b)
        if not (res is AREO_UNIO): all_strictly_AREO=False; details.append(f"Mul({a},{b})->{res!r}"); break
    if not all_strictly_AREO: return False, ", ".join(details)

    # 4. Problematic Division (using AltD Division)
    div_pairs = []
    if omega_val>=3: div_pairs.append((1,2)) # q=0
    if omega_val>=4: div_pairs.append((3,2)) # non-exact
    
    for a,b in div_pairs:
        if not(1<=a<omega_val and 1<=b<omega_val and b!=0): continue
        q_temp,r_temp=divmod(a,b)
        if r_temp==0 and 1<=q_temp<omega_val: continue # Skip non-problematic
        res = avc_div_AltD_Balanced_R1(a,b) # Using AltD for this check
        if not (res is AREO_UNIO): all_strictly_AREO=False; details.append(f"DivAltD({a},{b})->{res!r}"); break
    if not all_strictly_AREO: return False, ", ".join(details)
    
    return True, None

# --- Main Execution Block ---
if __name__ == "__main__":
    print("====== AVCA R1 Revisited: Add Overflow vs AltD Division Uniformity ======")
    omegas_to_test = [1, 2, 3, 4, 5]

    for omega_val_test in omegas_to_test:
        set_avca_omega_R1_AltDContext(omega_val_test)
        print(f"\n--- Testing for Ω = {omega_val_test} ---")

        variant_name_v11 = "⊕_v1.1 (Overflow to AREO)"
        run_test_R1_AltDContext("Assoc_Test", "Associativity", omega_val_test, 
                                lambda o, **kw: check_associativity_R1_AltD(o, add_func_variant=avc_add_v1_1_logic_R1_AltD), 
                                expect_pass=(omega_val_test <= 2), op_variant_name=variant_name_v11)
        run_test_R1_AltDContext("StrictUniformity_AltD_Div", "DFI Breach STRICT Uniformity (all object IS AREO, div=AltD)", omega_val_test,
                                lambda o, **kw: check_strict_uniformity_to_AREO_with_AltD_div(o, add_func_variant=avc_add_v1_1_logic_R1_AltD),
                                expect_pass=True, op_variant_name=variant_name_v11)

        variant_name_v10 = "⊕_v1.0 (Overflow to ZERO)"
        run_test_R1_AltDContext("Assoc_Test", "Associativity", omega_val_test,
                                lambda o, **kw: check_associativity_R1_AltD(o, add_func_variant=avc_add_v1_0_logic_R1_AltD),
                                expect_pass=(omega_val_test <= 2), op_variant_name=variant_name_v10)
        run_test_R1_AltDContext("StrictUniformity_AltD_Div", "DFI Breach STRICT Uniformity (all object IS AREO, div=AltD)", omega_val_test,
                                lambda o, **kw: check_strict_uniformity_to_AREO_with_AltD_div(o, add_func_variant=avc_add_v1_0_logic_R1_AltD),
                                expect_pass=False, op_variant_name=variant_name_v10)

    print("\n\n--- Overall Test Summary (R1 Revisited: Add Overflow vs AltD Div Uniformity) ---")
    for suite_key, results in sorted(test_results_R1_AltDContext.items()):
        print(f"  {suite_key}: Passed={results['passed']}, Failed={results['failed']}, Skipped={results['skipped']}, Errors={results['errors']}")
    print("\n====== R1 Revisited Script Finished ======")