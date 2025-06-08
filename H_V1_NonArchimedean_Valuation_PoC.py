# H_V1_NonArchimedean_Valuation_PoC.py
# Python Proof-of-Concept for Hypothesis H-V1.
# Tests:
# 1. v(x ⊕ y) >= min(v(x), v(y)) (ultrametric for addition)
# 2. v(x ⊗ y) = v(x) + v(y) (strong property for multiplication)
# Using "Best Combination" AVCA kernel.

import math
from typing import Literal, Union, Any, List, Tuple, Dict

# --- AVCA Core Components (from Appendix S.A "Best Combination") ---
_Omega_BC_H_V1: int = 0

class Unio_H_V1: # Renamed for this script
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_H_V1 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_H_V1)
    def __hash__(self) -> int:
        # For H_V1, distinct ZU/AU objects might need distinct v() if "signed residue" is used.
        # For now, our v() function will distinguish them by object identity.
        return hash((type(self), self.aspect))
    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"
    def __lt__(self, other): 
        if isinstance(other, Unio_H_V1):
            return self.aspect == "zero" and other.aspect == "areo"
        if isinstance(other, int): 
            return True 
        return NotImplemented

ZERO_UNIO_H_V1 = Unio_H_V1("zero")
AREO_UNIO_H_V1 = Unio_H_V1("areo")
AVCVal_H_V1 = Union[int, Unio_H_V1]

def set_avca_omega_bc_H_V1(omega_value: int, verbose: bool = False):
    global _Omega_BC_H_V1
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_BC_H_V1 parameter must be an integer >= 1.")
    _Omega_BC_H_V1 = omega_value
    if verbose:
        print(f"H_V1 Test: Omega_BC_H_V1 set to {_Omega_BC_H_V1}")

def _check_val_bc_H_V1(x: AVCVal_H_V1, current_omega: int, op_name:str="op", arg_name:str="input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega for {op_name} must be >= 1. Got: {current_omega!r}")
    if isinstance(x, Unio_H_V1): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid {arg_name} for {op_name}: {x!r} (type {type(x)}) for Ω={current_omega}.")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI {arg_name} for {op_name} when Omega=1: {x!r}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI {arg_name} for {op_name}: {x!r}. For Omega={current_omega}, DFI in [1, {current_omega-1}].")

# AVCA Operations ("Best Combination" Logic)
def avc_add_v1_1_bc_H_V1(a: AVCVal_H_V1, b: AVCVal_H_V1) -> AVCVal_H_V1:
    global _Omega_BC_H_V1
    _check_val_bc_H_V1(a, _Omega_BC_H_V1, "add","a"); _check_val_bc_H_V1(b, _Omega_BC_H_V1, "add","b")
    if isinstance(a, Unio_H_V1): return b
    if isinstance(b, Unio_H_V1): return a
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < _Omega_BC_H_V1 else AREO_UNIO_H_V1

def avc_mul_v1_2_bc_H_V1(a: AVCVal_H_V1, b: AVCVal_H_V1) -> AVCVal_H_V1:
    global _Omega_BC_H_V1
    _check_val_bc_H_V1(a, _Omega_BC_H_V1, "mul","a"); _check_val_bc_H_V1(b, _Omega_BC_H_V1, "mul","b")
    a_is_unio = isinstance(a, Unio_H_V1); b_is_unio = isinstance(b, Unio_H_V1)
    if a_is_unio or b_is_unio:
        a_is_areo = a_is_unio and a.aspect == "areo" # type: ignore
        b_is_areo = b_is_unio and b.aspect == "areo" # type: ignore
        return AREO_UNIO_H_V1 if a_is_areo or b_is_areo else ZERO_UNIO_H_V1
    else:
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < _Omega_BC_H_V1 else AREO_UNIO_H_V1

# --- Valuation Function v(x) ---
# H-V1: "DFI part carries a non-archimedean valuation v(n)=-log n; 
# Unio tags correspond to v=-∞ and a signed residue.
# AU→−∞high, ZU→−∞low"
# For PoC, let's use large negative numbers for -∞.
# If ZU < AU in some meta-sense, then v(ZU) > v(AU) if v is -log like.
# So, -∞_low would be "less negative" than -∞_high.
VALUATION_NEG_INF_ZU = -999.0  # Proxy for -infinity_low
VALUATION_NEG_INF_AU = -1000.0 # Proxy for -infinity_high (AU "more infinite" or "lower" in valuation)
LOG_BASE = 2.0

def v_valuation(val: AVCVal_H_V1, current_omega: int) -> float:
    if val is ZERO_UNIO_H_V1:
        return VALUATION_NEG_INF_ZU
    elif val is AREO_UNIO_H_V1:
        return VALUATION_NEG_INF_AU
    elif isinstance(val, int): # DFI
        if val <= 0: # Should not happen for valid DFI k >= 1
             raise ValueError(f"DFI value must be positive for log valuation: {val}")
        return -math.log(float(val), LOG_BASE)
    else: # Should be an unhandled Unio object if aspects are dynamically created
        raise TypeError(f"Unknown AVCA value type for v_valuation: {val!r}")

# Helper for addition with infinity proxies
def add_valuations(v1: float, v2: float) -> float:
    # Define (-inf) + x = -inf, (-inf) + (-inf) = -inf
    # Check against specific proxy values if needed, or use a general threshold
    neg_inf_threshold = -900.0 # Numbers below this are treated as -inf
    if v1 < neg_inf_threshold or v2 < neg_inf_threshold:
        # Return the "more infinite" one if distinguishing ZU/AU infinities matters for sum
        # For v(x*y) = v(x)+v(y), if one is -inf, sum is -inf.
        # The specific value of -inf might matter if comparing -999 vs -1000.
        # For now, let's just return a generic -inf proxy if any input is -inf.
        return min(VALUATION_NEG_INF_ZU, VALUATION_NEG_INF_AU) # Or a single -INF_PROXY
    return v1 + v2

# --- Test Runner for H-V1 ---
def test_H_V1_valuation_properties(omega_to_test: int):
    print(f"\n--- Testing H-V1: Non-Archimedean Valuation Properties for Omega={omega_to_test} ---")
    set_avca_omega_bc_H_V1(omega_to_test)

    s_omega: List[AVCVal_H_V1] = []
    if omega_to_test == 1:
        s_omega = [ZERO_UNIO_H_V1, AREO_UNIO_H_V1] 
    else:
        s_omega = [ZERO_UNIO_H_V1, AREO_UNIO_H_V1] + list(range(1, omega_to_test))
    
    print(f"Valuation map for Ω={omega_to_test}:")
    for elem in s_omega:
        print(f"  v({elem!r}) = {v_valuation(elem, omega_to_test):.3f}")

    # Test 1: v(x ⊕ y) >= min(v(x), v(y))
    print("\n  Testing ADDITION property: v(x ⊕ y) >= min(v(x), v(y))")
    add_prop_holds = True
    for x in s_omega:
        for y in s_omega:
            # Skip invalid DFI for Omega=1 if in s_omega construction
            if omega_to_test == 1 and (isinstance(x,int) or isinstance(y,int)): continue
            
            res_add = avc_add_v1_1_bc_H_V1(x, y)
            vx, vy, v_res_add = v_valuation(x, omega_to_test), v_valuation(y, omega_to_test), v_valuation(res_add, omega_to_test)
            min_vx_vy = min(vx, vy)

            # Using math.isclose for float comparison due to potential precision issues with log
            if not (v_res_add >= min_vx_vy or math.isclose(v_res_add, min_vx_vy)):
                print(f"    ADD COUNTEREXAMPLE: x={x!r}, y={y!r}")
                print(f"      v(x)={vx:.3f}, v(y)={vy:.3f}, min(v(x),v(y))={min_vx_vy:.3f}")
                print(f"      x ⊕ y = {res_add!r}, v(x ⊕ y)={v_res_add:.3f}")
                print(f"      Condition FAILED: {v_res_add:.3f} < {min_vx_vy:.3f}")
                add_prop_holds = False
                break
        if not add_prop_holds: break
    if add_prop_holds:
        print("    Addition property v(x ⊕ y) >= min(v(x), v(y)) HOLDS for all tested pairs.")

    # Test 2: v(x ⊗ y) = v(x) + v(y)
    print("\n  Testing MULTIPLICATION property: v(x ⊗ y) = v(x) + v(y)")
    mul_prop_holds = True
    for x in s_omega:
        for y in s_omega:
            if omega_to_test == 1 and (isinstance(x,int) or isinstance(y,int)): continue

            res_mul = avc_mul_v1_2_bc_H_V1(x, y)
            vx, vy, v_res_mul = v_valuation(x, omega_to_test), v_valuation(y, omega_to_test), v_valuation(res_mul, omega_to_test)
            sum_vx_vy = add_valuations(vx, vy) # Handles -infinity proxies

            if not math.isclose(v_res_mul, sum_vx_vy):
                print(f"    MUL COUNTEREXAMPLE: x={x!r}, y={y!r}")
                print(f"      v(x)={vx:.3f}, v(y)={vy:.3f}, v(x)+v(y)={sum_vx_vy:.3f}")
                print(f"      x ⊗ y = {res_mul!r}, v(x ⊗ y)={v_res_mul:.3f}")
                print(f"      Condition FAILED: {v_res_mul:.3f} != {sum_vx_vy:.3f}")
                mul_prop_holds = False
                break
        if not mul_prop_holds: break
    if mul_prop_holds:
        print("    Multiplication property v(x ⊗ y) = v(x) + v(y) HOLDS for all tested pairs.")

    return add_prop_holds, mul_prop_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_V1_NonArchimedean_Valuation_PoC: ======")
    
    # Test for Omega=3 (DFIs 1, 2) and Omega=4 (DFIs 1, 2, 3)
    omegas_to_test_H_V1 = [3, 4] 
    all_tests_passed_overall = True

    for omega_val in omegas_to_test_H_V1:
        set_avca_omega_bc_H_V1(omega_val) # Set global Omega for AVCA ops
        print(f"\n>>>> Testing for Omega = {omega_val} <<<<")
        add_holds, mul_holds = test_H_V1_valuation_properties(omega_val)
        
        print(f"\n  Summary for Omega = {omega_val}:")
        print(f"    v(x ⊕ y) >= min(v(x), v(y)): {'Holds' if add_holds else 'FAILED'}")
        print(f"    v(x ⊗ y) = v(x) + v(y):      {'Holds' if mul_holds else 'FAILED'}")
        if not (add_holds and mul_holds):
            all_tests_passed_overall = False
            
    print("\n--- Overall Summary of H-V1 PoC Test ---")
    if all_tests_passed_overall:
        print("Hypothesis H-V1 properties (ultrametric for ⊕, additive for ⊗ valuation)")
        print("APPEAR TO HOLD for all tested Omegas with the defined v(n) and infinity proxies.")
    else:
        print("Hypothesis H-V1 properties FAILED for at least one Omega or operation.")
        print("This suggests the simple v(n)=-log n with simple infinity proxies might not fully capture")
        print("the non-archimedean valuation, or the hypothesis needs refinement for AVCA.")

    print("\n====== H_V1_NonArchimedean_Valuation_PoC Script Finished ======")