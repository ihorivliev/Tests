# test_algebraic_laws_part1.py
# Purpose: To exhaustively test commutativity of add/mul, and associativity
# (general and power) of add for AVCA Core v1.2b operations for small Omega values.

import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- Unio Class Definition (Copied directly from Appendix A of AVCA Core DraftV3) ---
class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio aspect must be 'zero' or 'areo'.")
        self.aspect = aspect
    def __eq__(self, other: object) -> bool: # Checks for algebraic equivalence
        return isinstance(other, Unio)
    def __hash__(self) -> int:
        return hash(type(self))
    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"

# --- Canonical Unio Instances ---
ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")

# --- Type Alias for AVCA Values ---
AVCVal = Union[int, Unio]

# --- Global Omega Parameter ---
Omega: int = 0

# --- Domain Enforcement and Input Validation ---
def _check_val(x: AVCVal, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter must be an integer >= 1. Got: {current_omega}")
    if isinstance(x, Unio): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")
    if current_omega == 1:
        if isinstance(x, int):
            raise ValueError(f"Invalid DFI Value for Omega=1: {x}. DFI is empty when Omega=1.")
    elif not (1 <= x < current_omega):
            raise ValueError(f"Invalid DFI Value: {x}. For Omega={current_omega}, DFI integers must be in range [1, {current_omega - 1}].")

# --- AVCA Operations (v1.2b logic from Appendix A of AVCA Core DraftV3) ---
def avc_add(a: AVCVal, b: AVCVal) -> AVCVal: # ⊕_v1.1 logic
    global Omega
    if Omega == 0: raise ValueError("Global Omega not set.")
    _check_val(a, Omega); _check_val(b, Omega)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < Omega else AREO_UNIO

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal: # ⊗_v1.2 logic
    global Omega
    if Omega == 0: raise ValueError("Global Omega not set.")
    _check_val(a, Omega); _check_val(b, Omega)
    a_is_unio = isinstance(a, Unio); b_is_unio = isinstance(b, Unio)
    if a_is_unio or b_is_unio:
        is_any_areo = (a_is_unio and a.aspect == "areo") or \
                      (b_is_unio and b.aspect == "areo") # type: ignore
        return AREO_UNIO if is_any_areo else ZERO_UNIO
    else: # Both DFI
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < Omega else AREO_UNIO

# --- Helper for setting Omega for testing ---
def set_avca_omega(omega_value: int):
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega must be an integer >= 1.")
    Omega = omega_value

# --- Helper to compare AVCA values (respecting Unio's algebraic equivalence) ---
def avca_equals(val1: AVCVal, val2: AVCVal) -> bool:
    if isinstance(val1, Unio) and isinstance(val2, Unio):
        return True # All Unio objects are algebraically equal
    return val1 == val2 # For DFI or DFI vs Unio (which would be False)

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Algebraic Law Tests (Commutativity, Associativity - AVCA Core v1.2b) ---\n")
    
    omegas_for_commutativity = [1, 2, 3, 4]
    omegas_for_associativity = [1, 2, 3] # N^3 complexity, keep smaller

    overall_results = {}

    # Test Commutativity of avc_add
    print("## Testing Commutativity of avc_add (a + b == b + a) ##")
    for omega_val in omegas_for_commutativity:
        set_avca_omega(omega_val)
        s_omega: List[AVCVal] = [ZERO_UNIO, AREO_UNIO] + list(range(1, omega_val)) if omega_val > 1 else [ZERO_UNIO, AREO_UNIO]
        
        law_holds = True
        counterexample = None
        checked_pairs = 0
        for a, b in itertools.product(s_omega, s_omega):
            checked_pairs += 1
            try:
                res1 = avc_add(a, b)
                res2 = avc_add(b, a)
                if not avca_equals(res1, res2):
                    law_holds = False
                    counterexample = (a,b,res1,res2)
                    break
            except Exception as e:
                law_holds = False
                counterexample = (a,b, "Exception", str(e))
                break
        status = "Holds" if law_holds else f"FAILS (Counterexample: a={counterexample[0]!r}, b={counterexample[1]!r} -> ab={counterexample[2]!r}, ba={counterexample[3]!r})"
        overall_results[f"Commutativity_Add_Omega_{omega_val}"] = status
        print(f"  Omega={omega_val}: {status} (Checked {checked_pairs} pairs)")
    print("-" * 70)

    # Test Commutativity of avc_mul
    print("\n## Testing Commutativity of avc_mul (a * b == b * a) ##")
    for omega_val in omegas_for_commutativity:
        set_avca_omega(omega_val)
        s_omega: List[AVCVal] = [ZERO_UNIO, AREO_UNIO] + list(range(1, omega_val)) if omega_val > 1 else [ZERO_UNIO, AREO_UNIO]
        
        law_holds = True
        counterexample = None
        checked_pairs = 0
        for a, b in itertools.product(s_omega, s_omega):
            checked_pairs += 1
            try:
                res1 = avc_mul(a, b)
                res2 = avc_mul(b, a)
                if not avca_equals(res1, res2):
                    law_holds = False
                    counterexample = (a,b,res1,res2)
                    break
            except Exception as e:
                law_holds = False
                counterexample = (a,b, "Exception", str(e))
                break
        status = "Holds" if law_holds else f"FAILS (Counterexample: a={counterexample[0]!r}, b={counterexample[1]!r} -> ab={counterexample[2]!r}, ba={counterexample[3]!r})"
        overall_results[f"Commutativity_Mul_Omega_{omega_val}"] = status
        print(f"  Omega={omega_val}: {status} (Checked {checked_pairs} pairs)")
    print("-" * 70)

    # Test Associativity of avc_add
    print("\n## Testing Associativity of avc_add ((a + b) + c == a + (b + c)) ##")
    for omega_val in omegas_for_associativity:
        set_avca_omega(omega_val)
        s_omega: List[AVCVal] = [ZERO_UNIO, AREO_UNIO] + list(range(1, omega_val)) if omega_val > 1 else [ZERO_UNIO, AREO_UNIO]

        law_holds = True
        counterexample = None
        checked_triplets = 0
        for a, b, c in itertools.product(s_omega, s_omega, s_omega):
            checked_triplets += 1
            try:
                lhs = avc_add(avc_add(a, b), c)
                rhs = avc_add(a, avc_add(b, c))
                if not avca_equals(lhs, rhs):
                    law_holds = False
                    counterexample = (a,b,c,lhs,rhs)
                    break
            except Exception as e:
                law_holds = False
                counterexample = (a,b,c, "Exception", str(e))
                break
            if not law_holds: break # Inner loop break
        status = "Holds" if law_holds else f"FAILS (Counterexample: a={counterexample[0]!r}, b={counterexample[1]!r}, c={counterexample[2]!r} -> (ab)c={counterexample[3]!r}, a(bc)={counterexample[4]!r})"
        overall_results[f"Associativity_Add_Omega_{omega_val}"] = status
        print(f"  Omega={omega_val}: {status} (Checked up to {checked_triplets} triplets)")
    print("-" * 70)

    # Test Power-Associativity of avc_add
    print("\n## Testing Power-Associativity of avc_add ((a + a) + a == a + (a + a)) ##")
    for omega_val in omegas_for_associativity:
        set_avca_omega(omega_val)
        s_omega: List[AVCVal] = [ZERO_UNIO, AREO_UNIO] + list(range(1, omega_val)) if omega_val > 1 else [ZERO_UNIO, AREO_UNIO]

        law_holds = True
        counterexample = None
        checked_elements = 0
        for a in s_omega:
            checked_elements +=1
            try:
                # (a+a)+a
                aplus_a = avc_add(a,a)
                lhs = avc_add(aplus_a, a)
                # a+(a+a)
                # aplus_a is already computed
                rhs = avc_add(a, aplus_a)
                
                if not avca_equals(lhs, rhs):
                    law_holds = False
                    counterexample = (a,lhs,rhs)
                    break
            except Exception as e:
                law_holds = False
                counterexample = (a, "Exception", str(e))
                break
        status = "Holds" if law_holds else f"FAILS (Counterexample: a={counterexample[0]!r} -> (aa)a={counterexample[1]!r}, a(aa)={counterexample[2]!r})"
        overall_results[f"PowerAssociativity_Add_Omega_{omega_val}"] = status
        print(f"  Omega={omega_val}: {status} (Checked {checked_elements} elements)")
    print("-" * 70)

    print("\n--- Algebraic Law Tests (Part 1) Completed ---")
    # print("\nOverall Results Summary:")
    # for k, v in overall_results.items():
    # print(f"  {k}: {v}")

if __name__ == "__main__":
    run_all_tests()