# Script R4.2: Additive Associativity Counterexample for avc_add_v1_1 using (1,1,Ω-1) for Ω≥3
# Mathematical Obligation: R4(ii) from math LLM's refined deliverables.
# "Constructive counter-example for all Ω ≥ 3 (e.g., using (1,1,Ω−1))."
# This script demonstrates this for specific Ω values.

from typing import Union, List, Tuple, Any, Literal
import itertools

# --- Core AVCA Components (adapted from Script R4.1 / AVCA Core DraftV4 Appendix A) ---
_Omega_R4_2: int = 0

class Unio_R4_2: # Renamed to avoid conflict if run in same session as R4.1
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_R4_2 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_R4_2) 
    def __hash__(self) -> int:
        return hash(type(self)) 
    def __repr__(self) -> str:
        return f"Unio_R4_2('{self.aspect}')"

ZERO_UNIO_R4_2 = Unio_R4_2("zero")
AREO_UNIO_R4_2 = Unio_R4_2("areo") 
AVCVal_R4_2 = Union[int, Unio_R4_2]

def set_avca_omega_r4_2(omega_value: int):
    global _Omega_R4_2
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_R4_2 = omega_value
    # print(f"\nGlobal Omega for R4.2 set to: {_Omega_R4_2}")

def _check_val_r4_2(x: AVCVal_R4_2, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter ({current_omega}) for {var_name} must be an integer >= 1.")
    if isinstance(x, Unio_R4_2):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Expected int or Unio_R4_2. Omega={current_omega}")
    if current_omega == 1: # DFI is empty
        if isinstance(x, int):
             raise ValueError(f"Invalid DFI Value for {var_name} for Omega=1: {x}. DFI is empty.")
    elif not (1 <= x < current_omega): # DFI is [1, current_omega-1]
        raise ValueError(f"Invalid DFI Value for {var_name}: {x}. For Omega={current_omega}, DFI must be in range [1, {current_omega - 1}].")

# Standard AVCA Add (⊕_v1.1 logic from AVCA Core DraftV4 Appendix A)
def avc_add_v1_1_r4_2(a: AVCVal_R4_2, b: AVCVal_R4_2, current_omega: int) -> AVCVal_R4_2:
    _check_val_r4_2(a, current_omega, "operand 'a'")
    _check_val_r4_2(b, current_omega, "operand 'b'")

    if isinstance(a, Unio_R4_2): return b
    if isinstance(b, Unio_R4_2): return a
    
    standard_sum: int = a + b # type: ignore
    
    if standard_sum < current_omega:
        return standard_sum
    else: # standard_sum >= current_omega (DFI additive overflow)
        return AREO_UNIO_R4_2 # v1.1 refinement: overflow yields AREO_UNIO

# --- Associativity Test Function for Specific Triple ---
def test_associativity_failure_triple(current_omega: int):
    set_avca_omega_r4_2(current_omega)
    op_name = "avc_add_v1_1_r4_2"
    op = avc_add_v1_1_r4_2

    print(f"\n--- Additive Associativity Test for Ω={current_omega} using '{op_name}' ---")
    
    if current_omega < 3:
        print(f"  Counterexample (1,1,Ω-1) is not well-defined or DFI elements not distinct enough for Ω={current_omega}.")
        print(f"  (Standard AVCA ⊕_v1.1 is associative for Ω≤2, as confirmed by R4.1).")
        return

    sa_val = 1
    sb_val = 1
    sc_val = current_omega - 1 # This is Fp(Ω-1)

    # Ensure c is a valid DFI and distinct from a and b for typical counterexample structure
    if not (1 <= sc_val < current_omega):
        print(f"  Error: c = Ω-1 = {sc_val} is not a valid DFI for Ω={current_omega}. This should not happen for Ω>=2.")
        return

    print(f"  Testing triplet: a=Fp({sa_val}), b=Fp({sb_val}), c=Fp({sc_val})")

    # LHS: (sa_val op sb_val) op sc_val
    print("\n  Calculating LHS = (a ⊕ b) ⊕ c:")
    res_ab = op(sa_val, sb_val, current_omega)
    # Use repr for Unio objects to show their aspect, str for int
    res_ab_str = repr(res_ab) if isinstance(res_ab, Unio_R4_2) else str(res_ab)
    sa_str = str(sa_val)
    sb_str = str(sb_val)
    sc_str = str(sc_val)
    print(f"    Step 1: {sa_str} ⊕ {sb_str} = {res_ab_str}")
    
    lhs = op(res_ab, sc_val, current_omega)
    lhs_str = repr(lhs) if isinstance(lhs, Unio_R4_2) else str(lhs)
    print(f"    Step 2: ({res_ab_str}) ⊕ {sc_str} = {lhs_str}")


    # RHS: sa_val op (sb_val op sc_val)
    print("\n  Calculating RHS = a ⊕ (b ⊕ c):")
    res_bc = op(sb_val, sc_val, current_omega)
    res_bc_str = repr(res_bc) if isinstance(res_bc, Unio_R4_2) else str(res_bc)
    print(f"    Step 1: {sb_str} ⊕ {sc_str} = {res_bc_str}")
    
    rhs = op(sa_val, res_bc, current_omega)
    rhs_str = repr(rhs) if isinstance(rhs, Unio_R4_2) else str(rhs)
    print(f"    Step 2: {sa_str} ⊕ ({res_bc_str}) = {rhs_str}")

    # Comparison
    associativity_holds = (lhs == rhs) # Relies on Unio_R4_2.__eq__

    print("\n  Result:")
    if associativity_holds:
        print(f"    Additive Associativity HOLDS for this triple at Ω={current_omega}. (Unexpected for Ω≥3 and this triple)")
    else:
        print(f"    Additive Associativity FAILS for this triple at Ω={current_omega}. (Expected)")
        print(f"      LHS = {lhs_str}")
        print(f"      RHS = {rhs_str}")

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script R4.2: Additive Associativity Counterexample for avc_add_v1_1 using (1,1,Ω-1) for Ω≥3 ======")

    # Test for Ω = 3, 4, 5 (as per math LLM's suggestion for sanity check range)
    test_associativity_failure_triple(current_omega=3)
    test_associativity_failure_triple(current_omega=4)
    test_associativity_failure_triple(current_omega=5)

    print("\n====== R4.2 Script Finished ======")