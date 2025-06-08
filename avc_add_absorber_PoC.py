# avc_add_absorber_PoC.py
# Python Proof-of-Concept for an AVCA-like addition where Unio is a universal absorber.
# This directly tests ideas related to Plan 1, Track 5.C and the "Impossibility Theorem."

from typing import Literal, Union, Any

# --- Unio Class Definition for this PoC ---
# For this PoC, aspect distinction in the absorbing Unio might be less critical,
# but we'll keep it for consistency with other Unio objects.
# Let's define that absorption and DFI overflow to Unio yields ZERO_UNIO_POC.
_Omega_POC: int = 0

class Unio_POC:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_POC aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool: # Algebraic equivalence
        return isinstance(other, Unio_POC)
    def __hash__(self) -> int: # For set operations if needed
        return hash("Unio_POC_Algebraic_Singleton")
    def __repr__(self) -> str:
        return f"Unio_POC('{self.aspect}')"

ZERO_UNIO_POC = Unio_POC("zero") # Will be used as the absorbing Unio state
AREO_UNIO_POC = Unio_POC("areo") # For BC reference, DFI overflow target
AVCVal_POC = Union[int, Unio_POC]

def set_avca_omega_poc(omega_value: int, verbose: bool = True):
    global _Omega_POC
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_POC parameter must be an integer >= 1.")
    _Omega_POC = omega_value
    if verbose:
        print(f"\nPoC Omega set to: {_Omega_POC}")

def _check_val_poc(x: AVCVal_POC, current_omega: int, op_name: str = "op", arg_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega_POC for {op_name} must be >= 1. Got: {current_omega!r}")
    if isinstance(x, Unio_POC): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid {arg_name} for {op_name}: {x!r} (type {type(x)}) for Ω={current_omega}.")
    if current_omega == 1 and isinstance(x, int):
        raise ValueError(f"Invalid DFI {arg_name} for {op_name} when Omega_POC=1: {x!r}. DFI is empty.")
    if current_omega > 1 and not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI {arg_name} for {op_name}: {x!r}. For Omega_POC={current_omega}, DFI in [1, {current_omega - 1}].")

# --- Alternative Addition: Unio as Universal Absorber ---
def avc_add_absorber_poc(a: AVCVal_POC, b: AVCVal_POC) -> AVCVal_POC:
    """
    AVCA-like addition where Unio (represented by ZERO_UNIO_POC) is a universal absorber.
    DFI overflows also go to this absorbing Unio.
    """
    global _Omega_POC
    if _Omega_POC == 0: raise ValueError("Global Omega_POC not set.")
    _check_val_poc(a, _Omega_POC, "add_absorb", "a")
    _check_val_poc(b, _Omega_POC, "add_absorb", "b")

    if isinstance(a, Unio_POC) or isinstance(b, Unio_POC):
        return ZERO_UNIO_POC # Unio absorbs everything, becomes ZERO_UNIO_POC

    # Both a and b are DFI integers
    standard_sum = a + b # type: ignore
    if standard_sum < _Omega_POC:
        return standard_sum  # Result is DFI
    else:
        return ZERO_UNIO_POC # DFI additive overflow yields absorbing Unio

# --- Reference "Best Combination" Addition (⊕_BC / avc_add_v1_1) ---
def avc_add_BC_reference_poc(a: AVCVal_POC, b: AVCVal_POC) -> AVCVal_POC:
    """Standard AVCA Best Combo addition: Unio is identity, DFI overflow to AREO_UNIO_POC."""
    global _Omega_POC
    if _Omega_POC == 0: raise ValueError("Global Omega_POC not set.")
    _check_val_poc(a, _Omega_POC, "add_BC_ref", "a")
    _check_val_poc(b, _Omega_POC, "add_BC_ref", "b")

    # For BC reference, any Unio aspect object acts as identity
    if isinstance(a, Unio_POC): return b 
    if isinstance(b, Unio_POC): return a
    
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < _Omega_POC else AREO_UNIO_POC

# --- Test Scenarios ---
def run_poc_tests(omega_to_test: int):
    set_avca_omega_poc(omega_to_test)
    
    dfi1, dfi_mid, dfi_large = 0, 0, 0
    if omega_to_test > 1:
        dfi1 = 1
    if omega_to_test > 2:
        dfi_mid = 2 
    if omega_to_test > 3: # Needs Omega=4 for mid and large to cause overflow distinct from mid+1
        dfi_mid = 2
        dfi_large = omega_to_test - 1 # e.g., Fp(3) for Omega=4
    elif omega_to_test == 3: # For Omega=3, DFI={1,2}
        dfi_mid = 1 # To make dfi_mid + dfi_mid not overflow if possible
        dfi_large = 2 # dfi_large + dfi_large will overflow

    print(f"\n--- Testing with Omega = {omega_to_test} ---")
    print(f"Elements: ZU={ZERO_UNIO_POC!r}, AU={AREO_UNIO_POC!r}, Fp1={dfi1 if dfi1 else 'N/A'}")

    print("\nPart 1: Basic Absorption with avc_add_absorber_poc (⊕_absorb)")
    if dfi1:
        print(f"  {ZERO_UNIO_POC!r} ⊕_absorb Fp({dfi1}) = {avc_add_absorber_poc(ZERO_UNIO_POC, dfi1)!r} \t(Expected: {ZERO_UNIO_POC!r})")
        print(f"  Fp({dfi1}) ⊕_absorb {ZERO_UNIO_POC!r} = {avc_add_absorber_poc(dfi1, ZERO_UNIO_POC)!r} \t(Expected: {ZERO_UNIO_POC!r})")
    print(f"  {ZERO_UNIO_POC!r} ⊕_absorb {AREO_UNIO_POC!r} = {avc_add_absorber_poc(ZERO_UNIO_POC, AREO_UNIO_POC)!r} \t(Expected: {ZERO_UNIO_POC!r})")

    print("\nPart 2: DFI Interactions with avc_add_absorber_poc (⊕_absorb)")
    if omega_to_test >= 3: # Requires at least DFI {1,2}
        dfi_a, dfi_b = 1, 1 
        print(f"  Fp({dfi_a}) ⊕_absorb Fp({dfi_b}) = {avc_add_absorber_poc(dfi_a, dfi_b)!r} \t(Sum={dfi_a+dfi_b}, Expected: {dfi_a+dfi_b if dfi_a+dfi_b < omega_to_test else ZERO_UNIO_POC!r})")
        dfi_a, dfi_b = 1, (omega_to_test - 1) # e.g., 1, 2 for Omega=3 (sum=3 -> overflow)
        print(f"  Fp({dfi_a}) ⊕_absorb Fp({dfi_b}) = {avc_add_absorber_poc(dfi_a, dfi_b)!r} \t(Sum={dfi_a+dfi_b}, Expected: {ZERO_UNIO_POC!r})")
    elif omega_to_test == 2: # DFI={1}
        dfi_a, dfi_b = 1, 1
        print(f"  Fp({dfi_a}) ⊕_absorb Fp({dfi_b}) = {avc_add_absorber_poc(dfi_a, dfi_b)!r} \t(Sum={dfi_a+dfi_b}, Expected: {ZERO_UNIO_POC!r})")


    print("\nPart 3: Cyclical Emergence Test")
    dfi_k_small = dfi1
    if not dfi_k_small and omega_to_test > 1: dfi_k_small = 1 # ensure it's at least 1 if DFI exists
    
    if omega_to_test >= 3: # Need DFI elements that can reliably cause overflow
        # Define DFI_A, DFI_B such that DFI_A + DFI_B >= Omega
        # E.g., for Omega=3, DFI_A=Fp(2), DFI_B=Fp(2) -> sum=4 -> overflow
        # E.g., for Omega=4, DFI_A=Fp(2), DFI_B=Fp(2) -> sum=4 -> overflow
        dfi_val_for_overflow1 = omega_to_test - 1 if omega_to_test > 1 else (ZERO_UNIO_POC if omega_to_test==1 else 1) # Fp(Omega-1) or 1
        dfi_val_for_overflow2 = 1 if omega_to_test > 1 else (ZERO_UNIO_POC if omega_to_test==1 else 1)
        if isinstance(dfi_val_for_overflow1, Unio_POC) or isinstance(dfi_val_for_overflow2, Unio_POC):
             print("  Skipping emergence test for Omega=1 as DFI elements for overflow are not available.")
        else:
            print(f"  Using DFI_k_small = Fp({dfi_k_small}), DFI_overflow1 = Fp({dfi_val_for_overflow1}), DFI_overflow2 = Fp({dfi_val_for_overflow2})")

            # Standard AVCA (Best Combination)
            u_from_bc_overflow = avc_add_BC_reference_poc(dfi_val_for_overflow1, dfi_val_for_overflow2)
            emergence_bc = avc_add_BC_reference_poc(u_from_bc_overflow, dfi_k_small)
            print(f"  BEST COMBO ADD (⊕_BC):")
            print(f"    Overflow: Fp({dfi_val_for_overflow1}) ⊕_BC Fp({dfi_val_for_overflow2}) = {u_from_bc_overflow!r} \t(Expected: {AREO_UNIO_POC!r})")
            print(f"    Emergence: {u_from_bc_overflow!r} ⊕_BC Fp({dfi_k_small}) = {emergence_bc!r} \t(Expected: Fp({dfi_k_small}))")

            # Absorber AVCA
            u_from_absorb_overflow = avc_add_absorber_poc(dfi_val_for_overflow1, dfi_val_for_overflow2)
            emergence_absorb = avc_add_absorber_poc(u_from_absorb_overflow, dfi_k_small)
            print(f"  ABSORBER ADD (⊕_absorb):")
            print(f"    Overflow: Fp({dfi_val_for_overflow1}) ⊕_absorb Fp({dfi_val_for_overflow2}) = {u_from_absorb_overflow!r} \t(Expected: {ZERO_UNIO_POC!r})")
            print(f"    Emergence: {u_from_absorb_overflow!r} ⊕_absorb Fp({dfi_k_small}) = {emergence_absorb!r} \t(STUCK at Unio - Expected: {ZERO_UNIO_POC!r})")

            if emergence_bc == dfi_k_small and emergence_absorb is ZERO_UNIO_POC:
                print("  ==> Cyclical emergence SUCCESSFUL for Best Combo, but FAILED (stuck at Unio) for Absorber Add.")
            else:
                print("  ==> Cyclical emergence test yielded unexpected results.")
    elif omega_to_test == 2 : # DFI = {1}, dfi_k_small = 1
        dfi_val_for_overflow1 = 1
        dfi_val_for_overflow2 = 1
        print(f"  Using DFI_k_small = Fp({dfi_k_small}), DFI_overflow1 = Fp({dfi_val_for_overflow1}), DFI_overflow2 = Fp({dfi_val_for_overflow2})")
        u_from_bc_overflow = avc_add_BC_reference_poc(dfi_val_for_overflow1, dfi_val_for_overflow2) # 1+1=0 (AU)
        emergence_bc = avc_add_BC_reference_poc(u_from_bc_overflow, dfi_k_small) # AU+1 = 1
        print(f"  BEST COMBO ADD (⊕_BC):")
        print(f"    Overflow: Fp({dfi_val_for_overflow1}) ⊕_BC Fp({dfi_val_for_overflow2}) = {u_from_bc_overflow!r} \t(Expected: {AREO_UNIO_POC!r})")
        print(f"    Emergence: {u_from_bc_overflow!r} ⊕_BC Fp({dfi_k_small}) = {emergence_bc!r} \t(Expected: Fp({dfi_k_small}))")
        u_from_absorb_overflow = avc_add_absorber_poc(dfi_val_for_overflow1, dfi_val_for_overflow2) # 1+1=0 (ZU)
        emergence_absorb = avc_add_absorber_poc(u_from_absorb_overflow, dfi_k_small) # ZU+1 = ZU
        print(f"  ABSORBER ADD (⊕_absorb):")
        print(f"    Overflow: Fp({dfi_val_for_overflow1}) ⊕_absorb Fp({dfi_val_for_overflow2}) = {u_from_absorb_overflow!r} \t(Expected: {ZERO_UNIO_POC!r})")
        print(f"    Emergence: {u_from_absorb_overflow!r} ⊕_absorb Fp({dfi_k_small}) = {emergence_absorb!r} \t(STUCK at Unio - Expected: {ZERO_UNIO_POC!r})")
        if emergence_bc == dfi_k_small and emergence_absorb is ZERO_UNIO_POC:
            print("  ==> Cyclical emergence SUCCESSFUL for Best Combo, but FAILED (stuck at Unio) for Absorber Add.")

    else: # Omega = 1
        print("  Skipping emergence test for Omega=1 as DFI for operand is not available.")


# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script avc_add_absorber_PoC.py: Demonstrating Unio as Additive Absorber ======")
    
    omegas_to_test_poc = [3, 4, 2, 1] 
    for omega_val_poc in omegas_to_test_poc:
        run_poc_tests(omega_val_poc)
        print("-" * 70)

    print("\n====== avc_add_absorber_PoC.py Script Finished ======")