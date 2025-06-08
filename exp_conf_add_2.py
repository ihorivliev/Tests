# Script R4.1: Additive Associativity of avc_add_v1_1 for Ω=1, 2 (Exhaustive Check)
# Mathematical Obligation: R4(i) from math LLM's refined deliverables.
# "Direct proof for Ω≤2 (small case enumeration)."
# This script performs the computational enumeration for Ω=1 and Ω=2.

from typing import Union, List, Tuple, Any, Literal
import itertools

# --- Core AVCA Components (adapted from AVCA Core DraftV4 Appendix A) ---
# Renaming to avoid potential conflicts if multiple R-scripts are combined later.
_Omega_R4: int = 0

class Unio_R4:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"): # Sanity check
            raise ValueError("Unio_R4 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_R4) # Algebraic equivalence
    def __hash__(self) -> int:
        return hash(type(self)) # All Unio objects hash same
    def __repr__(self) -> str:
        return f"Unio_R4('{self.aspect}')"

ZERO_UNIO_R4 = Unio_R4("zero")
AREO_UNIO_R4 = Unio_R4("areo") # Standard AVCA overflow target for classic_avc_add
AVCVal_R4 = Union[int, Unio_R4]

def set_avca_omega_r4(omega_value: int):
    global _Omega_R4
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_R4 = omega_value
    # print(f"\nGlobal Omega for R4.1 set to: {_Omega_R4}")

def _check_val_r4(x: AVCVal_R4, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter ({current_omega}) for {var_name} must be an integer >= 1.")
    if isinstance(x, Unio_R4):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Expected int or Unio_R4. Omega={current_omega}")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI Value for {var_name} for Omega=1: {x}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value for {var_name}: {x}. For Omega={current_omega}, DFI must be in range [1, {current_omega - 1}].")

# Standard AVCA Add (⊕_v1.1 logic from AVCA Core DraftV4 Appendix A)
def avc_add_v1_1_r4(a: AVCVal_R4, b: AVCVal_R4, current_omega: int) -> AVCVal_R4:
    _check_val_r4(a, current_omega, "operand 'a'")
    _check_val_r4(b, current_omega, "operand 'b'")

    if isinstance(a, Unio_R4): return b
    if isinstance(b, Unio_R4): return a
    
    standard_sum: int = a + b # type: ignore
    
    if standard_sum < current_omega:
        return standard_sum
    else: # standard_sum >= current_omega (DFI additive overflow)
        return AREO_UNIO_R4 # v1.1 refinement: overflow yields AREO_UNIO

# --- Helper to get carrier set S_Omega ---
def get_s_omega_r4(current_omega: int) -> List[AVCVal_R4]:
    # For algebraic law testing, it's sufficient to use one Unio representative.
    # ZERO_UNIO_R4 is used here. AREO_UNIO_R4 would be algebraically equivalent.
    if current_omega == 1:
        return [ZERO_UNIO_R4] 
    else:
        s_omega: List[AVCVal_R4] = [ZERO_UNIO_R4]
        s_omega.extend(list(range(1, current_omega)))
        return s_omega

# --- Associativity Test Function ---
def check_associativity_exhaustive(current_omega: int):
    set_avca_omega_r4(current_omega)
    op_name = "avc_add_v1_1_r4"
    op = avc_add_v1_1_r4

    print(f"\n--- Exhaustive Associativity Test for Ω={current_omega} using '{op_name}' ---")
    s_omega = get_s_omega_r4(current_omega)
    associativity_holds = True
    counterexample: Any = None # Can store (sa, sb, sc, lhs, rhs)

    if not s_omega: # Should not happen if Omega >= 1
        print("  Carrier set is empty. Test N/A.")
        return

    num_elements = len(s_omega)
    num_triplets = num_elements ** 3
    print(f"  Carrier S_{current_omega} = {[str(e) for e in s_omega]}")
    print(f"  Number of elements = {num_elements}. Number of triplets (a,b,c) to check = {num_triplets}.")

    checked_count = 0
    for sa in s_omega:
        for sb in s_omega:
            for sc in s_omega:
                checked_count += 1
                # Defensive copy or consistent Unio object if aspects were involved,
                # but for algebraic Unio, using the single ZERO_UNIO_R4 representative is fine.
                
                try:
                    # LHS: (sa op sb) op sc
                    res_ab = op(sa, sb, current_omega)
                    lhs = op(res_ab, sc, current_omega)

                    # RHS: sa op (sb op sc)
                    res_bc = op(sb, sc, current_omega)
                    rhs = op(sa, res_bc, current_omega)

                    # Algebraic comparison: instances of Unio_R4 are considered equal.
                    # Integers are compared by value.
                    # An int is not equal to a Unio_R4 object.
                    results_equal = (lhs == rhs) 

                    if not results_equal:
                        associativity_holds = False
                        counterexample = (sa, sb, sc, lhs, rhs)
                        break
                except Exception as e:
                    associativity_holds = False
                    counterexample = (sa, sb, sc, "Exception", str(e))
                    break
            if not associativity_holds:
                break
        if not associativity_holds:
            break
    
    print(f"  Checked {checked_count} triplets.")
    if associativity_holds:
        print(f"  Result: Additive Associativity for ⊕_v1.1 HOLDS for Ω={current_omega}.")
    else:
        print(f"  Result: Additive Associativity for ⊕_v1.1 FAILS for Ω={current_omega}.")
        if counterexample:
            sa_orig, sb_orig, sc_orig, lhs_res, rhs_res = counterexample
            # Use repr for Unio objects to show their aspect
            sa_str = repr(sa_orig) if isinstance(sa_orig, Unio_R4) else str(sa_orig)
            sb_str = repr(sb_orig) if isinstance(sb_orig, Unio_R4) else str(sb_orig)
            sc_str = repr(sc_orig) if isinstance(sc_orig, Unio_R4) else str(sc_orig)
            lhs_str = repr(lhs_res) if isinstance(lhs_res, Unio_R4) else str(lhs_res)
            rhs_str = repr(rhs_res) if isinstance(rhs_res, Unio_R4) else str(rhs_res)
            
            print(f"    Counterexample: a={sa_str}, b={sb_str}, c={sc_str}")
            print(f"      (a⊕b)⊕c = {lhs_str}")
            print(f"      a⊕(b⊕c) = {rhs_str}")

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script R4.1: Additive Associativity of avc_add_v1_1 for Ω=1, 2 (Exhaustive Check) ======")

    # Test for Ω = 1
    check_associativity_exhaustive(current_omega=1)

    # Test for Ω = 2
    check_associativity_exhaustive(current_omega=2)
    
    # Optional: Sanity check for Ω = 3 (expected to fail, as per R4(ii))
    # print("\n--- Optional Sanity Check for Ω = 3 (Associativity Expected to Fail) ---")
    # check_associativity_exhaustive(current_omega=3)

    print("\n====== R4.1 Script Finished ======")