# Script R2.1: Forced Unique Inverse - Associativity Check at Ω=2 (and Ω=3)
# Mathematical Obligation: R2 from math LLM's refined deliverables.
# "Explicit algebraic computation for Ω = 2. One enumeration script for confirmation."
# (Show that modifying AVCA addition to force a unique inverse for a+b=Ω
#  breaks associativity, specifically at Ω=2).

from typing import Union, List, Tuple, Any, Dict, Literal
import itertools

# --- Core AVCA Components (adapted from AVCA Core DraftV4 Appendix A) ---
_Omega: int = 0

class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio)
    def __hash__(self) -> int:
        return hash(type(self))
    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"

ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")
AVCVal = Union[int, Unio]

def set_avca_omega(omega_value: int):
    global _Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega = omega_value
    # print(f"\nGlobal Omega set to: {_Omega}")

def _check_val(x: AVCVal, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter ({current_omega}) must be an integer >= 1.")
    if isinstance(x, Unio):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value: {x!r}. Expected int or Unio. Omega={current_omega}")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI Value for Omega=1: {x}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value: {x}. For Omega={current_omega}, DFI must be [1, {current_omega - 1}].")

# Standard AVCA Add (⊕_v1.1 logic from Appendix A)
def classic_avc_add_v1_1(a: AVCVal, b: AVCVal, current_omega: int) -> AVCVal:
    _check_val(a, current_omega)
    _check_val(b, current_omega)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    # Both a and b are DFI integers
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < current_omega else AREO_UNIO

# --- Modified Addition Operation (for R2) ---
def avc_add_forced_unique_R2(a: AVCVal, b: AVCVal, current_omega: int) -> AVCVal:
    """
    Modified AVCA addition for R2.
    If a,b are DFI and a_val + b_val == current_omega, result is ZERO_UNIO.
    Else, behaves like classic_avc_add_v1_1.
    """
    _check_val(a, current_omega)
    _check_val(b, current_omega)

    if isinstance(a, int) and isinstance(b, int): # Both are DFI
        if a + b == current_omega:
            return ZERO_UNIO
        else:
            # Fallback to classic_avc_add_v1_1 for other DFI+DFI cases
            # (handles a+b < Omega and a+b > Omega correctly)
            if a + b < current_omega:
                return a + b
            else: # a + b > current_omega (since == Omega is handled above)
                return AREO_UNIO
    # Cases involving Unio follow classic identity rules
    elif isinstance(a, Unio):
        return b
    elif isinstance(b, Unio):
        return a
    return AREO_UNIO # Should not be reached if inputs are valid

# --- Helper to get carrier set S_Omega ---
def get_s_omega(current_omega: int) -> List[AVCVal]:
    if current_omega == 1:
        return [ZERO_UNIO] # Or AREO_UNIO, algebraically same
    else:
        # Use both ZERO_UNIO and AREO_UNIO for testing to ensure robustness,
        # even though they are algebraically equivalent.
        # For algebraic law testing, it's sufficient to use one Unio representative.
        # For this test, let's use ZERO_UNIO as the representative for Unio.
        s_omega: List[AVCVal] = [ZERO_UNIO]
        s_omega.extend(list(range(1, current_omega)))
        return s_omega

# --- Inverse Check Function ---
def check_additive_inverses_R2(op: callable, current_omega: int):
    print(f"\n--- Inverse Check for Ω={current_omega} using '{op.__name__}' ---")
    s_omega = get_s_omega(current_omega)
    dfi_elements = [e for e in s_omega if isinstance(e, int)]

    # Target identity for inverses is algebraic Unio
    # Both ZERO_UNIO and AREO_UNIO are algebraically Unio.
    # The modified rule specifically targets ZERO_UNIO for sum == Omega.

    for a in s_omega:
        inverses_for_a = []
        dfi_inverses_for_a_target_ZU = []
        dfi_inverses_for_a_target_AU = []
        
        a_val = a if isinstance(a, int) else None # For DFI checks

        for x in s_omega:
            result = op(a, x, current_omega)
            if result == ZERO_UNIO or result == AREO_UNIO: # Algebraically Unio
                inverses_for_a.append(x)
                if isinstance(a_val, int) and isinstance(x, int) and (a_val + x == current_omega) and result == ZERO_UNIO:
                    dfi_inverses_for_a_target_ZU.append(x)
                elif result == AREO_UNIO: # Other ways to get Unio (e.g. DFI sum > Omega)
                    if isinstance(a_val, int) and isinstance(x, int):
                         dfi_inverses_for_a_target_AU.append(x)


        num_algebraic_inverses = len(set(inverses_for_a)) # Count unique algebraic inverses

        print(f"  Element a = {a!r}:")
        print(f"    All algebraic inverses {{x | a ⊕' x ~ Unio}}: {sorted(list(set(str(i) for i in inverses_for_a)))}")
        print(f"    Number of unique algebraic inverses: {num_algebraic_inverses}")

        if isinstance(a, int): # a is DFI
            print(f"    DFI x such that a+x==Ω (result ZERO_UNIO): {sorted(list(set(dfi_inverses_for_a_target_ZU)))}")
            unique_dfi_inverse_for_sum_eq_omega = (len(set(dfi_inverses_for_a_target_ZU)) == 1 if dfi_inverses_for_a_target_ZU else False)
            if a_val and current_omega - a_val in dfi_elements and len(dfi_inverses_for_a_target_ZU) == 1 and dfi_inverses_for_a_target_ZU[0] == (current_omega - a_val):
                 print(f"      -> Unique DFI inverse x={current_omega-a_val} for a+x==Ω yielding ZERO_UNIO: Confirmed.")
            elif not dfi_inverses_for_a_target_ZU and (a_val >= current_omega or current_omega - a_val not in dfi_elements):
                 print(f"      -> No DFI x such that a+x==Ω yielding ZERO_UNIO (as expected if Ω-a is not DFI).")
            else:
                 print(f"      -> Unique DFI inverse for a+x==Ω yielding ZERO_UNIO: NOT confirmed as expected / Multiple or None found unexpectedly.")
            print(f"    DFI x such that a+x > Ω (result AREO_UNIO): {sorted(list(set(dfi_inverses_for_a_target_AU)))}")


# --- Associativity Test Function ---
def test_associativity_R2(op: callable, current_omega: int):
    print(f"\n--- Associativity Test for Ω={current_omega} using '{op.__name__}' ---")
    s_omega = get_s_omega(current_omega)
    associativity_holds = True
    counterexample = None

    if not s_omega:
        print("  Carrier set is empty, associativity trivially holds or is N/A.")
        return

    for sa_repr in s_omega:
        for sb_repr in s_omega:
            for sc_repr in s_omega:
                # Ensure we use fresh Unio objects if that's part of the test,
                # but for algebraic laws, ZERO_UNIO as representative is fine.
                sa = ZERO_UNIO if isinstance(sa_repr, Unio) else sa_repr
                sb = ZERO_UNIO if isinstance(sb_repr, Unio) else sb_repr
                sc = ZERO_UNIO if isinstance(sc_repr, Unio) else sc_repr

                try:
                    # LHS: (sa op sb) op sc
                    res_ab = op(sa, sb, current_omega)
                    lhs = op(res_ab, sc, current_omega)

                    # RHS: sa op (sb op sc)
                    res_bc = op(sb, sc, current_omega)
                    rhs = op(sa, res_bc, current_omega)

                    # Compare results algebraically (Unio('zero') == Unio('areo'))
                    if not (lhs == rhs or (isinstance(lhs, Unio) and isinstance(rhs, Unio))):
                        associativity_holds = False
                        counterexample = (sa_repr, sb_repr, sc_repr, lhs, rhs)
                        break
                except Exception as e:
                    associativity_holds = False
                    counterexample = (sa_repr, sb_repr, sc_repr, "Exception", str(e))
                    break
            if not associativity_holds:
                break
        if not associativity_holds:
            break

    if associativity_holds:
        print("  Result: Additive Associativity HOLDS.")
    else:
        print("  Result: Additive Associativity FAILS.")
        if counterexample:
            sa_orig, sb_orig, sc_orig, lhs_res, rhs_res = counterexample
            print(f"    Counterexample: a={sa_orig!r}, b={sb_orig!r}, c={sc_orig!r}")
            print(f"      (a⊕'b)⊕'c = {lhs_res!r}")
            print(f"      a⊕'(b⊕'c) = {rhs_res!r}")

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script R2.1: Forced Unique Inverse - Associativity Check ======")

    # Test for Ω = 2
    set_avca_omega(2)
    check_additive_inverses_R2(avc_add_forced_unique_R2, 2)
    test_associativity_R2(avc_add_forced_unique_R2, 2)

    # Test for Ω = 3
    set_avca_omega(3)
    check_additive_inverses_R2(avc_add_forced_unique_R2, 3)
    test_associativity_R2(avc_add_forced_unique_R2, 3)

    print("\n====== R2.1 Script Finished ======")