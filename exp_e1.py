# Script E.1: Elaborate Boundary Tweak for Addition - Inverse & Associativity Check
# Red-Team Audit: Claim 7 (related to R2) "Boundary-tweak fails for Ω ≥ 3"
# Falsification Strategy: allow two special sums (Ω and Ω−1) to map to U;
#                        brute-check Ω = 3,4 for associativity and unique inverses.

from typing import Union, List, Tuple, Any, Literal, Set, FrozenSet, Callable
import itertools

# --- Core AVCA Components (adapted from previous scripts) ---
_Omega_sE1: int = 0

class Unio_sE1:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_sE1 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_sE1) 
    def __hash__(self) -> int:
        return hash(f"Unio_sE1_Algebraic_Singleton") 
    def __repr__(self) -> str:
        return f"Unio_sE1('{self.aspect}')"
    def __lt__(self, other): 
        if isinstance(other, Unio_sE1): return False
        if isinstance(other, int): return True 
        return NotImplemented

ZERO_UNIO_sE1 = Unio_sE1("zero") # Target for specific boundary sums Ω and Ω-1
AREO_UNIO_sE1 = Unio_sE1("areo") # Target for sums > Ω
AVCVal_sE1 = Union[int, Unio_sE1]

def set_avca_omega_sE1(omega_value: int):
    global _Omega_sE1
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_sE1 = omega_value
    # print(f"\nGlobal Omega for sE1 set to: {_Omega_sE1}")

def _check_val_sE1(x: AVCVal_sE1, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega ({current_omega}) for {var_name} must be >= 1.")
    if isinstance(x, Unio_sE1): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Omega={current_omega}")
    if current_omega == 1 and isinstance(x, int): # DFI is empty if omega=1
        raise ValueError(f"Invalid DFI {x} for {var_name} for Omega=1. DFI empty.")
    if current_omega > 1 and not (1 <= x < current_omega): # DFI is [1, current_omega-1]
        raise ValueError(f"Invalid DFI {x} for {var_name}. Omega={current_omega}, DFI [1,{current_omega-1}]")

# --- Modified Addition Operation (for E.1) ---
def avc_add_boundary_tweak_sE1(a: AVCVal_sE1, b: AVCVal_sE1, current_omega: int) -> AVCVal_sE1:
    """
    Modified AVCA addition for E.1.
    If a,b are DFI:
      - if a+b == current_omega OR a+b == current_omega-1, result is ZERO_UNIO_sE1.
      - else if a+b < current_omega-1, result is DFI sum.
      - else (a+b > current_omega), result is AREO_UNIO_sE1.
    Unio inputs act as identity.
    """
    _check_val_sE1(a, current_omega, "add_a")
    _check_val_sE1(b, current_omega, "add_b")

    if isinstance(a, Unio_sE1): return b
    if isinstance(b, Unio_sE1): return a
    
    # Both a and b are DFI integers
    s: int = a + b # type: ignore
    
    if s == current_omega or s == (current_omega - 1):
        return ZERO_UNIO_sE1
    elif s < (current_omega - 1): # Note: if current_omega=1, this branch is complex.
                                 # However, DFI is empty for omega=1, so a,b cannot be DFI.
                                 # if current_omega=2, DFI={1}. 1+1=2. current_omega-1 = 1.
                                 # s=2. s==current_omega is true. yields ZERO_UNIO_sE1.
        if s < 1 and current_omega > 1 : # Should not happen if a,b >=1
             # This case handles sums that might fall below DFI, e.g. if we allowed negative DFI
             # For positive DFI a,b >= 1, s will be >= 2.
             # If s is to be a DFI, it must be >=1.
             # For this problem, a,b are positive DFI, so a+b is always >=2.
             # if current_omega-1 is 1 (i.e. current_omega=2), then s < 1 is impossible.
             # if current_omega-1 is >1, then s < current_omega-1 is possible.
             return s # as DFI
        elif s >= 1 : # and s < current_omega -1 implicitly
            return s # as DFI
        else: # s < 1, this case should ideally not be hit with positive DFI inputs
            # This means result is conceptually <=0. AVCA would map this to Unio.
            # Our rule maps sums == Omega-1 to ZERO_UNIO. If sum is even less, like Omega-2...
            # The original AVCA rule for a+b < Omega was just 'return sum'.
            # The modified rule specifies threshold at Omega-1 and Omega.
            # Let's assume if s < current_omega-1 AND s is still a valid DFI value (>=1), it's s.
            # If s < 1, this implies a very small omega, or it's an edge case not well covered.
            # Given positive DFI, a+b >= 2.
            # If current_omega=3, omega-1=2. if s=a+b=2 (e.g. 1+1), then s == omega-1 -> ZU.
            # If current_omega=4, omega-1=3. if s=a+b=2 (e.g. 1+1), then s < omega-1 -> s=2.
             return s # This branch seems correct for s >= 1 and s < current_omega - 1
    elif s > current_omega : # strictly greater than omega
        return AREO_UNIO_sE1
    else: # Should not be reached due to previous conditions (s can't be < omega-1 and > omega simultaneously)
          # This implies s == current_omega-1 or s == current_omega which are handled.
          # Or s is exactly between current_omega-1 (exclusive) and current_omega (inclusive)
          # but s != current_omega and s != current_omega-1
          # This case should not exist.
          # For safety, default to an error or a defined Unio state.
          # print(f"Warning: Unhandled sum {s} for Omega {current_omega} in avc_add_boundary_tweak_sE1")
        return AREO_UNIO_sE1 # Fallback, though ideally all paths are covered.


# --- Helper to get carrier set S_Omega ---
def get_s_omega_algebraic_sE1(current_omega: int) -> List[AVCVal_sE1]:
    if current_omega == 1: return [ZERO_UNIO_sE1]
    s_omega: List[AVCVal_sE1] = [ZERO_UNIO_sE1]
    s_omega.extend(list(range(1, current_omega)))
    return s_omega

def prettify_subset_sE1(subset_list: List[AVCVal_sE1]) -> List[str]:
    return sorted([repr(e) if isinstance(e, Unio_sE1) else str(e) for e in subset_list])

# --- Inverse Check Function ---
def check_dfi_additive_inverses_sE1(op: Callable, current_omega: int):
    print(f"\n--- DFI Additive Inverse Check for Ω={current_omega} using '{op.__name__}' ---")
    s_omega = get_s_omega_algebraic_sE1(current_omega)
    dfi_elements = [e for e in s_omega if isinstance(e, int)]
    
    if not dfi_elements:
        print("  DFI is empty. No DFI inverses to check.")
        return

    all_dfi_have_unique_inverse = True
    for a_val in dfi_elements:
        algebraic_inverses_in_dfi: Set[int] = set()
        for x_val in dfi_elements:
            result = op(a_val, x_val, current_omega)
            if isinstance(result, Unio_sE1): # Result is algebraically Unio
                algebraic_inverses_in_dfi.add(x_val)
        
        num_dfi_inverses = len(algebraic_inverses_in_dfi)
        print(f"  DFI Element a = {a_val}:")
        print(f"    Set of DFI inverses {{x | a ⊕' x ~ Unio}}: {sorted(list(algebraic_inverses_in_dfi))}")
        print(f"    Number of unique DFI inverses: {num_dfi_inverses}")
        if num_dfi_inverses != 1:
            all_dfi_have_unique_inverse = False
            print(f"      -> Not universally unique for a={a_val} (found {num_dfi_inverses}).")
            
    if all_dfi_have_unique_inverse:
        print("  Result: All DFI elements have a unique DFI additive inverse in this context.")
    else:
        print("  Result: NOT all DFI elements have a unique DFI additive inverse in this context.")
    return all_dfi_have_unique_inverse

# --- Associativity Test Function ---
def test_associativity_sE1(op: Callable, current_omega: int):
    print(f"\n--- Associativity Test for Ω={current_omega} using '{op.__name__}' ---")
    s_omega = get_s_omega_algebraic_sE1(current_omega)
    associativity_holds = True
    counterexample: Any = None

    if not s_omega: return

    # print(f"  Carrier S_{current_omega} = {prettify_subset_sE1(s_omega)}")
    
    for sa in s_omega:
        for sb in s_omega:
            for sc in s_omega:
                try:
                    res_ab = op(sa, sb, current_omega)
                    lhs = op(res_ab, sc, current_omega)
                    res_bc = op(sb, sc, current_omega)
                    rhs = op(sa, res_bc, current_omega)

                    if not (lhs == rhs): 
                        associativity_holds = False
                        counterexample = (sa, sb, sc, lhs, rhs)
                        break
                except Exception as e:
                    associativity_holds = False
                    counterexample = (sa, sb, sc, "Exception", str(e))
                    break
            if not associativity_holds: break
        if not associativity_holds: break
    
    if associativity_holds:
        print("  Result: Additive Associativity HOLDS.")
    else:
        print("  Result: Additive Associativity FAILS.")
        if counterexample:
            sa_orig, sb_orig, sc_orig, lhs_res, rhs_res = counterexample
            sa_str = repr(sa_orig) if isinstance(sa_orig, Unio_sE1) else str(sa_orig)
            sb_str = repr(sb_orig) if isinstance(sb_orig, Unio_sE1) else str(sb_orig)
            sc_str = repr(sc_orig) if isinstance(sc_orig, Unio_sE1) else str(sc_orig)
            lhs_str = repr(lhs_res) if isinstance(lhs_res, Unio_sE1) else str(lhs_res)
            rhs_str = repr(rhs_res) if isinstance(rhs_res, Unio_sE1) else str(rhs_res)
            
            print(f"    Counterexample: a={sa_str}, b={sb_str}, c={sc_str}")
            print(f"      (a⊕'b)⊕'c = {lhs_str}")
            print(f"      a⊕'(b⊕'c) = {rhs_str}")
    return associativity_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script E.1: Elaborate Boundary Tweak for Addition - Inverse & Associativity Check ======")

    omegas_to_test = [3, 4] 
    # Math LLM also mentioned testing Omega=2 for the R2 script, let's test it here too for completeness
    # with this new rule.
    # omegas_to_test = [2, 3, 4]


    for omega_val_test in omegas_to_test:
        print(f"\n\n KKKKKKKKKKKKKKKKKKK TESTING FOR Ω = {omega_val_test} KKKKKKKKKKKKKKKKKKK")
        set_avca_omega_sE1(omega_val_test)
        
        # Test Ω=2 explicitly with this new rule to see if it behaves like R2.1 or differently
        if omega_val_test == 2:
            set_avca_omega_sE1(2)
            print("\n--- Explicit Test for Ω=2 with avc_add_boundary_tweak_sE1 ---")
            print("DFI = {1}")
            print(f"  1 ⊕' 1 (sum=2, Ω=2, Ω-1=1): rule 's == current_omega' (2==2) -> ZERO_UNIO_sE1")
            res_1_1 = avc_add_boundary_tweak_sE1(1,1,2)
            print(f"  Computed Fp(1) ⊕' Fp(1) = {res_1_1!r}") # Expected ZERO_UNIO_sE1
            # This forms Z2, which should be associative and have unique inverses.

        unique_inv = check_dfi_additive_inverses_sE1(avc_add_boundary_tweak_sE1, omega_val_test)
        assoc = test_associativity_sE1(avc_add_boundary_tweak_sE1, omega_val_test)
        
        print(f"\n  Summary for Ω={omega_val_test} with boundary tweak:")
        print(f"    Universal DFI Unique Inverses: {'Holds' if unique_inv else 'Fails (or N/A for DFI empty)'}")
        print(f"    Associativity: {'Holds' if assoc else 'Fails'}")


    print("\n====== E.1 Script Finished ======")