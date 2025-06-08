# Script S6.1: Brute-Force Sub-Ring Search for AVCA-Ω (Ω=3, 4)
# Mathematical Obligation: Stage 6 from math LLM's roadmap (sanity check part).
# "Have the coding-LLM run a brute subset search for Ω = 3, 4 to
#  corroborate the proof empirically."
# Goal: To check if any non-empty subsets of S_Ω (for Ω=3, 4) form a sub-ring
#       under AVCA's ⊕_v1.1 and ⊗_v1.2 operations.

from typing import Union, List, Tuple, Any, Literal, Set, FrozenSet, Callable
import itertools

# --- Core AVCA Components (adapted from R4.x scripts / AVCA Core DraftV4 App A) ---
_Omega_S6: int = 0

class Unio_S6:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_S6 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_S6) 
    def __hash__(self) -> int:
        # Critical for using Unio objects in sets/dictionary keys for subsets
        return hash(f"Unio_S6_Algebraic_Singleton") 
    def __repr__(self) -> str:
        return f"Unio_S6('{self.aspect}')"
    def __lt__(self, other): # For sorting, not strictly necessary for logic
        if isinstance(other, Unio_S6): return False
        if isinstance(other, int): return True # Unio considered "less than" DFI for sorting
        return NotImplemented

ZERO_UNIO_S6 = Unio_S6("zero")
AREO_UNIO_S6 = Unio_S6("areo") 
AVCVal_S6 = Union[int, Unio_S6]

def set_avca_omega_s6(omega_value: int):
    global _Omega_S6
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_S6 = omega_value

def _check_val_s6(x: AVCVal_S6, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega ({current_omega}) for {var_name} must be >= 1.")
    if isinstance(x, Unio_S6): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Omega={current_omega}")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI {x} for {var_name} for Omega=1. DFI empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI {x} for {var_name}. Omega={current_omega}, DFI [1,{current_omega-1}]")

# Standard AVCA Add (⊕_v1.1)
def avc_add_v1_1_s6(a: AVCVal_S6, b: AVCVal_S6, current_omega: int) -> AVCVal_S6:
    _check_val_s6(a, current_omega, "add_a")
    _check_val_s6(b, current_omega, "add_b")
    if isinstance(a, Unio_S6): return b
    if isinstance(b, Unio_S6): return a
    res_val: int = a + b # type: ignore
    return res_val if res_val < current_omega else AREO_UNIO_S6

# Standard AVCA Mul (⊗_v1.2)
def avc_mul_v1_2_s6(a: AVCVal_S6, b: AVCVal_S6, current_omega: int) -> AVCVal_S6:
    _check_val_s6(a, current_omega, "mul_a")
    _check_val_s6(b, current_omega, "mul_b")

    a_is_unio = isinstance(a, Unio_S6)
    b_is_unio = isinstance(b, Unio_S6)

    # For representing algebraic U in subsets, we use ZERO_UNIO_S6.
    # AREO_UNIO_S6 can be a *result* of operations.
    # The aspect handling in v1.2 is crucial.
    # If an input 'a' or 'b' from our subset *is* U (represented by ZERO_UNIO_S6),
    # its aspect for the mul rule is "zero".
    # If a DFI*DFI overflow produces AREO_UNIO_S6, that has "areo" aspect.

    if a_is_unio or b_is_unio:
        a_obj = a if a_is_unio else None
        b_obj = b if b_is_unio else None
        
        is_any_areo_aspected = (a_is_unio and a_obj.aspect == "areo") or \
                               (b_is_unio and b_obj.aspect == "areo") # type: ignore
        
        # If one operand is Unio (from subset, represented by ZERO_UNIO_S6) and other is DFI,
        # and no AREO_UNIO is involved, result is ZERO_UNIO_S6.
        # If an AREO_UNIO_S6 is an input (e.g. if it was a prior result and IS in the subset), it dominates.
        # If both are ZERO_UNIO_S6, result is ZERO_UNIO_S6.
        if is_any_areo_aspected:
            return AREO_UNIO_S6
        else: # All Unio operands involved must be effectively "zero" aspect from subset context
            return ZERO_UNIO_S6
    else: # Both DFI
        res_val: int = a * b # type: ignore
        return res_val if (1 <= res_val < current_omega) else AREO_UNIO_S6

# --- Helper Functions ---
def get_s_omega_algebraic(current_omega: int) -> List[AVCVal_S6]:
    """Returns S_Omega using ZERO_UNIO_S6 as the representative for algebraic Unio."""
    if current_omega == 1:
        return [ZERO_UNIO_S6]
    s_omega: List[AVCVal_S6] = [ZERO_UNIO_S6]
    s_omega.extend(list(range(1, current_omega)))
    return s_omega

def get_all_non_empty_subsets(s_omega: List[AVCVal_S6]) -> List[FrozenSet[AVCVal_S6]]:
    """Generates all non-empty subsets of S_Omega as frozensets."""
    subsets = []
    n = len(s_omega)
    for i in range(1, 1 << n): # Iterate from 1 to 2^n - 1
        subset = []
        for j in range(n):
            if (i >> j) & 1:
                subset.append(s_omega[j])
        subsets.append(frozenset(subset))
    return subsets

def is_algebraically_in_subset(element: AVCVal_S6, subset: FrozenSet[AVCVal_S6]) -> bool:
    """Checks if an element (algebraically) is in a subset."""
    if isinstance(element, Unio_S6): # Any Unio object represents algebraic Unio
        return any(isinstance(sub_elem, Unio_S6) for sub_elem in subset)
    return element in subset

def check_closure(subset: FrozenSet[AVCVal_S6], op: Callable, current_omega: int) -> bool:
    if not subset: return True # Empty set is trivially closed
    for a_sub in subset:
        for b_sub in subset:
            # When calling op, use representative objects.
            # Our subsets store ZERO_UNIO_S6 as the Unio representative.
            # DFI elements are ints.
            # The op itself will handle aspects if results like AREO_UNIO_S6 are produced.
            val_a = a_sub
            val_b = b_sub
            
            result = op(val_a, val_b, current_omega)
            if not is_algebraically_in_subset(result, subset):
                # print(f"Closure failed for {op.__name__} on subset {prettify_subset(subset)} with {val_a!r} op {val_b!r} -> {result!r}")
                return False
    return True

def check_associativity(subset: FrozenSet[AVCVal_S6], op: Callable, current_omega: int) -> bool:
    if not subset: return True
    for a_sub in subset:
        for b_sub in subset:
            for c_sub in subset:
                lhs = op(op(a_sub, b_sub, current_omega), c_sub, current_omega)
                rhs = op(a_sub, op(b_sub, c_sub, current_omega), current_omega)
                if lhs != rhs: # Algebraic equality due to Unio_S6.__eq__
                    return False
    return True

def check_additive_identity(subset: FrozenSet[AVCVal_S6], add_op: Callable, current_omega: int) -> bool:
    # Assumes ZERO_UNIO_S6 is the candidate identity
    identity_candidate = ZERO_UNIO_S6
    if not is_algebraically_in_subset(identity_candidate, subset):
        return False
    for a_sub in subset:
        if add_op(a_sub, identity_candidate, current_omega) != a_sub: return False
        if add_op(identity_candidate, a_sub, current_omega) != a_sub: return False
    return True

def check_additive_inverses(subset: FrozenSet[AVCVal_S6], add_op: Callable, current_omega: int) -> bool:
    identity_candidate = ZERO_UNIO_S6 # Algebraic Unio
    if not is_algebraically_in_subset(identity_candidate, subset): # Should be caught by identity check
        return False 
        
    for a_sub in subset:
        found_inverse_in_subset = False
        for x_sub in subset:
            res = add_op(a_sub, x_sub, current_omega)
            if isinstance(res, Unio_S6): # Result is algebraically Unio
                found_inverse_in_subset = True
                break
        if not found_inverse_in_subset:
            return False
    return True

def check_distributivity(subset: FrozenSet[AVCVal_S6], add_op: Callable, mul_op: Callable, current_omega: int) -> bool:
    if not subset: return True
    for a_sub in subset:
        for b_sub in subset:
            for c_sub in subset:
                # Left: a * (b + c)
                val_b_plus_c = add_op(b_sub, c_sub, current_omega)
                lhs = mul_op(a_sub, val_b_plus_c, current_omega)
                
                # Right: (a * b) + (a * c)
                val_a_mul_b = mul_op(a_sub, b_sub, current_omega)
                val_a_mul_c = mul_op(a_sub, c_sub, current_omega)
                rhs = add_op(val_a_mul_b, val_a_mul_c, current_omega)
                
                if lhs != rhs: # Algebraic equality
                    return False
    return True

def prettify_subset(subset: FrozenSet[AVCVal_S6]) -> List[str]:
    return sorted([repr(e) if isinstance(e, Unio_S6) else str(e) for e in subset])

# --- Main Sub-Ring Search Function ---
def find_subrings(current_omega: int):
    set_avca_omega_s6(current_omega)
    s_omega_list = get_s_omega_algebraic(current_omega)
    all_subs = get_all_non_empty_subsets(s_omega_list)
    
    print(f"\n--- Sub-Ring Sanity Check for Ω = {current_omega} ---")
    print(f"S_{current_omega} = {prettify_subset(frozenset(s_omega_list))}")
    print(f"Total non-empty subsets to check: {len(all_subs)}")

    found_subrings_count = 0

    for i, r_subset in enumerate(all_subs):
        # print(f"\nChecking subset {i+1}/{len(all_subs)}: {prettify_subset(r_subset)}")

        # 1. Closure under ⊕ and ⊗
        closed_add = check_closure(r_subset, avc_add_v1_1_s6, current_omega)
        if not closed_add:
            # print("  Not closed under ⊕_v1.1")
            continue
        closed_mul = check_closure(r_subset, avc_mul_v1_2_s6, current_omega)
        if not closed_mul:
            # print("  Not closed under ⊗_v1.2")
            continue
        
        # print("  Closed under ⊕_v1.1 and ⊗_v1.2.")

        # 2. (R, ⊕) is Abelian Group
        # Commutativity of ⊕ is inherited.
        add_associative = check_associativity(r_subset, avc_add_v1_1_s6, current_omega)
        if not add_associative:
            # print("  ⊕_v1.1 is NOT associative on this subset.")
            continue
        # print("  ⊕_v1.1 IS associative on this subset.")

        has_add_identity = check_additive_identity(r_subset, avc_add_v1_1_s6, current_omega)
        if not has_add_identity:
            # print("  Does NOT have additive identity (Unio) in subset or it doesn't act as such.")
            continue
        # print("  ⊕_v1.1 HAS additive identity (Unio) in subset.")
            
        has_add_inverses = check_additive_inverses(r_subset, avc_add_v1_1_s6, current_omega)
        if not has_add_inverses:
            # print("  NOT all elements have additive inverses within the subset.")
            continue
        # print("  ⊕_v1.1 HAS additive inverses in subset for all its elements.")

        # 3. (R, ⊗) is Semigroup
        # Associativity of ⊗ is inherited from S_Omega if closed.
        # mul_associative = check_associativity(r_subset, avc_mul_v1_2_s6, current_omega)
        # if not mul_associative:
        #     print("  ⊗_v1.2 is NOT associative on this subset. (This would be surprising)")
        #     continue
        # print("  ⊗_v1.2 IS associative on this subset.") (Known from S_Omega)

        # 4. Distributivity of ⊗ over ⊕
        is_distributive = check_distributivity(r_subset, avc_add_v1_1_s6, avc_mul_v1_2_s6, current_omega)
        if not is_distributive:
            # print("  Distributivity FAILS on this subset.")
            continue
        # print("  Distributivity HOLDS on this subset.")

        # If all checks pass, it's a sub-ring
        print(f"\n  FOUND POTENTIAL SUB-RING: {prettify_subset(r_subset)}")
        print(f"    Closed ⊕: Yes, Closed ⊗: Yes")
        print(f"    ⊕ Associative: Yes, ⊕ Identity: Yes, ⊕ Inverses: Yes")
        print(f"    Distributive (⊗ over ⊕): Yes")
        found_subrings_count +=1
        
    if found_subrings_count == 0:
        print("\n  No non-trivial sub-rings found (besides potentially {Unio} if it passed all tests alone).")
    elif found_subrings_count == 1 and prettify_subset(frozenset([ZERO_UNIO_S6])) == prettify_subset(list(filter(lambda r: "FOUND POTENTIAL SUB-RING" in str(r), map(str, all_subs))))[0].split(": ")[1]: # Complex check
         print(f"\n  Only the trivial sub-ring {{Unio}} was found for Ω={current_omega}.")
    else:
        print(f"\n  Found {found_subrings_count} potential sub-rings for Ω={current_omega} (see details above).")


# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script S6.1: Brute-Force Sub-Ring Search for AVCA-Ω ======")
    
    find_subrings(current_omega=3)
    find_subrings(current_omega=4)

    print("\n====== S6.1 Script Finished ======")