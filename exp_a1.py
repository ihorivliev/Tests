# Script A.1: Associativity Check for Size-3 Subsets {U,k,j} (k,j ≠ 1) using ⊕_v1.1
# Red-Team Audit: Claim 1 "Associativity (of ⊕_v1.1) holds iff Ω ≤ 2"
# Falsification Strategy: Enumerate size-3 subsets R={U,k,j} (k,j≠1, k≠j)
# for Ω=3,4,5 and brute-check associativity of ⊕_v1.1 with operands from R.

from typing import Union, List, Tuple, Any, Literal, Set, FrozenSet
import itertools

# --- Core AVCA Components (adapted from previous scripts / AVCA Core DraftV4 App A) ---
_Omega_A1: int = 0

class Unio_A1:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_A1 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_A1) 
    def __hash__(self) -> int:
        return hash(f"Unio_A1_Algebraic_Singleton") 
    def __repr__(self) -> str:
        return f"Unio_A1('{self.aspect}')"
    def __lt__(self, other): # For sorting in prettify_subset
        if isinstance(other, Unio_A1): return False
        if isinstance(other, int): return True 
        return NotImplemented


ZERO_UNIO_A1 = Unio_A1("zero") # Representative for algebraic Unio
AREO_UNIO_A1 = Unio_A1("areo") # Standard AVCA overflow target for classic_avc_add
AVCVal_A1 = Union[int, Unio_A1]

def set_avca_omega_a1(omega_value: int):
    global _Omega_A1
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_A1 = omega_value

def _check_val_a1(x: AVCVal_A1, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega ({current_omega}) for {var_name} must be >= 1.")
    if isinstance(x, Unio_A1): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Omega={current_omega}")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI {x} for {var_name} for Omega=1. DFI empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI {x} for {var_name}. Omega={current_omega}, DFI [1,{current_omega-1}]")

# Standard AVCA Add (⊕_v1.1 logic from AVCA Core DraftV4 Appendix A)
def avc_add_v1_1_a1(a: AVCVal_A1, b: AVCVal_A1, current_omega: int) -> AVCVal_A1:
    _check_val_a1(a, current_omega, "add_a")
    _check_val_a1(b, current_omega, "add_b")
    if isinstance(a, Unio_A1): return b
    if isinstance(b, Unio_A1): return a
    res_val: int = a + b # type: ignore
    return res_val if res_val < current_omega else AREO_UNIO_A1

# --- Helper Functions ---
def get_s_omega_algebraic_a1(current_omega: int) -> List[AVCVal_A1]:
    if current_omega == 1: return [ZERO_UNIO_A1]
    s_omega: List[AVCVal_A1] = [ZERO_UNIO_A1]
    s_omega.extend(list(range(1, current_omega)))
    return s_omega

def prettify_subset_a1(subset: FrozenSet[AVCVal_A1]) -> List[str]:
    return sorted([repr(e) if isinstance(e, Unio_A1) else str(e) for e in subset])

# --- Associativity Test for Specified Subsets ---
def check_associativity_on_subset(
    subset_r: FrozenSet[AVCVal_A1], 
    op: callable, 
    current_omega: int
) -> Tuple[bool, Any]:
    """
    Checks if op is associative for all triplets from subset_r.
    Returns (True, None) if associative, or (False, counterexample_tuple) if not.
    Operations are global AVCA operations.
    """
    for sa in subset_r:
        for sb in subset_r:
            for sc in subset_r:
                try:
                    res_ab = op(sa, sb, current_omega)
                    lhs = op(res_ab, sc, current_omega)
                    res_bc = op(sb, sc, current_omega)
                    rhs = op(sa, res_bc, current_omega)

                    if not (lhs == rhs): # Algebraic equality due to Unio_A1.__eq__
                        return False, (sa, sb, sc, lhs, rhs)
                except Exception as e:
                    return False, (sa, sb, sc, "Exception", str(e))
    return True, None

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script A.1: Associativity Check for Size-3 Subsets {U,k,j} (k,j ≠ 1) using ⊕_v1.1 ======")

    omegas_to_test = [3, 4, 5]
    found_associative_subset_for_omega_ge_3 = False

    for omega_val in omegas_to_test:
        set_avca_omega_a1(omega_val)
        s_omega_full = get_s_omega_algebraic_a1(omega_val)
        
        # DFI elements greater than 1
        dfi_gt_1 = [dfi for dfi in s_omega_full if isinstance(dfi, int) and dfi > 1]

        print(f"\n--- Testing Ω = {omega_val} ---")
        if len(dfi_gt_1) < 2:
            print(f"  Not enough DFI elements > 1 to form a size-3 subset {{U,k,j}} with k,j ≠ 1, k≠j.")
            continue

        # Generate 2-element combinations from dfi_gt_1
        dfi_combinations = list(itertools.combinations(dfi_gt_1, 2))
        
        if not dfi_combinations:
            print(f"  No valid pairs {{k,j}} with k,j > 1, k≠j found for Ω={omega_val}.")
            continue

        print(f"  Generated {len(dfi_combinations)} pairs {{k,j}} from DFI > 1.")
        subsets_checked_count = 0
        associative_candidates_found_this_omega = 0

        for dfi_pair in dfi_combinations:
            k, j = dfi_pair
            subset_R_elements = [ZERO_UNIO_A1, k, j]
            subset_R = frozenset(subset_R_elements)
            subsets_checked_count +=1

            # print(f"  Checking subset R = {prettify_subset_a1(subset_R)}...")
            
            is_associative, counterexample = check_associativity_on_subset(
                subset_R, avc_add_v1_1_a1, omega_val
            )

            if is_associative:
                print(f"  POTENTIAL FINDING for Ω={omega_val}: Subset {prettify_subset_a1(subset_R)} IS associative for ⊕_v1.1!")
                found_associative_subset_for_omega_ge_3 = True
                associative_candidates_found_this_omega +=1
            # else:
                # For brevity, only print if associative is found, or print first failure if needed for debug.
                # sa_orig, sb_orig, sc_orig, lhs_res, rhs_res = counterexample
                # print(f"    Associativity FAILS for subset {prettify_subset_a1(subset_R)}.")
                # print(f"      Counterexample: a={sa_orig!r}, b={sb_orig!r}, c={sc_orig!r} -> LHS={lhs_res!r}, RHS={rhs_res!r}")

        if associative_candidates_found_this_omega == 0:
            print(f"  No size-3 subsets of the form {{U,k,j}} (k,j≠1, k≠j) found to be associative for Ω={omega_val}.")
        else:
            print(f"  Found {associative_candidates_found_this_omega} size-3 subsets of form {{U,k,j}} (k,j≠1, k≠j) that ARE associative for Ω={omega_val}.")


    print("\n--- Summary of Red-Team Audit A.1 ---")
    if found_associative_subset_for_omega_ge_3:
        print("  WARNING: At least one size-3 subset {U,k,j} (k,j≠1) for Ω≥3 was found where ⊕_v1.1 IS associative.")
        print("  This would challenge Claim 1's implication if such subsets are also closed and lead to larger classical structures.")
    else:
        print("  SUCCESS: No size-3 subsets of the form {U,k,j} (k,j≠1, k≠j) were found where ⊕_v1.1 is associative for Ω≥3.")
        print("  This supports the assertion that associativity failure for ⊕_v1.1 is pervasive for Ω≥3,")
        print("  and not easily rescued by restricting operands to specific small subsets lacking Fp(1).")

    print("\n====== A.1 Script Finished ======")