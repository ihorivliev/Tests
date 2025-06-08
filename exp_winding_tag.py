# Script R1.1: Winding Tag (Carry-Bit Logic) - Associativity Failure for (1,1,Ω-1)
# Mathematical Obligation: R1 from math LLM's refined deliverables.
# "Construct a triple (1,1,Ω−1) and show any ≤1-bit tag rule yields
#  non-associativity by direct case analysis. Script optional (only to show
#  concrete counter-triple)."
# This script instantiates this with a specific "carry-bit" like rule.

from typing import Union, Tuple, Any, Literal

# --- Core AVCA Components (adapted from AVCA Core DraftV4 Appendix A) ---
# These are simplified for the purpose of this script, focusing on what's needed.
_Omega_R1: int = 0

class Unio_R1:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_R1 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_R1) # Algebraic equivalence
    def __hash__(self) -> int:
        return hash(type(self))
    def __repr__(self) -> str:
        return f"Unio_R1('{self.aspect}')"

# Use specific Unio objects for clarity in rule definition
# ZERO_UNIO_R1 will represent the algebraic Unio in results and as identity value part
ZERO_UNIO_R1 = Unio_R1("zero")
AREO_UNIO_R1 = Unio_R1("areo") # Standard AVCA overflow target for classic_avc_add

AVCVal_R1 = Union[int, Unio_R1]

# Tagged State Representation: (value: AVCVal_R1, tag: bool)
TaggedAVCVal = Tuple[AVCVal_R1, bool]

def set_avca_omega_r1(omega_value: int):
    global _Omega_R1
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_R1 = omega_value
    print(f"\nGlobal Omega for R1.1 set to: {_Omega_R1}")

def _check_val_r1(x: AVCVal_R1, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega parameter ({current_omega}) must be an integer >= 1.")
    if isinstance(x, Unio_R1): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value: {x!r}. Expected int or Unio_R1. Omega={current_omega}")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI Value for Omega=1: {x}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value: {x}. For Omega={current_omega}, DFI must be [1, {current_omega - 1}].")

# Standard AVCA Add (⊕_v1.1 logic from Appendix A) - for internal use in winding add
def classic_avc_add_v1_1_internal(a: AVCVal_R1, b: AVCVal_R1, current_omega: int) -> AVCVal_R1:
    _check_val_r1(a, current_omega)
    _check_val_r1(b, current_omega)
    if isinstance(a, Unio_R1): return b
    if isinstance(b, Unio_R1): return a
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < current_omega else AREO_UNIO_R1 # Standard AVCA overflow to AREO

# --- Winding Tag Addition Rule (Carry-Bit Logic) ---
def avc_add_winding_carry(sa: TaggedAVCVal, sb: TaggedAVCVal, current_omega: int) -> TaggedAVCVal:
    """
    Performs addition on tagged AVCA values (value, tag_bool) using carry-bit logic for the tag.
    Identity state for addition is (ZERO_UNIO_R1, False).
    """
    va, ta = sa
    vb, tb = sb

    _check_val_r1(va, current_omega)
    _check_val_r1(vb, current_omega)

    final_value_part: AVCVal_R1
    new_tag: bool

    # Handle Unio Inputs for value part, tag logic combines input tags
    if isinstance(va, Unio_R1) and isinstance(vb, Unio_R1):
        final_value_part = ZERO_UNIO_R1 # U + U = U (represented by ZERO_UNIO_R1)
        new_tag = ta or tb
    elif isinstance(va, Unio_R1): # vb is DFI
        final_value_part = vb
        new_tag = ta or tb
    elif isinstance(vb, Unio_R1): # va is DFI
        final_value_part = va
        new_tag = ta or tb
    else: # Both va and vb are DFI
        classic_sum_obj = classic_avc_add_v1_1_internal(va, vb, current_omega)
        
        overflow_occurred_in_classic_sum = isinstance(classic_sum_obj, Unio_R1)
        
        if overflow_occurred_in_classic_sum:
            final_value_part = ZERO_UNIO_R1 # Consistent Unio representation for value part
        else:
            final_value_part = classic_sum_obj # DFI result
            
        new_tag = ta or tb or overflow_occurred_in_classic_sum
        
    return (final_value_part, new_tag)

# --- Associativity Test Function for Winding Tag Logic ---
def test_associativity_winding(op_winding: callable, current_omega: int,
                               a_tagged: TaggedAVCVal, b_tagged: TaggedAVCVal, c_tagged: TaggedAVCVal):
    
    va, ta = a_tagged
    vb, tb = b_tagged
    vc, tc = c_tagged
    
    print(f"\n--- Testing Associativity for Ω={current_omega} with Winding Op '{op_winding.__name__}' ---")
    print(f"  Triple: a_w = ({va!r}, {ta}), b_w = ({vb!r}, {tb}), c_w = ({vc!r}, {tc})")

    # LHS: (a_w + b_w) + c_w
    print("\n  Calculating LHS = (a_w + b_w) + c_w:")
    res_ab_tagged = op_winding(a_tagged, b_tagged, current_omega)
    print(f"    Step 1: a_w + b_w = ({res_ab_tagged[0]!r}, {res_ab_tagged[1]})")
    lhs_tagged = op_winding(res_ab_tagged, c_tagged, current_omega)
    print(f"    Step 2: (a_w + b_w) + c_w = ({lhs_tagged[0]!r}, {lhs_tagged[1]})")

    # RHS: a_w + (b_w + c_w)
    print("\n  Calculating RHS = a_w + (b_w + c_w):")
    res_bc_tagged = op_winding(b_tagged, c_tagged, current_omega)
    print(f"    Step 1: b_w + c_w = ({res_bc_tagged[0]!r}, {res_bc_tagged[1]})")
    rhs_tagged = op_winding(a_tagged, res_bc_tagged, current_omega)
    print(f"    Step 2: a_w + (b_w + c_w) = ({rhs_tagged[0]!r}, {rhs_tagged[1]})")

    # Comparison (both value and tag must match)
    associativity_holds = (lhs_tagged == rhs_tagged)

    print("\n  Result:")
    if associativity_holds:
        print(f"    Additive Associativity HOLDS for this triple and rule set at Ω={current_omega}.")
    else:
        print(f"    Additive Associativity FAILS for this triple and rule set at Ω={current_omega}.")
        print(f"      LHS = ({lhs_tagged[0]!r}, {lhs_tagged[1]})")
        print(f"      RHS = ({rhs_tagged[0]!r}, {rhs_tagged[1]})")

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script R1.1: Winding Tag (Carry-Bit Logic) - Associativity Test ======")

    # Test for Ω = 3 with triple (Fp(1), Fp(1), Fp(Ω-1)) = (1,1,2)
    # All initial tags are False
    omega_val = 3
    set_avca_omega_r1(omega_val)
    sa_3 = (1, False) # Fp(1) with tag False
    sb_3 = (1, False) # Fp(1) with tag False
    sc_3 = (omega_val - 1, False) # Fp(2) with tag False
    test_associativity_winding(avc_add_winding_carry, omega_val, sa_3, sb_3, sc_3)

    # Test for Ω = 4 with triple (Fp(1), Fp(1), Fp(Ω-1)) = (1,1,3)
    omega_val = 4
    set_avca_omega_r1(omega_val)
    sa_4 = (1, False) # Fp(1) with tag False
    sb_4 = (1, False) # Fp(1) with tag False
    sc_4 = (omega_val - 1, False) # Fp(3) with tag False
    test_associativity_winding(avc_add_winding_carry, omega_val, sa_4, sb_4, sc_4)
    
    # Example with a Unio input for sanity check (not the main test triple)
    # omega_val = 3
    # set_avca_omega_r1(omega_val)
    # sa_u = (ZERO_UNIO_R1, False)
    # sb_u = (1, False)
    # sc_u = (2, True) # Tagged
    # test_associativity_winding(avc_add_winding_carry, omega_val, sa_u, sb_u, sc_u)


    print("\n====== R1.1 Script Finished ======")