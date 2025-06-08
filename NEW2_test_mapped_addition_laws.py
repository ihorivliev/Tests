# test_mapped_addition_laws.py
# Purpose: Stage 2-B - Tabulate which algebraic laws (for addition) survive
# after mapping local frame operations via the defined lens to canonical AVCA-S.
# Tests commutativity and associativity of mapped addition.

import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- Unio Class Definition (Minimal for canonical representation) ---
class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"] = "zero"):
        self.aspect = aspect # Aspect not strictly used by lens, but good for consistent Unio type
    def __eq__(self, other: object) -> bool: 
        return isinstance(other, Unio)
    def __hash__(self) -> int:
        return hash(type(self))
    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"

CANONICAL_UNIO_POLE = Unio("zero") # Target for mapped P_A, P_B
# For results from AVCA core operations that are Unio
CORE_ZERO_UNIO = Unio("zero")
CORE_AREO_UNIO = Unio("areo")


# --- Type Aliases ---
LocalVal = int # Values in the local frame [P_A, P_B] are integers
CanonicalVal = Union[int, Unio] # Values in the canonical AVCA-S frame

# --- Global Omega for Core AVCA operations ---
_CORE_AVCA_OMEGA: int = 0

# --- Core AVCA Domain Enforcement & Operations (v1.2b logic) ---
def _core_check_val(x: CanonicalVal, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"CoreAVCA Omega parameter must be an integer >= 1. Got: {current_omega}")
    if isinstance(x, Unio): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid CoreAVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")
    if current_omega == 1: # Canonical DFI is empty if S=1 (though lens defined for S>=2)
        if isinstance(x, int):
            raise ValueError(f"Invalid CoreAVCA DFI Value for Omega=1: {x}. DFI is empty.")
    # Canonical DFI for AVCA-S is {1, ..., S-1}
    elif not (1 <= x < current_omega): 
            raise ValueError(f"Invalid CoreAVCA DFI Value: {x}. For Omega={current_omega}, DFI must be in range [1, {current_omega - 1}].")

def core_avc_add(a: CanonicalVal, b: CanonicalVal) -> CanonicalVal: # ⊕_v1.1 logic
    global _CORE_AVCA_OMEGA
    if _CORE_AVCA_OMEGA == 0: raise ValueError("CoreAVCA Omega not set.")
    # Inputs 'a' and 'b' are already canonical, so _core_check_val uses _CORE_AVCA_OMEGA
    _core_check_val(a, _CORE_AVCA_OMEGA)
    _core_check_val(b, _CORE_AVCA_OMEGA)

    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    
    standard_sum = a + b # type: ignore 
    # In v1.1 add, overflow yields AREO_UNIO
    return standard_sum if standard_sum < _CORE_AVCA_OMEGA else CORE_AREO_UNIO

def set_core_avca_omega(omega_value: int):
    global _CORE_AVCA_OMEGA
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("CoreAVCA Omega must be an integer >= 1.")
    _CORE_AVCA_OMEGA = omega_value

# --- Lens Functions (Stage 2-A) ---
def lens_forward(x_local: LocalVal, P_A: int, P_B: int) -> CanonicalVal:
    if not (P_A <= x_local <= P_B):
        raise ValueError(f"Value x_local={x_local} is outside the local frame [{P_A}, {P_B}]")
    if x_local == P_A or x_local == P_B:
        return CANONICAL_UNIO_POLE 
    return x_local - P_A # Maps to canonical DFI {1, ..., S-1}

def lens_inverse(k_canonical: CanonicalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    if S < 1: raise ValueError("Span S must be >= 1 for lens_inverse.") # S>=2 for lens_forward
    
    if isinstance(k_canonical, Unio):
        return P_A # Map canonical Unio back to local P_A (origin)
    elif isinstance(k_canonical, int):
        # Canonical DFI is {1, ..., S-1}
        if 1 <= k_canonical < S:
            return P_A + k_canonical
        else: # Should not happen if core_avc_add is correct for AVCA-S
            # This indicates an issue or an unexpected canonical value (e.g. 0, or >=S)
            # For robustness, map unexpected int canonical results to a boundary.
            # This choice can affect law preservation. Math LLM suggested gPA(Unio)=PA
            # What about gPA(0) or gPA(S) if they are somehow produced by core_avc_add?
            # core_avc_add with S as Omega should produce DFI {1..S-1} or Unio (AREO/ZERO).
            # So, if k_canonical is int, it *should* be in {1..S-1}.
            # If core_avc_add produces an int outside this, it's a problem with core_avc_add's closure for AVCA-S
            # or _core_check_val failed for its result.
            # Given totality of core_avc_add, its int results are DFI {1..S-1}.
            # This 'else' might be for unexpected canonical integer values.
            # Let's assume k_canonical will be valid DFI {1..S-1} or Unio.
             raise ValueError(f"Invalid canonical DFI value {k_canonical} for inversion into span {S}")
    else:
        raise TypeError(f"Invalid type for k_canonical: {type(k_canonical)}")

# --- Mapped AVCA Operation ---
def mapped_avc_add(x_local: LocalVal, y_local: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    if S < 1 : raise ValueError("Span S must be >= 1 for mapped operations.")
    if S == 1 and not (isinstance(lens_forward(x_local, P_A, P_B), Unio) and isinstance(lens_forward(y_local, P_A, P_B), Unio)):
        # For S=1 (e.g. [0,1]), DFI_canonical is empty. Only Unio ops possible.
        # x_local and y_local must be P_A or P_B.
         pass # let lens_forward handle this. If S=1, P_A and P_B are distinct. Ω_eff=1.

    val_x_canon = lens_forward(x_local, P_A, P_B)
    val_y_canon = lens_forward(y_local, P_A, P_B)
    
    set_core_avca_omega(S) # Set Omega for the canonical AVCA-S operation
    
    res_canon = core_avc_add(val_x_canon, val_y_canon)
    
    res_local = lens_inverse(res_canon, P_A, P_B)
    return res_local

# --- Helper to compare local results (integers) ---
# Since results of mapped_avc_add are local integers, direct == is fine.
# Unio is not expected as a final local result from lens_inverse as defined.
def local_equals(val1: LocalVal, val2: LocalVal) -> bool:
    return val1 == val2

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Mapped Addition Law Tests (Stage 2-B) ---")
    print("    Using lens: f(x)=Unio if x=PA/PB, else x-PA. g(Unio)=PA, g(k)=PA+k.\n")
    
    # Spans S to test. For S, Omega_eff = S. Local frame [0,S] has S+1 elements.
    spans_to_test = [2, 3, 4] 
    # Span S=2 -> Omega_eff=2 (Core is Group). Local frame [0,1,2]
    # Span S=3 -> Omega_eff=3 (Core is Non-Associative Loop). Local frame [0,1,2,3]
    # Span S=4 -> Omega_eff=4 (Core is Non-Associative Loop). Local frame [0,1,2,3,4]

    P_A = 0 # Keep P_A fixed for simplicity, as lens behavior is relative to span

    for S_val in spans_to_test:
        P_B = P_A + S_val
        print(f"--- Testing with Local Span S = {S_val} (Frame [{P_A},{P_B}], Canonical AVCA-{S_val}) ---")
        
        local_elements: List[LocalVal] = list(range(P_A, P_B + 1))
        if not local_elements : continue

        # Test Commutativity of mapped_avc_add
        print(f"  Testing Commutativity of mapped_avc_add for S={S_val}")
        comm_law_holds = True
        comm_counterexample = None
        comm_checked_pairs = 0
        for x, y in itertools.product(local_elements, local_elements):
            comm_checked_pairs += 1
            try:
                res1 = mapped_avc_add(x, y, P_A, P_B)
                res2 = mapped_avc_add(y, x, P_A, P_B)
                if not local_equals(res1, res2):
                    comm_law_holds = False
                    comm_counterexample = (x,y,res1,res2)
                    break
            except Exception as e:
                comm_law_holds = False
                comm_counterexample = (x,y, "Exception", str(e))
                break
        status_comm = "Holds" if comm_law_holds else f"FAILS (e.g., x={comm_counterexample[0]}, y={comm_counterexample[1]} -> xy={comm_counterexample[2]}, yx={comm_counterexample[3]})"
        print(f"    Commutativity: {status_comm} (Checked {comm_checked_pairs} pairs)")

        # Test Associativity of mapped_avc_add
        print(f"  Testing Associativity of mapped_avc_add for S={S_val}")
        assoc_law_holds = True
        assoc_counterexample = None
        assoc_checked_triplets = 0
        # For S=2, |local_elements|=3. 3^3 = 27.
        # For S=3, |local_elements|=4. 4^3 = 64.
        # For S=4, |local_elements|=5. 5^3 = 125.
        if S_val > 3 and len(local_elements) > 4: # Reduce triplets for larger spans if too slow
             print(f"    (Note: Associativity check for S={S_val} might be slow, checking a subset or consider sampling if needed)")
        
        for x, y, z in itertools.product(local_elements, local_elements, local_elements):
            assoc_checked_triplets += 1
            try:
                lhs = mapped_avc_add(mapped_avc_add(x, y, P_A, P_B), z, P_A, P_B)
                rhs = mapped_avc_add(x, mapped_avc_add(y, z, P_A, P_B), P_A, P_B)
                if not local_equals(lhs, rhs):
                    assoc_law_holds = False
                    assoc_counterexample = (x,y,z,lhs,rhs)
                    break
            except Exception as e:
                assoc_law_holds = False
                assoc_counterexample = (x,y,z, "Exception", str(e))
                break
            if not assoc_law_holds: break
        status_assoc = "Holds" if assoc_law_holds else f"FAILS (e.g., x={assoc_counterexample[0]}, y={assoc_counterexample[1]}, z={assoc_counterexample[2]} -> (xy)z={assoc_counterexample[3]}, x(yz)={assoc_counterexample[4]})"
        print(f"    Associativity: {status_assoc} (Checked up to {assoc_checked_triplets} triplets)")
        print("-" * 70)

    print("\n--- Mapped Addition Law Tests Completed ---")

if __name__ == "__main__":
    run_all_tests()