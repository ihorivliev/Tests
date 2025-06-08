# calculate_lens_loss.py
# Purpose: To implement the Stage 2-A lens definition and calculate the
# loss metric L(f) for various local frames with span S <= 7.
# This script focuses on the initial lens definition provided by the math LLM.

import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Set

# --- Unio Class Definition (Minimal for this script, only for ZERO_UNIO representation) ---
class Unio:
    __slots__ = ("aspect",)
    # For this script, we only care about its type for isinstance checks
    # and having a canonical Unio object to map to. Aspect not strictly used by lens_forward.
    def __init__(self, aspect: Literal["zero", "areo"] = "zero"): 
        self.aspect = aspect
    def __eq__(self, other: object) -> bool: 
        return isinstance(other, Unio) # All Unios are algebraically equal
    def __hash__(self) -> int:
        return hash(type(self))
    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"

# Canonical Unio representation for the target of the lens mapping
CANONICAL_UNIO_POLE = Unio("zero") # Using ZERO_UNIO as the representative

# Type Alias for mapped values (Canonical DFI or Canonical Unio)
MappedVal = Union[int, Unio]

# --- Lens Functions (as per Math LLM's Stage 2-A proposal) ---
def lens_forward(x: int, P_A: int, P_B: int) -> MappedVal:
    """
    Forward mapping from local frame value x to a canonical representation.
    Canonical DFI is {1, ..., S-1} where S = P_B - P_A.
    P_A and P_B map to CANONICAL_UNIO_POLE.
    """
    if not (P_A <= x <= P_B):
        raise ValueError(f"Value x={x} is outside the local frame [{P_A}, {P_B}]")
    
    if x == P_A or x == P_B:
        return CANONICAL_UNIO_POLE
    elif P_A < x < P_B:
        return x - P_A # Maps to canonical DFI: 1, 2, ..., S-1
    else: # Should not happen if P_A <= x <= P_B and x is not P_A or P_B
        raise ValueError("Logic error in lens_forward for DFI mapping")

# Inverse mapping (for conceptual completeness, not used in L(f) calculation here)
def lens_inverse(k_canonical: MappedVal, P_A: int, P_B: int) -> int:
    """
    Inverse mapping from canonical value k_canonical back to local frame.
    """
    S = P_B - P_A
    if isinstance(k_canonical, Unio):
        return P_A # Math LLM proposed P_A (could also be P_B or a choice)
    elif isinstance(k_canonical, int) and 1 <= k_canonical < S:
        return P_A + k_canonical
    else:
        raise ValueError(f"Invalid canonical value {k_canonical!r} for inversion into frame [{P_A},{P_B}] (span {S})")

# --- Loss Metric L(f) Calculation ---
def calculate_L_f(test_set_T: List[int], P_A: int, P_B: int) -> int:
    """
    Calculates the loss metric L(f) for the given test_set_T within frame [P_A, P_B].
    L(f) = count of ordered pairs (x,y) such that x,y in T, x != y, and f(x) == f(y).
    Equality for f(x) == f(y) uses algebraic equivalence for Unio.
    """
    loss_count = 0
    mapped_values = {val_t: lens_forward(val_t, P_A, P_B) for val_t in test_set_T}

    for x, y in itertools.product(test_set_T, test_set_T):
        if x == y:
            continue # x != y condition

        fx = mapped_values[x]
        fy = mapped_values[y]

        # Check for algebraic equality of mapped values
        # Our Unio.__eq__ handles Unio() == Unio() as True.
        # Integers compared normally. Unio() == int is False.
        if fx == fy: 
            loss_count += 1
            # print(f"  Collision: ({x}, {y}) -> f({x})={fx!r}, f({y})={fy!r}") # For debugging
            
    return loss_count

# --- Main Test Execution ---
def run_lens_loss_calculation():
    print("--- Starting Stage 2-B: Lens Definition & Loss Metric L Calculation ---")
    print("Using Math LLM's proposed lens:")
    print("  f(x, PA, PB): Unio if x=PA or x=PB, else x-PA")
    print("  Ω_eff = S = PB - PA (for S >= 2)")
    print("  L(f) = count of ordered pairs (x,y) in T, x!=y, where f(x)==f(y)\n")

    min_span = 2
    max_span = 7

    results = []

    for S in range(min_span, max_span + 1):
        # For simplicity and because L(f) for this lens is independent of P_A's absolute value,
        # we'll use P_A = 0 for each span.
        P_A = 0
        P_B = P_A + S
        
        # Test set T will be all integers in the local frame [P_A, P_B]
        test_set_T = list(range(P_A, P_B + 1))
        
        num_elements_in_T = len(test_set_T)
        if num_elements_in_T != S + 1:
            print(f"Error: For Span={S}, P_A={P_A}, P_B={P_B}, num_elements_in_T is {num_elements_in_T}, expected {S+1}")
            continue

        loss = calculate_L_f(test_set_T, P_A, P_B)
        results.append({
            "Span_S": S,
            "P_A": P_A,
            "P_B": P_B,
            "Test_Set_T_size": num_elements_in_T,
            "Loss_L(f)": loss
        })
        print(f"Span S={S} (Frame [{P_A},{P_B}], |T|={num_elements_in_T}): L(f) = {loss}")

    print("\n--- Lens Loss Calculation Completed ---")
    
    print("\nSummary Table of Loss Metric L(f):")
    print("Span (S) | Frame      | |T| | L(f) (Colliding Ordered Pairs)")
    print("---------|------------|-----|-------------------------------")
    for res in results:
        print(f"{res['Span_S']:<8} | [{res['P_A']},{res['P_B']}]      | {res['Test_Set_T_size']:<3} | {res['Loss_L(f)']:<30}")

    # Theoretical expectation for this lens and T = [P_A, ..., P_B]:
    # Only P_A and P_B map to the same value (CANONICAL_UNIO_POLE).
    # All other S-1 DFI values P_A+1, ..., P_B-1 map to unique canonical DFI values 1, ..., S-1.
    # So, the colliding pairs are (P_A, P_B) and (P_B, P_A). Thus, L(f) should always be 2.
    all_loss_is_2 = all(res['Loss_L(f)'] == 2 for res in results)
    if all_loss_is_2 and results: # Check if results list is not empty
        print("\nTheoretical Check: For T = all integers in [P_A, P_B], L(f) is consistently 2. Matches expectation.")
    elif results:
        print("\nTheoretical Check: For T = all integers in [P_A, P_B], L(f) DEVIATED from expected 2.")
    else:
        print("\nNo results to check against theory (min_span might be > max_span).")


if __name__ == "__main__":
    run_lens_loss_calculation()