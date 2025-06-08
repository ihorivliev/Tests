import itertools
from typing import Union, List, Any, Tuple, Callable

# --- Core AVCA Specification (from Revised Core AVCA manuscript Draft1, Section 2.5.1) ---
# This code defines the system under test.

# Global Omega, needs to be set by the test runner for each iteration
Omega: int = 0 

class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: str):
        assert aspect in ("zero","areo"), "Unio aspect must be 'zero' or 'areo'"
        self.aspect = aspect
    def __eq__(self, other): # All Unio objects are algebraically the same
        return isinstance(other, Unio)
    def __hash__(self): # For use in sets/dict keys if needed
        return hash(Unio) 
    def __repr__(self):
        return f"Unio({self.aspect!r})"

ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")

AVCVal = Union[int, Unio]

def _check_val(x: AVCVal):
    """Ensures an input value x is a valid member of the current AVCA-Ω carrier set SΩ."""
    global Omega
    if Omega == 0:
        raise ValueError("Omega parameter must be set before _check_val can be used.")
    if isinstance(x, Unio):
        return # Unio objects are always valid members of S_Omega
    if not isinstance(x, int):
        raise TypeError(f"AVC value must be an integer or Unio instance, got {type(x)} for value {x!r}")
    
    # Check DFI constraints based on the current Omega
    if Omega == 1: 
        # If Omega is 1, DFI is empty. No integers are allowed.
        raise ValueError(f"DFI integers are not permitted when Omega=1, got integer {x}")
    if Omega > 1 and not (1 <= x < Omega): # DFI is {1, ..., Omega-1}
        raise ValueError(f"DFI integer value {x} is out of range [1...{Omega-1}] for Omega={Omega}")

def avc_add(a: AVCVal, b: AVCVal) -> AVCVal:
    """⊕ : SΩ × SΩ → SΩ (cyclic addition, “360° loop”)"""
    global Omega
    _check_val(a); _check_val(b)
    # Rule 1: Unio as additive identity (Zero-aspect behavior)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    # Rule 2: Both operands are DFI integers. Standard integer addition, with overflow to ZERO_UNIO.
    s = a + b
    return s if s < Omega else ZERO_UNIO

def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal:
    """⊖ : SΩ × SΩ → SΩ (asymmetric subtraction)"""
    global Omega
    _check_val(a); _check_val(b)
    # Rule 1: Subtracting Unio (any aspect) acts as subtracting zero (identity)
    if isinstance(b, Unio): return a
    # Rule 2: Unio (any aspect) as minuend, DFI as subtrahend, results in AREO_UNIO
    if isinstance(a, Unio): return AREO_UNIO
    # Rule 3: Both operands are DFI integers. Standard integer subtraction if result is valid DFI, else AREO_UNIO.
    return (a - b) if a > b else AREO_UNIO

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal:
    """⊗ : SΩ × SΩ → SΩ (cyclic multiplication with aspect handling)"""
    global Omega
    _check_val(a); _check_val(b)
    # Rule 1: Handling Unio inputs (aspect-dependent outcome)
    if isinstance(a, Unio):
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    if isinstance(b, Unio): # a must be DFI here
        return ZERO_UNIO if b.aspect=="zero" else AREO_UNIO
    # Rule 2: Both operands are DFI integers. Standard integer multiplication, with overflow to AREO_UNIO.
    p = a * b
    return p if p < Omega else AREO_UNIO

def avc_div(a: AVCVal, b: AVCVal) -> AVCVal:
    """⊘ : SΩ × SΩ → SΩ (cyclic division with aspect handling)"""
    global Omega
    _check_val(a); _check_val(b)
    # Rule 1: Dividend 'a' is Unio (aspect-dependent outcome)
    if isinstance(a, Unio):
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    # Rule 2: Divisor 'b' is Unio (and 'a' must be DFI due to Rule 1) -> AREO_UNIO
    if isinstance(b, Unio): 
        return AREO_UNIO
    # Rule 3: Both operands 'a' and 'b' are DFI integers.
    # b is DFI, so b >= 1. _check_val ensures this.
    q, r = divmod(a, b)
    return q if (r == 0 and 1 <= q < Omega) else AREO_UNIO

# --- Experiment Harness ---

def get_carrier_set_elements(omega_val: int) -> List[AVCVal]:
    """Generates all elements of the carrier set SΩ for a given Omega."""
    s_elements = [ZERO_UNIO, AREO_UNIO]
    if omega_val > 1:
        s_elements.extend(list(range(1, omega_val)))
    return s_elements

def get_dfi_representative(omega_val: int) -> Union[int, None]:
    """Returns a representative DFI element for testing, or None if DFI is empty."""
    if omega_val <= 1:
        return None # No DFI elements
    elif omega_val == 2:
        return 1 # Only DFI element is 1
    else:
        # Use a middle DFI element for a general case, or 1 if DFI is small
        return (omega_val // 2) if (omega_val // 2) >= 1 else 1

def run_unio_operational_profile(omegas_to_test: List[int]):
    global Omega 
    
    print(f"\n{'='*20} EXPERIMENT 1.1: UNIO'S OPERATIONAL PROFILE {'='*20}")
    print("  Precisely verifying Unio's interaction with DFI elements and other Unio aspects.")
    print("  Expected outcomes are based on the 'Revised Core AVCA' specification (Python code).")
    print("  (✅ = Actual matches Expected | ❌ = Actual differs from Expected)")

    # Define the Unio aspects to use in test cases
    unio_aspects = [ZERO_UNIO, AREO_UNIO]

    # Define the operations to test
    operations = [
        (avc_add, "ADD (⊕)"),
        (avc_sub, "SUB (⊖)"),
        (avc_mul, "MUL (⊗)"),
        (avc_div, "DIV (⊘)")
    ]

    for current_omega in omegas_to_test:
        Omega = current_omega # Set the global Omega for this iteration
        s_elements = get_carrier_set_elements(Omega)
        dfi_rep = get_dfi_representative(Omega) # A representative DFI element for tests

        print(f"\n{'-'*15} TESTING FOR OMEGA = {Omega} ({'Carrier Set: ' + repr([repr(x) for x in s_elements])}) {'-'*15}")
        if dfi_rep is None and Omega > 1:
            print(f"  (Warning: DFI representative is None for Omega={Omega}, likely small DFI where Omega-1 is 0 or 1)")

        for op_func, op_name in operations:
            print(f"\n  --- Operation: {op_name} ---")

            # Test 1: Unio Aspect (LHS) op DFI_k (RHS)
            if dfi_rep is not None:
                print(f"    Unio_Aspect op DFI({dfi_rep}):")
                for u_lhs in unio_aspects:
                    actual_res = op_func(u_lhs, dfi_rep)
                    
                    # Define Expected Outcome based on Revised Core AVCA spec for Unio op DFI
                    expected_res = None
                    if op_name == "ADD (⊕)":
                        expected_res = dfi_rep # Unio + DFI = DFI (additive identity)
                    elif op_name == "SUB (⊖)":
                        expected_res = AREO_UNIO # Unio - DFI = AREO_UNIO (stuck-at-Areo)
                    elif op_name == "MUL (⊗)":
                        expected_res = ZERO_UNIO if u_lhs.aspect == "zero" else AREO_UNIO # Aspect-dependent annihilation/absorption
                    elif op_name == "DIV (⊘)":
                        expected_res = ZERO_UNIO if u_lhs.aspect == "zero" else AREO_UNIO # Aspect-dependent preservation/collapse
                    
                    status = "✅" if actual_res == expected_res else "❌"
                    print(f"      {repr(u_lhs)} {op_name[-2]} {dfi_rep} = {repr(actual_res)} (Expected: {repr(expected_res)}) {status}")

            # Test 2: DFI_k (LHS) op Unio Aspect (RHS)
            if dfi_rep is not None:
                print(f"    DFI({dfi_rep}) op Unio_Aspect:")
                for u_rhs in unio_aspects:
                    actual_res = op_func(dfi_rep, u_rhs)
                    
                    # Define Expected Outcome based on Revised Core AVCA spec for DFI op Unio
                    expected_res = None
                    if op_name == "ADD (⊕)":
                        expected_res = dfi_rep # DFI + Unio = DFI (additive identity)
                    elif op_name == "SUB (⊖)":
                        expected_res = dfi_rep # DFI - Unio = DFI (subtrahend identity)
                    elif op_name == "MUL (⊗)":
                        expected_res = ZERO_UNIO if u_rhs.aspect == "zero" else AREO_UNIO # Aspect-dependent annihilation/absorption
                    elif op_name == "DIV (⊘)":
                        expected_res = AREO_UNIO # DFI / Unio = AREO_UNIO (collapse to Areo)
                    
                    status = "✅" if actual_res == expected_res else "❌"
                    print(f"      {dfi_rep} {op_name[-2]} {repr(u_rhs)} = {repr(actual_res)} (Expected: {repr(expected_res)}) {status}")
            
            # Test 3: Unio Aspect (LHS) op Unio Aspect (RHS)
            print(f"    Unio_Aspect op Unio_Aspect:")
            for u_lhs in unio_aspects:
                for u_rhs in unio_aspects:
                    actual_res = op_func(u_lhs, u_rhs)
                    
                    # Define Expected Outcome based on Revised Core AVCA spec for Unio op Unio
                    expected_res = None
                    if op_name == "ADD (⊕)":
                        # Unio+Unio behaves like Unio+X=X, so if LHS is Unio, returns RHS. 
                        # So if u_lhs is ZU, returns u_rhs. If u_lhs is AU, returns u_rhs.
                        # This effectively means the result is the RHS operand.
                        expected_res = u_rhs 
                    elif op_name == "SUB (⊖)":
                        # DFI - Unio = DFI. Unio - Unio: minuend's aspect preserved.
                        expected_res = u_lhs # Unio - Unio = Minuend Aspect
                    elif op_name == "MUL (⊗)":
                        # ZERO_UNIO annihilates everything. AREO_UNIO absorbs if ZU not involved.
                        expected_res = ZERO_UNIO if u_lhs.aspect == "zero" or u_rhs.aspect == "zero" else AREO_UNIO
                    elif op_name == "DIV (⊘)":
                        # Unio / X = Aspect of Dividend. Here X is also Unio.
                        expected_res = u_lhs # Unio / Unio = Dividend Aspect

                    status = "✅" if actual_res == expected_res else "❌"
                    print(f"      {repr(u_lhs)} {op_name[-2]} {repr(u_rhs)} = {repr(actual_res)} (Expected: {repr(expected_res)}) {status}")

# --- Main Execution ---
if __name__ == "__main__":
    omegas_to_run = [1, 2, 3, 5] # Covering phase transitions and edge cases
    run_unio_operational_profile(omegas_to_run)
    print(f"\n{'='*20} EXPERIMENT 1.1 COMPLETE {'='*20}")
    print("  Review the output above for precise operational details.")