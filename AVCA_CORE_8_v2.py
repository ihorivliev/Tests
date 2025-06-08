import itertools
from typing import Union, List, Any, Tuple, Callable, Dict

# --- Core AVCA Specification (from Revised Core AVCA manuscript) ---
# Global Omega, needs to be set by the test runner for each iteration
Omega: int = 0

class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: str):
        # "zero" or "areo"
        assert aspect in ("zero","areo"), f"Unio aspect must be 'zero' or 'areo', got {aspect}"
        self.aspect = aspect
    def __eq__(self, other):
        # All Unio objects are identified algebraically
        return isinstance(other, Unio)
    def __hash__(self):
        # Make Unio objects hashable. All Unio hash to the same value.
        return hash("UNIO_ALGEBRAIC_ELEMENT") # Consistent hash for all Unio objects
    def __repr__(self):
        return f"Unio('{self.aspect}')" # Consistent repr

ZERO_UNIO = Unio("zero")  # additive-identity / additive-overflow aspect
AREO_UNIO = Unio("areo")  # saturation / non-DFI-result aspect

AVCVal = Union[int, Unio]

def _check_val(x: AVCVal, omega_val: int): # Pass Omega explicitly for clarity in function
    """Allow only Unio or ints 1…omega_val-1."""
    if omega_val == 0: # Changed from Omega to omega_val
        raise ValueError("Omega parameter must be set (to >= 1) before _check_val can be used.")
    if isinstance(x, Unio):
        return
    if not isinstance(x, int):
        raise TypeError(f"AVC value must be an integer or Unio instance, got {type(x)} for value {x!r}")
    
    if omega_val == 1: # If Omega is 1, DFI is empty. No integers are allowed.
        raise ValueError(f"DFI integers are not permitted when Omega=1, got integer {x}")
    # If Omega > 1, DFI integers must be in the range [1, omega_val-1)
    if not (1 <= x < omega_val):
        raise ValueError(f"DFI integer value {x} is out of range [1...{omega_val-1}] for Omega={omega_val}")

# --- Four total operations (from Revised Core AVCA spec) ---

def avc_add(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega
    _check_val(a, Omega); _check_val(b, Omega)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    # Both a, b are DFI ints
    s = a + b
    return s if s < Omega else ZERO_UNIO

def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega
    _check_val(a, Omega); _check_val(b, Omega)
    if isinstance(b, Unio): return a # X - Unio = X
    if isinstance(a, Unio): return AREO_UNIO # Unio - DFI = AREO_UNIO (covers ZU-DFI and AU-DFI)
    # Both a, b are DFI ints
    return (a - b) if a > b else AREO_UNIO # DFI - DFI: underflow/eq to AREO_UNIO

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega
    _check_val(a, Omega); _check_val(b, Omega)
    if isinstance(a, Unio):
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    if isinstance(b, Unio): # a must be DFI here
        return ZERO_UNIO if b.aspect=="zero" else AREO_UNIO
    # Both a, b are DFI ints
    p = a * b
    # DFI elements are >= 1, so p >= 1.
    # We only need to check if p < Omega for it to be a valid DFI.
    return p if (1 <= p < Omega) else AREO_UNIO # DFI*DFI: overflow to AREO_UNIO

def avc_div(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega
    _check_val(a, Omega); _check_val(b, Omega) # _check_val ensures DFI b is not 0 if Omega > 1
    
    if isinstance(a, Unio): # Dividend is Unio
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    if isinstance(b, Unio): # Divisor is Unio (and a is DFI here)
        return AREO_UNIO
        
    # Both a, b are DFI ints. b is guaranteed to be >= 1.
    # Standard Python divmod will handle division by non-zero b.
    quotient, remainder = divmod(a, b)
    
    if remainder == 0 and (1 <= quotient < Omega):
        # Clean division resulting in a valid DFI value
        return quotient
    else:
        # Non-exact division, or quotient is not a valid DFI (e.g., 0, or >= Omega)
        return AREO_UNIO

# --- Experiment 1.1: Unio's Operational Profile ---

OPERATIONS: Dict[str, Callable[[AVCVal, AVCVal], AVCVal]] = {
    "⊕ (add)": avc_add,
    "⊖ (sub)": avc_sub,
    "⊗ (mul)": avc_mul,
    "⊘ (div)": avc_div,
}

def run_unio_operational_profile(omega_val: int):
    global Omega
    Omega = omega_val
    
    print(f"\n\n{'='*20} Experiment 1.1: Unio's Operational Profile (Omega={Omega}) {'='*20}")

    pole_operands: List[AVCVal] = [ZERO_UNIO, AREO_UNIO]
    dfi_operands: List[AVCVal] = []

    if Omega == 1:
        print("DFI is empty for Omega=1. Testing Pole-Pole interactions only.")
    elif Omega == 2:
        dfi_operands = [1]
        print(f"DFI for Omega=2: {dfi_operands}")
    elif Omega > 2:
        # Select representative DFI values: 1 (smallest), Omega-1 (largest), maybe a middle one if Omega is large enough
        dfi_operands.append(1)
        if Omega - 1 != 1 : # Avoid duplicate if Omega=2 (already handled)
             dfi_operands.append(Omega - 1)
        if Omega > 3 and (Omega // 2) not in dfi_operands and (Omega // 2) != 0 : # Add a middle DFI if distinct
            dfi_operands.append(Omega // 2)
        dfi_operands.sort() # Ensure order for readability
        print(f"Representative DFI for Omega={Omega}: {dfi_operands}")
    
    all_operands = pole_operands + dfi_operands
    if Omega == 1: # For Omega=1, ZERO_UNIO and AREO_UNIO are the only distinct Python objects for input
        all_operands = pole_operands # DFI list is empty

    # Max length of operand representation for formatting
    max_op_len = max(len(repr(op)) for op in all_operands) if all_operands else 10

    for op_name, op_func in OPERATIONS.items():
        print(f"\n--- Operation: {op_name} ---")
        # Header
        header_parts = [f"{'':<{max_op_len}}"] + [f"{repr(b):>{max_op_len}}" for b in all_operands]
        print(" | ".join(header_parts))
        print("-" * len(" | ".join(header_parts)))

        for a in all_operands:
            row_parts = [f"{repr(a):<{max_op_len}}"]
            for b in all_operands:
                try:
                    # Ensure _check_val is implicitly called if we construct DFI on the fly
                    # But since we pull from S_elements which should be pre-validated by generate_s_test,
                    # direct calls are okay. For this focused test, we use explicit valid operands.
                    res = op_func(a, b)
                    row_parts.append(f"{repr(res):>{max_op_len}}")
                except Exception as e:
                    row_parts.append(f"{'ERROR':>{max_op_len}}") # Should not happen with pre-validated inputs
            print(" | ".join(row_parts))

if __name__ == "__main__":
    omegas_to_test = [1, 2, 3, 5] 
    # You can add more Omega values if needed, e.g., 4, 7 for more DFI interactions

    for current_omega_val in omegas_to_test:
        run_unio_operational_profile(omega_val=current_omega_val)

    print(f"\n\n{'='*20} Experiment 1.1 Concluded {'='*20}")
    print("Key Observations from Unio's Operational Profile:")
    print("1. For ADDITION (⊕):")
    print("   - Unio (ZERO_UNIO or AREO_UNIO) + X -> X (Unio acts as perfect additive identity).")
    print("   - X + Unio (ZERO_UNIO or AREO_UNIO) -> X.")
    print("   - DFI + DFI (overflow) -> ZERO_UNIO.")
    print("2. For SUBTRACTION (⊖):")
    print("   - X - Unio (ZERO_UNIO or AREO_UNIO) -> X (Unio as identity when subtrahend).")
    print("   - Unio (ZERO_UNIO or AREO_UNIO) - DFI_k -> AREO_UNIO ('Stuck-at-Areo' when Unio is minuend).")
    print("   - DFI_i - DFI_j (underflow/cancellation) -> AREO_UNIO.")
    print("3. For MULTIPLICATION (⊗):")
    print("   - ZERO_UNIO * X -> ZERO_UNIO (Annihilator).")
    print("   - X * ZERO_UNIO -> ZERO_UNIO.")
    print("   - AREO_UNIO * DFI_k -> AREO_UNIO (Absorber).")
    print("   - DFI_k * AREO_UNIO -> AREO_UNIO.")
    print("   - AREO_UNIO * AREO_UNIO -> AREO_UNIO (Idempotent absorber).")
    print("   - DFI * DFI (overflow) -> AREO_UNIO.")
    print("4. For DIVISION (⊘):")
    print("   - ZERO_UNIO / X -> ZERO_UNIO (Annihilator-like for dividend).")
    print("   - AREO_UNIO / X -> AREO_UNIO (Absorber-like for dividend).")
    print("   - DFI_k / Unio (ZERO_UNIO or AREO_UNIO) -> AREO_UNIO (Collapse/Saturation when Unio is divisor).")
    print("   - DFI / DFI (non-exact or out-of-range quotient) -> AREO_UNIO.")
    print("\nThis profile highlights the operational asymmetry of Unio across operations.")