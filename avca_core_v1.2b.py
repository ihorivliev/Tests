# avca_core_v1.2b.py
# Canonical Python Specification for Core AVCA-Ω v1.2 Variant B
# This code forms the axiomatic basis of the algebra.

from typing import Literal, Union, Any # Union for AVCVal, Any for broader type hints if needed

# --- Global Omega Parameter ---
Omega: int = 0 # Must be set by set_avca_omega before operations

# --- Unio Class Definition ---
class Unio:
    """
    Represents the unified Unio pole in AVCA-Ω, embodying conceptual Zero 
    and Areo aspects. All Unio instances are algebraically equivalent, 
    meaning they represent the single Unio pole element.
   
    """
    __slots__ = ("aspect",) # Memory optimization

    def __init__(self, aspect: Literal["zero", "areo"]):
        """
        Initializes a Unio object with a specific conceptual aspect.
       
        :param aspect: Must be the string "zero" or "areo".
        :raises ValueError: If aspect is not "zero" or "areo".
        """
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect

    def __eq__(self, other: object) -> bool:
        """
        Defines algebraic equivalence: all Unio instances are considered equal
        if the 'other' object is also an instance of Unio, regardless of aspect.
       
        """
        return isinstance(other, Unio)

    def __hash__(self) -> int:
        """
        Ensures all Unio instances hash to the same value, consistent with
        their algebraic equivalence. This allows them to be used correctly
        in hash-based collections like sets or dictionary keys.
       
        """
        # All Unio objects represent the same algebraic element, so they should hash identically.
        # Hashing based on the class type ensures this.
        return hash(type(self)) 

    def __repr__(self) -> str:
        """
        Provides an unambiguous string representation of the Unio object,
        clearly indicating its aspect.
       
        """
        return f"Unio('{self.aspect}')"

# --- Canonical Unio Instances ---
ZERO_UNIO = Unio("zero")  # Represents Unio with its conceptual Zero-State aspect.
                          # Typically associated with additive identity characteristics.
AREO_UNIO = Unio("areo")  # Represents Unio with its conceptual Areo-State (saturation) aspect.
                          # Typically the result of DFI boundary breaches.

# --- Type Alias for AVCA Values ---
AVCVal = Union[int, Unio] # An AVCA Value is either a DFI integer or a Unio object.

# --- Helper for setting Omega for testing and use ---
def set_avca_omega(omega_value: int):
    """
    Sets the global Omega parameter for AVCA operations.
    Omega must be an integer >= 1.
   
    """
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    Omega = omega_value

# --- Domain Enforcement and Input Validation ---
def _check_val(x: AVCVal, current_omega: int):
    """
    Validates if x is a proper element of S_Ω for the given current_omega.
    This function is called at the beginning of each AVCA operation.
   
    DFI elements are integers from 1 to current_omega-1.
    Unio instances are always valid members of S_Ω.
    Raises TypeError for invalid types or ValueError for out-of-range DFI or invalid Omega.
    """
    if not isinstance(current_omega, int) or current_omega < 1: #
        raise ValueError(f"Omega parameter must be an integer >= 1. Got: {current_omega!r}")

    if isinstance(x, Unio): #
        return  # Unio objects are always valid elements of S_Omega.

    if not isinstance(x, int): #
        raise TypeError(f"Invalid AVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")

    # Integer checks for DFI eligibility
    if current_omega == 1: #
        # If Omega is 1, the DFI is empty. No integers are allowed as DFI elements.
        # This check ensures 'isinstance(x,int)' for Omega=1 raises error.
        raise ValueError(f"Invalid DFI Value for Omega=1: {x}. DFI is empty when Omega=1.")
    
    # If Omega > 1, DFI elements must be in the range [1, Omega-1]
    # x is guaranteed to be an int here.
    if not (1 <= x < current_omega): #
        raise ValueError(f"Invalid DFI Value: {x}. For Omega={current_omega}, DFI integers must be in range [1, {current_omega - 1}].")

# --- AVCA Operations (v1.2b logic) ---

def avc_add(a: AVCVal, b: AVCVal) -> AVCVal: # ⊕_v1.1 logic
    """
    ⊕ : S_Ω × S_Ω → S_Ω (Cyclical Addition - v1.1 Refinement Logic)
    Axiomatic definition as per Part I, Chapter 2, Section 2.1.
    - Unio (any aspect object) is the universal additive identity.
    - DFI + DFI: Standard sum if < Ω; result is AREO_UNIO if sum ≥ Ω (v1.1 refinement).
    """
    global Omega
    if Omega == 0: 
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    _check_val(a, Omega)
    _check_val(b, Omega)

    if isinstance(a, Unio):
        return b  # Unio + X -> X (Rule 2.1.1)
    if isinstance(b, Unio):
        return a  # X + Unio -> X (Rule 2.1.1)

    # Both a and b are DFI integers at this point
    standard_sum = a + b # type: ignore # Type checker knows a, b are ints now
    if standard_sum < Omega:
        return standard_sum  # Result is DFI (Rule 2.1.2)
    else:
        return AREO_UNIO     # DFI additive overflow yields AREO_UNIO (Rule 2.1.2, v1.1 refinement)

def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal: # ⊖_v1.0 logic
    """
    ⊖ : S_Ω × S_Ω → S_Ω (Asymmetric Subtraction - Original v1.0 Logic)
    Axiomatic definition as per Part I, Chapter 2, Section 2.2.
    - Unio (any aspect object) as subtrahend acts as identity (X - Unio -> X).
    - Unio (any aspect object) as minuend with DFI subtrahend (Unio - DFI_k -> AREO_UNIO).
    - DFI - DFI: Standard difference if > 0; result is AREO_UNIO if difference ≤ 0.
    """
    global Omega
    if Omega == 0: 
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    _check_val(a, Omega)
    _check_val(b, Omega)

    if isinstance(b, Unio): # Rule 1: X ⊖ U → X (Rule 2.2.1)
        return a
    
    # b is DFI at this point
    if isinstance(a, Unio): # Rule 2: U ⊖ DFI_k → AREO_UNIO (Rule 2.2.2)
        return AREO_UNIO
    
    # Both a and b are DFI integers at this point (Rule 3)
    # Type checker knows a, b are ints now
    if a > b: # type: ignore 
        return a - b # type: ignore      
    else: # a <= b (underflow or cancellation)
        return AREO_UNIO     # DFI subtractive underflow/cancellation yields AREO_UNIO

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal: # ⊗_v1.2 logic
    """
    ⊗ : S_Ω × S_Ω → S_Ω (Symmetric Aspect-Aware Multiplication - v1.2 Refinement Logic)
    Axiomatic definition as per Part I, Chapter 2, Section 2.3.
    - Unio-involved: AREO_UNIO if any Unio operand is Areo-aspected, else ZERO_UNIO (v1.2 Symmetric Rule).
    - DFI * DFI: Standard product if valid DFI (1 <= p < Ω); else AREO_UNIO (overflow).
    """
    global Omega
    if Omega == 0: 
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    _check_val(a, Omega)
    _check_val(b, Omega)

    a_is_unio = isinstance(a, Unio)
    b_is_unio = isinstance(b, Unio)

    if a_is_unio or b_is_unio: # Rule 1: At least one operand is Unio (Rule 2.3.1)
        # v1.2 Symmetric Rule: AREO_UNIO if any Unio factor is Areo-aspected, otherwise ZERO_UNIO.
        # Need to access .aspect, so ensure type is Unio before attribute access
        is_any_areo_aspected = (a_is_unio and a.aspect == "areo") or \
                               (b_is_unio and b.aspect == "areo") # type: ignore
        if is_any_areo_aspected:
            return AREO_UNIO
        else: # All Unio operands involved must be Zero-aspected (or one is ZU, other DFI)
            return ZERO_UNIO
    else: # Rule 2: Both a and b are DFI integers (Rule 2.3.2)
        # Types are guaranteed to be int by here
        standard_product = a * b # type: ignore
        # DFI product must be > 0 because DFI elements are >= 1.
        if 1 <= standard_product < Omega:
            return standard_product # Result is DFI
        else: # Multiplicative overflow (product >= Omega) or product is 0 (not possible for DFI*DFI)
            return AREO_UNIO

def avc_div(a: AVCVal, b: AVCVal) -> AVCVal: # ⊘_v1.2B logic
    """
    ⊘ : S_Ω × S_Ω → S_Ω (Symmetric Aspect-Aware Division - v1.2 Variant B Refinement Logic)
    Axiomatic definition as per Part I, Chapter 2, Section 2.4.
    - Rule B1: Divisor b is Unio (any aspect object) -> AREO_UNIO.
    - Rule B2: Dividend a is Unio (any aspect) AND Divisor b is DFI -> Preserves Dividend's Unio aspect.
    - Rule B3: DFI / DFI -> Standard quotient if exact and valid DFI; else AREO_UNIO.
    """
    global Omega
    if Omega == 0: 
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    # _check_val for 'b' will ensure DFI 'b' is not 0, for Omega > 1.
    # For Omega = 1, DFI is empty, so 'b' can only be Unio.
    _check_val(a, Omega) 
    _check_val(b, Omega) 

    # Rule B1: Divisor b is Unio (any aspect object) (Rule 2.4.1)
    if isinstance(b, Unio):
        return AREO_UNIO

    # At this point, b must be DFI (guaranteed by _check_val if Omega > 1;
    # if Omega = 1, this part is unreachable as b must have been Unio).
    
    # Rule B2: Dividend a is Unio (any aspect object) AND Divisor b is DFI (Rule 2.4.2)
    if isinstance(a, Unio):
        if a.aspect == "zero": # type: ignore
            return ZERO_UNIO # Preserves "0 / k = 0" (ZERO_UNIO / DFI_k -> ZERO_UNIO)
        else: # a.aspect == "areo"
            return AREO_UNIO # AREO_UNIO / DFI_k -> AREO_UNIO
    
    # Rule B3: Both a and b are DFI integers (Rule 2.4.3)
    # At this point, a and b are guaranteed to be DFI integers by _check_val and preceding checks.
    # b_val is also guaranteed to be >= 1 by _check_val (for Omega > 1).
    
    # Explicit type assertion for type checker after isinstance checks
    a_val: int = a # type: ignore 
    b_val: int = b # type: ignore

    quotient, remainder = divmod(a_val, b_val)

    if remainder == 0 and (1 <= quotient < Omega):
        return quotient # Result is a valid DFI element
    else:
        # Non-exact division, or quotient is 0 (e.g. 1 // 2), or quotient >= Omega
        return AREO_UNIO
        
# --- Example Usage Block (Illustrative, from Appendix A of AVCA Core DraftV3) ---
if __name__ == "__main__": #
    print("--- AVCA-Ω v1.2b Core Operations: Example Usage ---")
    
    print("\nSetting Omega = 3 (DFI will be {1, 2})")
    set_avca_omega(3)
    
    u_z = ZERO_UNIO
    u_a = AREO_UNIO
    dfi1 = 1
    dfi2 = 2

    print(f"\n--- avc_add (⊕_v1.1) examples for Omega={Omega} ---")
    print(f"  {u_z!r} ⊕ {dfi1!r} = {avc_add(u_z, dfi1)!r}")    # Expected: 1
    print(f"  {dfi1!r} ⊕ {u_a!r} = {avc_add(dfi1, u_a)!r}")    # Expected: 1
    print(f"  {dfi1!r} ⊕ {dfi1!r} = {avc_add(dfi1, dfi1)!r}")  # Expected: 2
    print(f"  {dfi1!r} ⊕ {dfi2!r} = {avc_add(dfi1, dfi2)!r}")  # Expected: AREO_UNIO (1+2=3 >= Omega=3)
    print(f"  {dfi2!r} ⊕ {dfi2!r} = {avc_add(dfi2, dfi2)!r}")  # Expected: AREO_UNIO (2+2=4 >= Omega=3)

    print(f"\n--- avc_sub (⊖_v1.0) examples for Omega={Omega} ---")
    print(f"  {dfi2!r} ⊖ {dfi1!r} = {avc_sub(dfi2, dfi1)!r}")    # Expected: 1
    print(f"  {dfi1!r} ⊖ {dfi2!r} = {avc_sub(dfi1, dfi2)!r}")    # Expected: AREO_UNIO (1-2 < 0)
    print(f"  {dfi1!r} ⊖ {u_z!r} = {avc_sub(dfi1, u_z)!r}")    # Expected: 1
    print(f"  {u_a!r} ⊖ {dfi1!r} = {avc_sub(u_a, dfi1)!r}")    # Expected: AREO_UNIO

    print(f"\n--- avc_mul (⊗_v1.2) examples for Omega={Omega} ---")
    print(f"  {u_z!r} ⊗ {dfi2!r} = {avc_mul(u_z, dfi2)!r}")    # Expected: ZERO_UNIO
    print(f"  {u_a!r} ⊗ {dfi2!r} = {avc_mul(u_a, dfi2)!r}")    # Expected: AREO_UNIO
    print(f"  {u_z!r} ⊗ {u_a!r} = {avc_mul(u_z, u_a)!r}")    # Expected: AREO_UNIO (Areo dominates)
    print(f"  {dfi1!r} ⊗ {dfi2!r} = {avc_mul(dfi1, dfi2)!r}")  # Expected: 2 (1*2=2 < Omega=3)
    print(f"  {dfi2!r} ⊗ {dfi2!r} = {avc_mul(dfi2, dfi2)!r}")  # Expected: AREO_UNIO (2*2=4 >= Omega=3)

    print(f"\n--- avc_div (⊘_v1.2B) examples for Omega={Omega} ---")
    print(f"  {dfi2!r} ⊘ {dfi1!r} = {avc_div(dfi2, dfi1)!r}")    # Expected: 2
    print(f"  {dfi1!r} ⊘ {dfi2!r} = {avc_div(dfi1, dfi2)!r}")    # Expected: AREO_UNIO (q=0)
    print(f"  {u_z!r} ⊘ {dfi2!r} = {avc_div(u_z, dfi2)!r}")    # Expected: ZERO_UNIO (preserves ZU aspect)
    print(f"  {u_a!r} ⊘ {dfi1!r} = {avc_div(u_a, dfi1)!r}")    # Expected: AREO_UNIO (preserves AU aspect)
    print(f"  {dfi2!r} ⊘ {u_z!r} = {avc_div(dfi2, u_z)!r}")    # Expected: AREO_UNIO (divisor is Unio)
    print(f"  {u_a!r} ⊘ {u_z!r} = {avc_div(u_a, u_z)!r}")    # Expected: AREO_UNIO (divisor is Unio)

    print("\nSetting Omega = 1 (DFI is empty)")
    set_avca_omega(1)
    print(f"  {u_z!r} ⊕ {u_a!r} = {avc_add(u_z, u_a)!r}") # Expected: AREO_UNIO
    try:
        print(f"  Attempting {u_z!r} ⊕ {dfi1!r} for Omega=1: ")
        avc_add(u_z, dfi1) # dfi1 (value 1) is invalid for Omega=1
    except ValueError as e:
        print(f"    Correctly raised ValueError: {e}")

    print("\n--- Example Usage Completed ---")