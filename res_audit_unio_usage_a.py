import re

# --- Content of avca_core_v1_2b.py embedded as a string ---
AVCA_CORE_V1_2B_CODE = """
# avca_core_v1.2b.py
# Canonical Python Specification for Core AVCA-Ω v1.2 Variant B
# This code forms the axiomatic basis of the algebra.

from typing import Literal, Union, Any # Union for AVCVal, Any for broader type hints if needed

# --- Global Omega Parameter ---
Omega: int = 0 # Must be set by set_avca_omega before operations

# --- Unio Class Definition ---
class Unio:
    \"\"\"
    Represents the unified Unio pole in AVCA-Ω, embodying conceptual Zero 
    and Areo aspects. All Unio instances are algebraically equivalent, 
    meaning they represent the single Unio pole element.
   
    \"\"\"
    __slots__ = ("aspect",) # Memory optimization

    def __init__(self, aspect: Literal["zero", "areo"]):
        \"\"\"
        Initializes a Unio object with a specific conceptual aspect.
       
        :param aspect: Must be the string "zero" or "areo".
        :raises ValueError: If aspect is not "zero" or "areo".
        \"\"\"
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect

    def __eq__(self, other: object) -> bool:
        \"\"\"
        Defines algebraic equivalence: all Unio instances are considered equal
        if the 'other' object is also an instance of Unio, regardless of aspect.
       
        \"\"\"
        return isinstance(other, Unio)

    def __hash__(self) -> int:
        \"\"\"
        Ensures all Unio instances hash to the same value, consistent with
        their algebraic equivalence. This allows them to be used correctly
        in hash-based collections like sets or dictionary keys.
       
        \"\"\"
        # All Unio objects represent the same algebraic element, so they should hash identically.
        # Hashing based on the class type ensures this.
        return hash(type(self)) 

    def __repr__(self) -> str:
        \"\"\"
        Provides an unambiguous string representation of the Unio object,
        clearly indicating its aspect.
       
        \"\"\"
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
    \"\"\"
    Sets the global Omega parameter for AVCA operations.
    Omega must be an integer >= 1.
   
    \"\"\"
    global Omega
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    Omega = omega_value

# --- Domain Enforcement and Input Validation ---
def _check_val(x: AVCVal, current_omega: int):
    \"\"\"
    Validates if x is a proper element of S_Ω for the given current_omega.
    This function is called at the beginning of each AVCA operation.
   
    DFI elements are integers from 1 to current_omega-1.
    Unio instances are always valid members of S_Ω.
    Raises TypeError for invalid types or ValueError for out-of-range DFI or invalid Omega.
    \"\"\"
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

def avc_add(a: AVCVal, b: AVCVal) -> AVCVal:  # ⊕_v1.1 logic 
    \"\"\"
    ⊕ : S_Ω × S_Ω → S_Ω (Cyclical Addition - v1.1 Refinement Logic)
    Axiomatic definition as per Part I, Chapter 2, Section 2.1.
    - Unio (any aspect object) is the universal additive identity.
    - DFI + DFI: Standard sum if < Ω; result is AREO_UNIO if sum ≥ Ω (v1.1 refinement).
    \"\"\"
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

def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal:  # ⊖_v1.0 logic 
    \"\"\"
    ⊖ : S_Ω × S_Ω → S_Ω (Asymmetric Subtraction - Original v1.0 Logic)
    Axiomatic definition as per Part I, Chapter 2, Section 2.2.
    - Unio (any aspect object) as subtrahend acts as identity (X - Unio -> X).
    - Unio (any aspect object) as minuend with DFI subtrahend (Unio - DFI_k -> AREO_UNIO).
    - DFI - DFI: Standard difference if > 0; result is AREO_UNIO if difference ≤ 0.
    \"\"\"
    global Omega
    if Omega == 0: 
        raise ValueError("Global Omega parameter not set. Call set_avca_omega(value) first.")
    _check_val(a, Omega)
    _check_val(b, Omega)

    if isinstance(b, Unio):  # Rule 1: X ⊖ U → X (Rule 2.2.1) 
        return a
    
    # b is DFI at this point
    if isinstance(a, Unio):  # Rule 2: U ⊖ DFI_k → AREO_UNIO (Rule 2.2.2) 
        return AREO_UNIO
    
    # Both a and b are DFI integers at this point (Rule 3)
    # Type checker knows a, b are ints now
    if a > b: # type: ignore 
        return a - b # type: ignore      
    else: # a <= b (underflow or cancellation)
        return AREO_UNIO     # DFI subtractive underflow/cancellation yields AREO_UNIO

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal:  # ⊗_v1.2 logic 
    \"\"\"
    ⊗ : S_Ω × S_Ω → S_Ω (Symmetric Aspect-Aware Multiplication - v1.2 Refinement Logic)
    Axiomatic definition as per Part I, Chapter 2, Section 2.3.
    - Unio-involved: AREO_UNIO if any Unio operand is Areo-aspected, else ZERO_UNIO (v1.2 Symmetric Rule).
    - DFI * DFI: Standard product if valid DFI (1 <= p < Ω); else AREO_UNIO (overflow).
    \"\"\"
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
        a_aspect_is_areo = a_is_unio and a.aspect == "areo" # type: ignore
        b_aspect_is_areo = b_is_unio and b.aspect == "areo" # type: ignore
        is_any_areo_aspected = a_aspect_is_areo or b_aspect_is_areo
                               
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

def avc_div(a: AVCVal, b: AVCVal) -> AVCVal:  # ⊘_v1.2B logic 
    \"\"\"
    ⊘ : S_Ω × S_Ω → S_Ω (Symmetric Aspect-Aware Division - v1.2 Variant B Refinement Logic)
    Axiomatic definition as per Part I, Chapter 2, Section 2.4.
    - Rule B1: Divisor b is Unio (any aspect object) -> AREO_UNIO.
    - Rule B2: Dividend a is Unio (any aspect) AND Divisor b is DFI -> Preserves Dividend's Unio aspect.
    - Rule B3: DFI / DFI -> Standard quotient if exact and valid DFI; else AREO_UNIO.
    \"\"\"
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
        
# --- Example Usage Block (from Appendix A of AVCA Core DraftV3) ---
# This block is commented out as it's part of the code being audited, not the audit tool itself.
# if __name__ == "__main__": 
# ...
"""

# --- Audit Script Logic ---

PATTERNS = {
    "is_ZERO_UNIO": re.compile(r"\bis\s+ZERO_UNIO\b"),
    "is_AREO_UNIO": re.compile(r"\bis\s+AREO_UNIO\b"),
    "equals_ZERO_UNIO": re.compile(r"==\s+ZERO_UNIO\b"),
    "equals_AREO_UNIO": re.compile(r"==\s+AREO_UNIO\b"),
    "direct_aspect_access": re.compile(r"\.aspect\b"),
}

LEGITIMATE_ASPECT_CONTEXT_KEYWORDS = [
    "Unio(" ,
    "def __init__",
    "def __repr__",
    "avc_mul", 
    "avc_div", 
    "ZERO_UNIO =",
    "AREO_UNIO =",
]

V1_2B_ASPECT_AWARE_FUNCTIONS = ["avc_mul", "avc_div"]

def audit_embedded_code(code_string: str):
    """
    Audits the embedded AVCA Python code string for specific Unio object
    identity checks and direct .aspect access.
    """
    print(f"--- Auditing Embedded AVCA Core v1.2b Code ---")
    found_issues = {}
    suspicious_aspect_access = []
    
    lines = code_string.strip().splitlines()
    current_function_is_aspect_aware = False

    for i, line in enumerate(lines):
        line_num = i + 1
        stripped_line = line.strip()

        if stripped_line.startswith("def "):
            current_function_is_aspect_aware = False
            for func_name in V1_2B_ASPECT_AWARE_FUNCTIONS:
                if f"def {func_name}(" in stripped_line or f"def {func_name} (" in stripped_line : # handle space after func name
                    current_function_is_aspect_aware = True
                    break
        
        for pattern_name, regex in PATTERNS.items():
            for match in regex.finditer(line):
                issue_key = f"L{line_num}: '{pattern_name}'"
                if issue_key not in found_issues:
                    found_issues[issue_key] = []
                
                context = line.strip()
                
                if pattern_name == "direct_aspect_access":
                    is_legitimate_context = current_function_is_aspect_aware or \
                                            any(keyword in line for keyword in LEGITIMATE_ASPECT_CONTEXT_KEYWORDS)
                    
                    if is_legitimate_context:
                        detail = (f"Found '{match.group(0)}' at col {match.start()}. "
                                  f"Context: \"{context}\" (Likely legitimate within "
                                  f"{'aspect-aware op' if current_function_is_aspect_aware else 'definition/repr'})")
                    else:
                        detail = (f"Found '{match.group(0)}' at col {match.start()}. "
                                  f"Context: \"{context}\" (Potentially suspicious "
                                  f"if differentiating behavior beyond algebraic equivalence "
                                  f"outside defined aspect-aware ops)")
                        suspicious_aspect_access.append(f"L{line_num}: {context}")
                    found_issues[issue_key].append(detail)
                else: # Object identity checks
                    # Check if it's part of the Unio.__eq__ method definition, which is fine
                    is_in_eq_method_context = False
                    if "def __eq__(" in stripped_line and pattern_name.startswith("equals_"):
                        # This is too simple, need to check if we are *inside* __eq__
                        # For this basic audit, we'll assume direct '==' with canonicals
                        # outside __init__ of Unio itself is worth noting.
                        # A more robust check would parse the AST or track function context.
                        pass # For now, let's list all direct comparisons

                    detail = (f"Found '{match.group(0)}' at col {match.start()}. "
                              f"Context: \"{context}\" (Suspicious: Potential object identity check "
                              f"instead of algebraic equivalence if used for behavior differentiation)")
                    found_issues[issue_key].append(detail)
                    suspicious_aspect_access.append(f"L{line_num}: {context} (Pattern: {pattern_name})")

    if found_issues:
        print("\n[Found Patterns - Details]:")
        for issue_key, details in sorted(found_issues.items()):
            print(f"  {issue_key}:")
            for detail_text in details:
                print(f"    - {detail_text}")
    else:
        print("\nNo specified patterns found in the embedded code.")

    if suspicious_aspect_access:
        print("\n\n[Summary of Potentially Suspicious Lines/Accesses]:")
        print("(These lines use object identity checks like 'is ZERO_UNIO' or '.aspect' access outside")
        print(" of the explicitly aspect-aware v1.2b operations avc_mul/avc_div, or Unio definitions/repr.)")
        print("Review these to ensure they don't break algebraic equivalence principles behaviorally.")
        for item in sorted(list(set(suspicious_aspect_access))):
            print(f"  - {item}")
    else:
        print("\nNo potentially suspicious object identity checks or external .aspect accesses found.")
        print("(Note: '.aspect' access *within* the definitions of avc_mul and avc_div is expected and part of their v1.2b aspect-handling logic.)")

    print(f"\n--- Audit Complete for Embedded Code ---")

if __name__ == "__main__":
    audit_embedded_code(AVCA_CORE_V1_2B_CODE)