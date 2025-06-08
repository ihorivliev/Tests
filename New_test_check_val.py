# test_check_val.py
# Purpose: To exhaustively test the _check_val domain enforcement function
# from AVCA Core v1.2b for various Omega values and inputs.

from typing import Literal, Union, Any # Added Any for broader invalid type testing

# --- Unio Class Definition (Copied directly from Appendix A of AVCA Core DraftV3) ---
class Unio:
    """
    Represents the unified Unio pole, embodying conceptual Zero and Areo aspects.
    All Unio instances are algebraically equivalent.
    """
    __slots__ = ("aspect",)

    def __init__(self, aspect: Literal["zero", "areo"]):
        """
        Initializes a Unio object with a specific aspect.
        :param aspect: Must be "zero" or "areo".
        """
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio aspect must be 'zero' or 'areo'.")
        self.aspect = aspect

    def __eq__(self, other: object) -> bool:
        """
        Defines algebraic equivalence: all Unio instances are considered equal.
        """
        return isinstance(other, Unio)

    def __hash__(self) -> int:
        """
        Ensures all Unio instances hash to the same value, reflecting their
        algebraic equivalence.
        Important for use in sets or dictionary keys.
        """
        return hash(type(self)) # Hash based on the class type itself

    def __repr__(self) -> str:
        """
        Provides a string representation of the Unio object, including its aspect.
        """
        return f"Unio('{self.aspect}')"

# --- Canonical Unio Instances ---
ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")

# --- Type Alias for AVCA Values ---
AVCVal = Union[int, Unio]

# --- _check_val Function (Copied directly from Appendix A of AVCA Core DraftV3) ---
def _check_val(x: AVCVal, current_omega: int):
    """
    Validates if x is a proper element of S_Ω for the given current_omega.
    DFI elements are integers from 1 to Omega-1.
    Unio instances are always valid.
    Raises TypeError or ValueError for invalid inputs.
    """
    if not isinstance(current_omega, int) or current_omega < 1: #
        raise ValueError(f"Omega parameter must be an integer >= 1. Got: {current_omega}")

    if isinstance(x, Unio): #
        return  # Unio objects are always valid elements of S_Omega.

    if not isinstance(x, int): #
        raise TypeError(f"Invalid AVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")

    # Integer checks for DFI
    if current_omega == 1: #
        # If Omega is 1, the DFI is empty. No integers are allowed as DFI elements.
        raise ValueError(f"Invalid DFI Value for Omega=1: {x}. DFI is empty when Omega=1.")
    
    # If Omega > 1, DFI elements must be in the range [1, Omega-1]
    if not (1 <= x < current_omega): #
        raise ValueError(f"Invalid DFI Value: {x}. For Omega={current_omega}, DFI integers must be in range [1, {current_omega - 1}].")

# --- Test Runner ---
def run_tests():
    print("--- Starting _check_val Domain Enforcement Tests (AVCA Core v1.2b Logic) ---\n")
    
    test_configs = [
        {"omega": 1, "valid_dfi": [], "invalid_dfi_gte_omega": [1, 2], "invalid_dfi_lte_zero": [0, -1]},
        {"omega": 2, "valid_dfi": [1], "invalid_dfi_gte_omega": [2, 3], "invalid_dfi_lte_zero": [0, -1]},
        {"omega": 3, "valid_dfi": [1, 2], "invalid_dfi_gte_omega": [3, 4], "invalid_dfi_lte_zero": [0, -1]},
        {"omega": 5, "valid_dfi": [1, 2, 3, 4], "invalid_dfi_gte_omega": [5, 6], "invalid_dfi_lte_zero": [0, -1]},
    ]

    invalid_types = ["string", 3.14, [1,2], {"a":1}, None]
    valid_unio_inputs = [ZERO_UNIO, AREO_UNIO, Unio("zero"), Unio("areo")]
    invalid_omega_values = [0, -1, 0.5, "string_omega"]


    # Test 1: Invalid Omega values for _check_val itself
    print("Test 1: _check_val with invalid 'current_omega' values")
    for invalid_omega in invalid_omega_values:
        try:
            _check_val(ZERO_UNIO, invalid_omega) # type: ignore
            print(f"  FAIL: _check_val(ZERO_UNIO, {invalid_omega!r}) did not raise error.")
        except ValueError as e:
            if "Omega parameter must be an integer >= 1" in str(e):
                print(f"  PASS: _check_val(ZERO_UNIO, {invalid_omega!r}) correctly raised ValueError: {e}")
            else:
                print(f"  FAIL: _check_val(ZERO_UNIO, {invalid_omega!r}) raised ValueError, but wrong message: {e}")
        except TypeError as e: # For non-int omega
             if "Omega parameter must be an integer >= 1" in str(e) or "must be an integer" in str(e) or "int" in str(e).lower(): # Accomodate potential slight variations if type error occurs earlier
                print(f"  PASS: _check_val(ZERO_UNIO, {invalid_omega!r}) correctly indicated issue with Omega type/value: {e}")
             else:
                print(f"  FAIL: _check_val(ZERO_UNIO, {invalid_omega!r}) raised TypeError, but wrong message: {e}")

    print("-" * 60)

    for config in test_configs:
        omega = config["omega"]
        print(f"\n--- Testing with Omega = {omega} ---")

        # Test 2: Valid Unio inputs
        print("  Test 2: Valid Unio inputs")
        for unio_val in valid_unio_inputs:
            try:
                _check_val(unio_val, omega)
                print(f"    PASS: _check_val({unio_val!r}, {omega}) accepted valid Unio.")
            except Exception as e:
                print(f"    FAIL: _check_val({unio_val!r}, {omega}) raised unexpected error: {e}")
        
        # Test 3: Valid DFI inputs
        print("  Test 3: Valid DFI inputs")
        if not config["valid_dfi"]:
            print("    INFO: No valid DFI inputs to test for Omega=1.")
        for dfi_val in config["valid_dfi"]:
            try:
                _check_val(dfi_val, omega)
                print(f"    PASS: _check_val({dfi_val}, {omega}) accepted valid DFI.")
            except Exception as e:
                print(f"    FAIL: _check_val({dfi_val}, {omega}) raised unexpected error for valid DFI: {e}")

        # Test 4: Invalid DFI inputs (out of range)
        print("  Test 4: Invalid DFI inputs (out of range)")
        all_invalid_dfi = config["invalid_dfi_gte_omega"] + config["invalid_dfi_lte_zero"]
        for dfi_val in all_invalid_dfi:
            expected_msg_part = ""
            if omega == 1:
                expected_msg_part = "DFI is empty when Omega=1"
            else:
                expected_msg_part = f"DFI integers must be in range [1, {omega - 1}]"
            
            try:
                _check_val(dfi_val, omega)
                print(f"    FAIL: _check_val({dfi_val}, {omega}) accepted invalid DFI.")
            except ValueError as e:
                if expected_msg_part in str(e):
                    print(f"    PASS: _check_val({dfi_val}, {omega}) correctly raised ValueError: {e}")
                else:
                    print(f"    FAIL: _check_val({dfi_val}, {omega}) raised ValueError, but wrong message: {e}")
            except Exception as e:
                print(f"    FAIL: _check_val({dfi_val}, {omega}) raised unexpected error for invalid DFI: {e}")

        # Test 5: Invalid types for 'x'
        print("  Test 5: Invalid types for input 'x'")
        for invalid_val in invalid_types:
            try:
                _check_val(invalid_val, omega) # type: ignore 
                print(f"    FAIL: _check_val({invalid_val!r}, {omega}) accepted invalid type.")
            except TypeError as e:
                if "Expected int (for DFI) or Unio instance" in str(e):
                    print(f"    PASS: _check_val({invalid_val!r}, {omega}) correctly raised TypeError: {e}")
                else:
                    print(f"    FAIL: _check_val({invalid_val!r}, {omega}) raised TypeError, but wrong message: {e}")
            except Exception as e:
                print(f"    FAIL: _check_val({invalid_val!r}, {omega}) raised unexpected error for invalid type: {e}")
        print("-" * 60)

    print("\n--- _check_val Domain Enforcement Tests Completed ---")

if __name__ == "__main__":
    run_tests()