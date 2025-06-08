# test_unio_properties.py
# Purpose: To test the fundamental properties of the Unio class from AVCA Core v1.2b.
# This includes aspect initialization, object distinction vs. algebraic equivalence,
# hashing, and representation.

from typing import Literal, Union # Added Union for AVCVal type hint, though not strictly needed for this script

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

# --- Canonical Unio Instances (Copied directly from Appendix A of AVCA Core DraftV3) ---
ZERO_UNIO = Unio("zero")  # Represents Unio with its conceptual Zero-State aspect.
AREO_UNIO = Unio("areo")  # Represents Unio with its conceptual Areo-State (saturation) aspect.

# --- Type Alias (for completeness, though not strictly used in tests below) ---
AVCVal = Union[int, Unio]


def run_tests():
    print("--- Starting Unio Property Tests (AVCA Core v1.2b Logic) ---\n")

    # Test 1: Aspect Initialization and Attribute Correctness
    print("Test 1: Aspect Initialization and Attribute Correctness")
    print(f"  ZERO_UNIO.aspect: '{ZERO_UNIO.aspect}' (Expected: 'zero')")
    assert ZERO_UNIO.aspect == "zero"
    print(f"  AREO_UNIO.aspect: '{AREO_UNIO.aspect}' (Expected: 'areo')")
    assert AREO_UNIO.aspect == "areo"
    
    custom_zero = Unio("zero")
    custom_areo = Unio("areo")
    print(f"  custom_zero.aspect: '{custom_zero.aspect}' (Expected: 'zero')")
    assert custom_zero.aspect == "zero"
    print(f"  custom_areo.aspect: '{custom_areo.aspect}' (Expected: 'areo')")
    assert custom_areo.aspect == "areo"
    
    try:
        invalid_unio = Unio("invalid_aspect") # type: ignore
        print("  FAIL: Invalid aspect initialization did not raise ValueError.")
    except ValueError as e:
        print(f"  PASS: Invalid aspect initialization correctly raised ValueError: {e}")
    print("-" * 40)

    # Test 2: Object Distinction vs. Algebraic Equivalence (__eq__)
    print("\nTest 2: Object Distinction vs. Algebraic Equivalence (__eq__)")
    print(f"  id(ZERO_UNIO): {id(ZERO_UNIO)}")
    print(f"  id(AREO_UNIO): {id(AREO_UNIO)}")
    print(f"  id(custom_zero): {id(custom_zero)}")
    print(f"  id(custom_areo): {id(custom_areo)}")
    
    print(f"  ZERO_UNIO is AREO_UNIO: {ZERO_UNIO is AREO_UNIO} (Expected: False - different objects)")
    assert not (ZERO_UNIO is AREO_UNIO)
    print(f"  ZERO_UNIO == AREO_UNIO: {ZERO_UNIO == AREO_UNIO} (Expected: True - algebraic equivalence)")
    assert (ZERO_UNIO == AREO_UNIO)
    
    print(f"  custom_zero is ZERO_UNIO: {custom_zero is ZERO_UNIO} (Expected: False - different objects unless interns)") # Python might intern identical strings for aspects
    # No assertion here as interning of Unio objects themselves is not guaranteed
    print(f"  custom_zero == ZERO_UNIO: {custom_zero == ZERO_UNIO} (Expected: True - algebraic equivalence)")
    assert (custom_zero == ZERO_UNIO)
    
    print(f"  custom_areo == AREO_UNIO: {custom_areo == AREO_UNIO} (Expected: True - algebraic equivalence)")
    assert (custom_areo == AREO_UNIO)

    print(f"  Unio('zero') == Unio('areo'): {Unio('zero') == Unio('areo')} (Expected: True)")
    assert (Unio('zero') == Unio('areo'))
    
    print(f"  ZERO_UNIO == 0: {ZERO_UNIO == 0} (Expected: False)")
    assert not (ZERO_UNIO == 0)
    print(f"  ZERO_UNIO == 'Unio(zero)': {ZERO_UNIO == 'Unio(zero)'} (Expected: False)") # type: ignore
    assert not (ZERO_UNIO == 'Unio(zero)') # type: ignore
    print("-" * 40)

    # Test 3: Hashing Behavior (__hash__)
    print("\nTest 3: Hashing Behavior (__hash__)")
    hash_zu = hash(ZERO_UNIO)
    hash_au = hash(AREO_UNIO)
    hash_cz = hash(custom_zero)
    hash_ca = hash(custom_areo)
    hash_new_zu = hash(Unio("zero"))
    hash_new_au = hash(Unio("areo"))

    print(f"  hash(ZERO_UNIO): {hash_zu}")
    print(f"  hash(AREO_UNIO): {hash_au}")
    print(f"  hash(custom_zero): {hash_cz}")
    print(f"  hash(custom_areo): {hash_ca}")
    print(f"  hash(Unio('zero')): {hash_new_zu}")
    print(f"  hash(Unio('areo')): {hash_new_au}")
    
    print(f"  All Unio hashes are equal: {(hash_zu == hash_au == hash_cz == hash_ca == hash_new_zu == hash_new_au)} (Expected: True)")
    assert (hash_zu == hash_au == hash_cz == hash_ca == hash_new_zu == hash_new_au)
    
    # Test if Unio objects can be used in a set (relies on __eq__ and __hash__)
    unio_set = {ZERO_UNIO, AREO_UNIO, custom_zero, custom_areo, Unio("zero"), Unio("areo")}
    print(f"  Size of set containing multiple Unio objects: {len(unio_set)} (Expected: 1)")
    assert len(unio_set) == 1
    print(f"  Element in set: {list(unio_set)[0]!r}") # Should be one of them, e.g., Unio('zero') or Unio('areo')
    print("-" * 40)

    # Test 4: String Representation (__repr__)
    print("\nTest 4: String Representation (__repr__)")
    print(f"  repr(ZERO_UNIO): '{repr(ZERO_UNIO)}' (Expected: Unio('zero'))")
    assert repr(ZERO_UNIO) == "Unio('zero')"
    print(f"  repr(AREO_UNIO): '{repr(AREO_UNIO)}' (Expected: Unio('areo'))")
    assert repr(AREO_UNIO) == "Unio('areo')"
    print(f"  repr(custom_zero): '{repr(custom_zero)}' (Expected: Unio('zero'))")
    assert repr(custom_zero) == "Unio('zero')"
    print(f"  repr(custom_areo): '{repr(custom_areo)}' (Expected: Unio('areo'))")
    assert repr(custom_areo) == "Unio('areo')"
    print("-" * 40)

    print("\n--- Unio Property Tests Completed ---")

if __name__ == "__main__":
    run_tests()