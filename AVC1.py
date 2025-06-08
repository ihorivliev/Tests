from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Solver, is_sat, TRUE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE

# --- Phase 1: Foundational Definitions and Equivalence Relation ---
# This script focuses on defining the 'Intensity' type and the 'avc_equiv'
# relation, then rigorously testing the properties of 'avc_equiv' to
# ensure it behaves as a mathematically sound equivalence relation and
# correctly distinguishes between conceptually different intensity states
# as per the AVC model.

# --- Helper function to create an Intensity representation ---
def create_intensity_representation(name_prefix: str):
    """
    Creates PySMT symbols for an Intensity and its critical validity constraints.
    An Intensity is abstractly one of: ZeroState, AreoState, or Finite(PosNat).
    This function models this using boolean flags and a conditional value.

    Args:
        name_prefix (str): A prefix for PySMT symbol names to ensure uniqueness
                           when multiple intensity instances are created.
        
    Returns:
        dict: A dictionary containing:
              'is_zero' (Symbol): True if this intensity is ZeroState.
              'is_areo' (Symbol): True if this intensity is AreoState.
              'is_finite' (Symbol): True if this intensity is Finite.
              'val' (Symbol): The integer value if 'is_finite' (must be > 0).
              'constraints' (PySMT Formula): A formula that *must* be asserted
                                             for this representation to be a
                                             valid, well-defined Intensity.
    """
    is_zero = Symbol(f"{name_prefix}_is_zero", solver_BOOL_TYPE)
    is_areo = Symbol(f"{name_prefix}_is_areo", solver_BOOL_TYPE)
    is_finite = Symbol(f"{name_prefix}_is_finite", solver_BOOL_TYPE)
    val = Symbol(f"{name_prefix}_val", solver_INT_TYPE) # Value if finite

    # --- Validity Constraints for this Intensity representation ---
    # Constraint 1: Exactly one of the state flags must be true.
    # This is fundamental to modeling an algebraic data type with distinct constructors.
    # An Intensity cannot be, for example, both ZeroState and FiniteState.
    constraint_exactly_one_state = ExactlyOne(is_zero, is_areo, is_finite)

    # Constraint 2: If 'is_finite' is true, 'val' must be positive (PosNat constraint).
    # This ensures that any Finite intensity encapsulates a value > 0.
    constraint_pos_nat_if_finite = Implies(is_finite, val > Int(0))
    
    # Combine all constraints that define a valid intensity.
    # Any statement about an intensity 'i' should typically be conjoined with 'i["constraints"]'.
    all_constraints = And(constraint_exactly_one_state, constraint_pos_nat_if_finite)
    
    representation = {
        "is_zero": is_zero,
        "is_areo": is_areo,
        "is_finite": is_finite,
        "val": val,
        "constraints": all_constraints
    }
    return representation

# --- Define the avc_equiv relation ---
def avc_equiv(i1_repr, i2_repr):
    """
    Defines the avc_equiv relation between two intensity representations based on the AVC model.
    This relation is the core of defining Unio in the quotient space.

    Args:
        i1_repr (dict): The representation of the first intensity.
        i2_repr (dict): The representation of the second intensity.
        
    Returns:
        PySMT Formula: A formula that is True if i1_repr is avc_equiv to i2_repr,
                       and False otherwise, according to the AVC definition.
    """
    
    # Case 1: Both are ZeroState
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    
    # Case 2: Both are AreoState
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    
    # Case 3 & 4: One is ZeroState and the other is AreoState (Unio identification)
    # This is the central postulate of the AVC model being formalized.
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"])
    
    # Case 5: Both are FiniteState AND their underlying values are equal.
    finite_finite_equal_val = And(i1_repr["is_finite"], 
                                  i2_repr["is_finite"], 
                                  Equals(i1_repr["val"], i2_repr["val"]))
    
    # avc_equiv is true if *any* of these specific conditions for equivalence hold.
    # All other combinations of intensity kinds, or finite intensities with different values,
    # are implicitly not equivalent by this definition.
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Main section for rigorous testing ---
if __name__ == "__main__":
    print("====== AVC Phase 1: Rigorous Foundational Tests ======")
    print("Methodology: Proving universal properties by showing their negations are UNSATISFIABLE (UNSAT).")
    print("An UNSAT result for 'NOT Property' means 'Property' is PROVED for all valid Intensities.\n")

    # Create symbolic intensity representations. These act as "arbitrary" (universally quantified)
    # intensities for the SMT solver, subject to their validity constraints.
    i1 = create_intensity_representation("i1_sym") # Suffix '_sym' for symbolic
    i2 = create_intensity_representation("i2_sym")
    i3 = create_intensity_representation("i3_sym")

    # --- Test 1: Proving Reflexivity of avc_equiv ---
    # Property: For any valid intensity i, avc_equiv(i, i) must hold.
    # Test: Is it possible to find a valid intensity 'i1' such that NOT avc_equiv(i1, i1)?
    # Expected SMT Result: UNSAT (meaning the property holds universally)
    print("--- Test 1: Proving avc_equiv is Reflexive ---")
    # For a property to hold universally, its negation must be unsatisfiable.
    # The SMT solver will search for any assignment to i1's components (is_zero, is_areo, is_finite, val)
    # that satisfies i1["constraints"] but makes avc_equiv(i1, i1) false.
    with Solver(name="z3") as s: # Using z3 solver; others like 'msat' can be used.
        s.add_assertion(i1["constraints"])         # Crucial: i1 must be a valid intensity.
        s.add_assertion(Not(avc_equiv(i1, i1))) # Assert the negation of reflexivity.
        
        result = s.solve() # Ask the solver if such a counterexample exists.
        if not result: # 'not result' is True if s.solve() is False (UNSAT)
            print("Result: UNSAT. Reflexivity (ForAll i, avc_equiv(i,i)) is PROVED. ✅")
        else:
            # This would be a critical failure, indicating a flaw in definitions.
            print("Result: SAT. Reflexivity FAILED. Counterexample model:")
            print(s.get_model())
    print("-" * 60)

    # --- Test 2: Proving Symmetry of avc_equiv ---
    # Property: For any valid intensities i, j, if avc_equiv(i, j) then avc_equiv(j, i).
    # Test: Is it possible to find valid i1, i2 such that (avc_equiv(i1, i2) AND NOT avc_equiv(i2, i1))?
    # Expected SMT Result: UNSAT
    print("--- Test 2: Proving avc_equiv is Symmetric ---")
    with Solver(name="z3") as s:
        s.add_assertion(i1["constraints"])      # i1 must be valid.
        s.add_assertion(i2["constraints"])      # i2 must be valid.
        s.add_assertion(avc_equiv(i1, i2))      # Assume the premise: avc_equiv(i1, i2) holds.
        s.add_assertion(Not(avc_equiv(i2, i1))) # Assert the negation of the conclusion.
        
        result = s.solve()
        if not result:
            print("Result: UNSAT. Symmetry (avc_equiv(i,j) => avc_equiv(j,i)) is PROVED. ✅")
        else:
            print("Result: SAT. Symmetry FAILED. Counterexample model:")
            print(s.get_model())
    print("-" * 60)

    # --- Test 3: Proving Transitivity of avc_equiv ---
    # Property: For valid i,j,k, if avc_equiv(i,j) and avc_equiv(j,k), then avc_equiv(i,k).
    # Test: Is it possible to find valid i1,i2,i3 such that 
    #       (avc_equiv(i1,i2) AND avc_equiv(i2,i3) AND NOT avc_equiv(i1,i3))?
    # Expected SMT Result: UNSAT
    print("--- Test 3: Proving avc_equiv is Transitive ---")
    with Solver(name="z3") as s:
        s.add_assertion(i1["constraints"])      # i1 must be valid.
        s.add_assertion(i2["constraints"])      # i2 must be valid.
        s.add_assertion(i3["constraints"])      # i3 must be valid.
        s.add_assertion(avc_equiv(i1, i2))      # Assume first part of premise.
        s.add_assertion(avc_equiv(i2, i3))      # Assume second part of premise.
        s.add_assertion(Not(avc_equiv(i1, i3))) # Assert the negation of the conclusion.
        
        result = s.solve()
        if not result:
            print("Result: UNSAT. Transitivity (avc_equiv(i,j) ^ avc_equiv(j,k) => avc_equiv(i,k)) is PROVED. ✅")
        else:
            print("Result: SAT. Transitivity FAILED. Counterexample model:")
            print(s.get_model())
    print("-" * 60)
    
    print("Mathematical Conclusion: Reflexivity, Symmetry, and Transitivity PROVED.")
    print("'avc_equiv' is formally verified as an EQUIVALENCE RELATION over valid Intensity representations.\n")

    # --- Test 4: Proving DFI is distinct from Unio (ZeroState aspect) ---
    # Property: A DFI (finite intensity) is NEVER avc_equiv to ZeroState.
    # Test: Is it possible to find valid i1 (Finite) and i2 (ZeroState) such that avc_equiv(i1, i2) is true?
    # Expected SMT Result: UNSAT
    print("--- Test 4: Proving DFI is distinct from Unio (ZeroState aspect) ---")
    with Solver(name="z3") as s:
        s.add_assertion(i1["constraints"])      # i1 must be a valid intensity.
        s.add_assertion(i1["is_finite"])        # Specifically, i1 is Finite (implies i1.val > 0).
        
        s.add_assertion(i2["constraints"])      # i2 must be a valid intensity.
        s.add_assertion(i2["is_zero"])          # Specifically, i2 is ZeroState.
        
        s.add_assertion(avc_equiv(i1, i2))      # Assert they ARE equivalent (this is the contradiction we seek).
        
        result = s.solve()
        if not result:
            print("Result: UNSAT. Property (DFI is NOT ZeroState) is PROVED. ✅")
        else:
            print("Result: SAT. Property (DFI is NOT ZeroState) FAILED. Counterexample:")
            print(s.get_model()) 
    print("-" * 60)

    # --- Test 5: Proving DFI is distinct from Unio (AreoState aspect) ---
    # Property: A DFI (finite intensity) is NEVER avc_equiv to AreoState.
    # Test: Is it possible to find valid i1 (Finite) and i2 (AreoState) such that avc_equiv(i1, i2) is true?
    # Expected SMT Result: UNSAT
    print("--- Test 5: Proving DFI is distinct from Unio (AreoState aspect) ---")
    with Solver(name="z3") as s:
        s.add_assertion(i1["constraints"])      # i1 must be valid.
        s.add_assertion(i1["is_finite"])        # i1 is Finite.
        
        s.add_assertion(i2["constraints"])      # i2 must be valid.
        s.add_assertion(i2["is_areo"])          # i2 is AreoState.
        
        s.add_assertion(avc_equiv(i1, i2))      # Assert they ARE equivalent.
        
        result = s.solve()
        if not result:
            print("Result: UNSAT. Property (DFI is NOT AreoState) is PROVED. ✅")
        else:
            print("Result: SAT. Property (DFI is NOT AreoState) FAILED. Counterexample:")
            print(s.get_model())
    print("-" * 60)

    # --- Test 6: Proving distinct DFIs (by value) are not equivalent ---
    # Property: If i1 is Finite(v1), i2 is Finite(v2), and v1 != v2, then NOT avc_equiv(i1, i2).
    # Test: Is it possible to find valid i1 (Finite), i2 (Finite) with i1.val != i2.val, 
    #       such that avc_equiv(i1, i2) is true?
    # Expected SMT Result: UNSAT
    print("--- Test 6: Proving distinct DFIs (by value) are not avc_equiv ---")
    with Solver(name="z3") as s:
        s.add_assertion(i1["constraints"])      # i1 must be valid.
        s.add_assertion(i1["is_finite"])        # i1 is Finite.
        
        s.add_assertion(i2["constraints"])      # i2 must be valid.
        s.add_assertion(i2["is_finite"])        # i2 is Finite.
        
        s.add_assertion(Not(Equals(i1["val"], i2["val"]))) # Crucial: their underlying values are different.
        
        s.add_assertion(avc_equiv(i1, i2))      # Assert they ARE equivalent.
        
        result = s.solve()
        if not result:
            print("Result: UNSAT. Property (Distinct Finite Intensities by value are NOT avc_equiv) is PROVED. ✅")
        else:
            print("Result: SAT. Property (Distinct Finite Intensities by value are NOT avc_equiv) FAILED. Counterexample:")
            print(s.get_model()) # If SAT, this would mean avc_equiv is flawed for Finites.
    print("-" * 60)

    print("--- Demonstrating Expected Non-Equivalences (Sanity Checks) ---")
    # These tests check if specific non-equivalences are correctly identified as 'possible to be false'.
    # We expect these to be SAT, where the model shows the non-equivalence.

    # Demonstation 1: Finite(3) is NOT ZeroState
    i_f3 = create_intensity_representation("i_f3")
    i_zs = create_intensity_representation("i_zs")
    formula_f3_not_zs = And(i_f3["constraints"], i_f3["is_finite"], Equals(i_f3["val"], Int(3)),
                              i_zs["constraints"], i_zs["is_zero"],
                              Not(avc_equiv(i_f3, i_zs)))
    print(f"Demonstration (Finite(3) NOT avc_equiv ZeroState): SAT? {is_sat(formula_f3_not_zs)} (Expected: True)")

    # Demonstation 2: Finite(3) is NOT Finite(4)
    i_f4 = create_intensity_representation("i_f4")
    formula_f3_not_f4 = And(i_f3["constraints"], i_f3["is_finite"], Equals(i_f3["val"], Int(3)),
                              i_f4["constraints"], i_f4["is_finite"], Equals(i_f4["val"], Int(4)),
                              Not(avc_equiv(i_f3, i_f4)))
    print(f"Demonstration (Finite(3) NOT avc_equiv Finite(4)): SAT? {is_sat(formula_f3_not_f4)} (Expected: True)")
    
    # Demonstation 3: ZeroState is NOT Finite(1)
    i_f1 = create_intensity_representation("i_f1")
    formula_zs_not_f1 = And(i_zs["constraints"], i_zs["is_zero"],
                              i_f1["constraints"], i_f1["is_finite"], Equals(i_f1["val"], Int(1)),
                              Not(avc_equiv(i_zs, i_f1)))
    print(f"Demonstration (ZeroState NOT avc_equiv Finite(1)): SAT? {is_sat(formula_zs_not_f1)} (Expected: True)")
    print("-" * 60)

    print("====== All Phase 1 rigorous tests and demonstrations complete. ======")
    print("If all 'PROVED' messages are shown for Tests 1-6, and 'SAT? True' for demonstrations,")
    print("the definitions of Intensity and avc_equiv are robustly verified against their")
    print("intended mathematical properties for this phase.")