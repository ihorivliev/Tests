# Script R3.1: SMT Dual Role Contradiction (N=2, No Commutativity) - Corrected Print
# Purpose: To use SMT to formally prove that it's impossible for a unique element U
# in a 2-element set {U, D1} to be simultaneously a universal (left and right)
# additive identity AND a universal (left and right) additive absorber for D1
# under a single binary operation 'add', without assuming 'add' is commutative.
# This addresses the mathematical obligation R3 from the math LLM's roadmap.

from pysmt.shortcuts import Symbol, Function, Equals, Not, And, Or, Implies, Iff
from pysmt.shortcuts import Solver, Int, TRUE, FALSE, FunctionType
from pysmt.typing import INT

def run_r3_dual_role_contradiction_n2_corrected():
    """
    Sets up and runs the SMT check for the dual role contradiction for N=2 (corrected print).
    """
    print("--- R3.1: SMT Dual Role Contradiction for N=2 (No Commutativity) - Corrected Print ---")

    # 1. Define Elements U and D1 as distinct integer constants
    U_const = Int(0)  # Representing U
    D1_const = Int(1) # Representing D1
    elements = [U_const, D1_const]
    print(f"\nRepresenting elements as: U = {U_const.constant_value()}, D1 = {D1_const.constant_value()}")
    print(f"Implicitly, U != D1 since {U_const.constant_value()} != {D1_const.constant_value()}.")

    # 2. Define 'add' as an SMT function: add: S x S -> S
    add_func_signature = FunctionType(INT, [INT, INT])
    add = Symbol("add", add_func_signature)
    # Corrected print statement:
    print(f"Defining binary operation: {add.serialize()} with signature {str(add_func_signature)}")


    assertions = []
    assertion_descriptions = {} # To map formula objects back to descriptions

    # Helper to add and describe assertions
    def add_described_assertion(formula, description):
        assertions.append(formula)
        assertion_descriptions[formula] = description
        # To keep the output cleaner for this run, let's comment out the per-assertion print for now
        # print(f"  {description} :: {formula.serialize()}")

    # 4. Assert Totality
    # print("\nAsserting Totality (add(x,y) must result in U or D1):") # Keep output less verbose
    for i, x_in in enumerate(elements):
        for j, y_in in enumerate(elements):
            desc = f"Totality for add({x_in.constant_value()},{y_in.constant_value()})"
            formula = Or(Equals(add(x_in, y_in), U_const), Equals(add(x_in, y_in), D1_const))
            add_described_assertion(formula, desc)

    # 5. Assert U is Left and Right Identity
    # print("\nAsserting U is Left and Right Identity:") # Keep output less verbose
    id1_formula = Equals(add(U_const, U_const), U_const)
    add_described_assertion(id1_formula, "Identity U+U=U")
    
    id2_formula = Equals(add(U_const, D1_const), D1_const)
    add_described_assertion(id2_formula, "Identity U+D1=D1 (U is left identity for D1)")
    
    id3_formula = Equals(add(D1_const, U_const), D1_const)
    add_described_assertion(id3_formula, "Identity D1+U=D1 (U is right identity for D1)")

    # 6. Assert U is Left and Right Absorber for D1 (the non-U element)
    # print("\nAsserting U is Left and Right Absorber for D1:") # Keep output less verbose
    abs1_formula = Equals(add(U_const, D1_const), U_const)
    add_described_assertion(abs1_formula, "Absorber U+D1=U (U is left absorber for D1)")
    
    abs2_formula = Equals(add(D1_const, U_const), U_const)
    add_described_assertion(abs2_formula, "Absorber D1+U=U (U is right absorber for D1)")
    
    print("\nAll assertions prepared. Checking for satisfiability with Z3...")
    
    with Solver(name="z3", unsat_cores_mode="all") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)

        result = s.solve()

        if result:
            print("\nStatus: SAT")
            print("This is UNEXPECTED. A model satisfying all conditions was found.")
            print("This implies there is no contradiction with the given assertions for N=2,")
            print("which would mean U can be both identity and absorber under these rules.")
            print("Please double-check the assertions and the problem statement if this occurs.")
            print("\nModel extract (illustrative):")
            try:
                print(f"  Value of add(U,D1) i.e. add({U_const.constant_value()},{D1_const.constant_value()}): {s.get_value(add(U_const, D1_const))}")
                # Further model details could be extracted if needed.
            except Exception as e:
                print(f"  Could not retrieve specific model details: {e}")
        else:
            print("\nStatus: UNSAT")
            print("This is EXPECTED. The conditions are mutually exclusive, meaning it's impossible")
            print("for U to be both a universal identity and a universal absorber for D1 simultaneously.")
            
            try:
                unsat_core_formulas = s.get_unsat_core() 
                if unsat_core_formulas:
                    print("\n--- UNSAT Core (Minimal Set of Conflicting Assertions from Solver) ---")
                    core_contains_id2 = False
                    core_contains_abs1 = False
                                        
                    for core_formula in unsat_core_formulas:
                        description = assertion_descriptions.get(core_formula, "An assertion from the core (unmapped description)")
                        print(f"  - \"{description}\" :: {core_formula.serialize()}")
                        if core_formula == id2_formula: 
                            core_contains_id2 = True
                        if core_formula == abs1_formula: 
                            core_contains_abs1 = True
                    
                    print("\n--- Analysis of the Contradiction ---")
                    # Always print the key conflicting formulas for clarity, regardless of explicit core content
                    key_identity_assertion_text = f"Identity U+D1=D1 :: {id2_formula.serialize()}"
                    key_absorber_assertion_text = f"Absorber U+D1=U :: {abs1_formula.serialize()}"
                    print(f"The assertion that U is a Left Identity for D1 implies: {key_identity_assertion_text}")
                    print(f"The assertion that U is a Left Absorber for D1 implies: {key_absorber_assertion_text}")
                    
                    if core_contains_id2 and core_contains_abs1:
                        print("\n  >> Conclusion: The UNSAT core explicitly contains the direct contradiction.")
                        print(f"     These two assertions together require D1 ({D1_const.constant_value()}) to be equal to U ({U_const.constant_value()}),")
                        print(f"     which contradicts the premise of U and D1 being distinct elements.")
                    else:
                        print("\n  >> Conclusion: The UNSAT core (listed above) demonstrates overall unsatisfiability.")
                        print(f"     The fundamental conflict remains that 'add(U,D1)' cannot simultaneously be D1 and U.")
                        print(f"     This necessarily implies D1 = U, contradicting their distinctness.")

                else:
                    print("\nUNSAT Core: The solver confirmed UNSAT but did not return a specific list of core formulas.")
                    print("However, the unsatisfiability arises because the properties asserted for 'add(U,D1)' are contradictory:")
                    print(f"  - Identity requires: {id2_formula.serialize()}")
                    print(f"  - Absorber requires: {abs1_formula.serialize()}")
                    print(f"These assertions force D1 ({D1_const.constant_value()}) = U ({U_const.constant_value()}), violating their distinctness.")

            except Exception as e:
                print(f"\nError or issue during UNSAT core processing: {e}")
                print("Despite this, the overall status is UNSAT, confirming the inherent contradiction.")
                print("The primary conflicting assertions are necessarily:")
                print(f"  - Identity: {id2_formula.serialize()} (i.e., add(U,D1) = D1)")
                print(f"  - Absorber: {abs1_formula.serialize()} (i.e., add(U,D1) = U)")

    print("\n--- R3.1 Script (Corrected Print) Finished ---")

if __name__ == "__main__":
    run_r3_dual_role_contradiction_n2_corrected()