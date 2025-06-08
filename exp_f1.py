# Script F.1: SMT Search for Alternative Addition Table (Ω=3, No Commutativity, Relaxed DFI-Haven)
# Red-Team Audit: Attack on Claim 5 "Uniqueness of ⊕ table"
# Falsification Strategy: SMT: drop commutativity or remove rule “a+b<Ω→a+b”;
#                        search for an alternative total identity operation.

from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Literal

# --- AVCA Primitives (Simplified for this SMT context) ---
# For this script, we represent S_Omega elements directly as SMT Integers
# U_sF1 = Int(0)
# D1_sF1 = Int(1) # Fp(1)
# D2_sF1 = Int(2) # Fp(2) for Omega=3

# Standard AVCA Add (⊕_v1.1) for comparison table
# We'll use a Python dictionary for the standard table for Ω=3
# U=0, D1=1, D2=2
# AREO_UNIO is algebraically U (0)
std_avc_add_table_omega3: Dict[Tuple[int, int], int] = {
    # (a, b) : a ⊕_v1.1 b
    (0, 0): 0, (0, 1): 1, (0, 2): 2,
    (1, 0): 1, (1, 1): 2, (1, 2): 0, # 1+2=3 -> Unio (0)
    (2, 0): 2, (2, 1): 0, # 2+1=3 -> Unio (0)
              (2, 2): 0  # 2+2=4 -> Unio (0)
}


def run_smt_alternative_add_table_search_f1():
    print("====== Script F.1: SMT Search for Alternative Addition Table (Ω=3, No Commutativity, Relaxed DFI-Haven) ======")
    
    omega_val = 3
    U_val = 0
    D1_val = 1
    D2_val = 2
    
    s_omega_elements = [Int(U_val), Int(D1_val), Int(D2_val)]
    s_omega_py_elements = [U_val, D1_val, D2_val]

    # Define 9 SMT integer variables for the outputs of alt_add(row, col)
    # Each can be U, D1, or D2 (0, 1, or 2)
    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    for r_idx, r_py_val in enumerate(s_omega_py_elements):
        for c_idx, c_py_val in enumerate(s_omega_py_elements):
            alt_add_results[(r_py_val, c_py_val)] = Symbol(f"res_{r_py_val}_{c_py_val}", SMT_INT_TYPE)

    assertions = []

    # 1. Assert Totality: Each alt_add_results[key] must be in S_3 = {0, 1, 2}
    print("\n1. Asserting Totality for alt_add results:")
    for r_py_val in s_omega_py_elements:
        for c_py_val in s_omega_py_elements:
            res_var = alt_add_results[(r_py_val, c_py_val)]
            assertions.append(Or(Equals(res_var, Int(U_val)),
                                 Equals(res_var, Int(D1_val)),
                                 Equals(res_var, Int(D2_val))))
            # print(f"  alt_add({r_py_val},{c_py_val}) ∈ {{0,1,2}}")


    # 2. Assert U (Int(0)) is Left and Right Identity for alt_add
    print("\n2. Asserting U (0) is Left and Right Identity for alt_add:")
    assertions.append(Equals(alt_add_results[(U_val, U_val)], Int(U_val)))   # U+U = U
    assertions.append(Equals(alt_add_results[(U_val, D1_val)], Int(D1_val))) # U+D1 = D1
    assertions.append(Equals(alt_add_results[(U_val, D2_val)], Int(D2_val))) # U+D2 = D2
    assertions.append(Equals(alt_add_results[(D1_val, U_val)], Int(D1_val))) # D1+U = D1
    assertions.append(Equals(alt_add_results[(D2_val, U_val)], Int(D2_val))) # D2+U = D2

    # 3. Assert DFI+DFI Overflow Rule for alt_add (conceptual sum s = val(a)+val(b))
    #    If s >= Ω (i.e., s >= 3), then alt_add(a,b) = U (0).
    #    This directly implements "classical behaviour ... until overflow" (overflow part).
    print("\n3. Asserting DFI+DFI Overflow Rule (sum >= Ω -> U) for alt_add:")
    # D1+D1 (1+1=2). This is < Ω=3. Rule: NOT assert it must be D2. It can be anything in S3.
    # This is the "remove rule 'a+b<Ω→a+b'" part.
    # alt_add_results[(D1_val, D1_val)] is only constrained by Totality.
    
    # D1+D2 (1+2=3). This is == Ω=3. Must be U.
    assertions.append(Equals(alt_add_results[(D1_val, D2_val)], Int(U_val)))
    # D2+D1 (2+1=3). This is == Ω=3. Must be U.
    assertions.append(Equals(alt_add_results[(D2_val, D1_val)], Int(U_val)))
    # D2+D2 (2+2=4). This is > Ω=3. Must be U.
    assertions.append(Equals(alt_add_results[(D2_val, D2_val)], Int(U_val)))

    # 4. Assert Difference from standard avc_add_v1_1 table for Ω=3
    print("\n4. Asserting alt_add differs from standard avc_add_v1_1 for at least one pair:")
    difference_clauses = []
    for r_py_val in s_omega_py_elements:
        for c_py_val in s_omega_py_elements:
            std_result = std_avc_add_table_omega3[(r_py_val, c_py_val)]
            difference_clauses.append(NotEquals(alt_add_results[(r_py_val, c_py_val)], Int(std_result)))
    assertions.append(Or(difference_clauses)) # At least one result must be different

    # 5. No Commutativity Asserted for alt_add in this variant.

    print("\nAll assertions prepared. Solving with Z3...")
    with Solver(name="z3", logic="LIA") as s: # Linear Integer Arithmetic
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()

        print("\n--- Variant 1: No Commutativity Assumed for alt_add ---")
        if result:
            print("Status: SAT")
            print("  This is a POTENTIAL FALSIFICATION of Claim 5's strongest interpretation.")
            print("  An alternative addition table for Ω=3 was found that:")
            print("    - Is total on S3.")
            print("    - Has U (0) as a two-sided identity.")
            print("    - Maps DFI+DFI sums >= Ω to U.")
            print("    - Differs from standard avc_add_v1_1.")
            print("    - Does NOT necessarily respect DFI+DFI sums < Ω being their integer sum.")
            print("    - Is NOT necessarily commutative.")
            
            model = s.get_model()
            print("\n  Alternative 'alt_add' Table for Ω=3 (U=0, D1=1, D2=2):")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_py_val in s_omega_py_elements:
                row_str = f"     {r_py_val}  | "
                for c_py_val in s_omega_py_elements:
                    val = model.get_value(alt_add_results[(r_py_val, c_py_val)])
                    row_str += f" {val}  | "
                print(row_str)
            
            print("\n  Standard avc_add_v1_1 Table for Ω=3 for comparison:")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_py_val in s_omega_py_elements:
                row_str = f"     {r_py_val}  | "
                for c_py_val in s_omega_py_elements:
                    val = std_avc_add_table_omega3[(r_py_val, c_py_val)]
                    row_str += f" {val}  | "
                print(row_str)

        else:
            print("Status: UNSAT")
            print("  This means NO alternative addition table exists for Ω=3 under these relaxed conditions")
            print("  that still has U as identity, maps overflows (>=Ω) to U, is total, and differs from std avc_add_v1_1.")
            print("  This would strongly support the uniqueness of AVCA's ⊕_v1.1 table if 'classical until overflow'")
            print("  is interpreted as 'DFI+DFI sums < Ω can be arbitrary (within S_Omega) but sums >= Ω must be U'.")

    print("\n====== F.1 Script (Variant 1) Finished ======")

if __name__ == "__main__":
    run_smt_alternative_add_table_search_f1()