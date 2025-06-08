# Script GIT.2b: SMT Test for Uniqueness of ⊕ Table (No Commutativity Assumed for alt_add)
# Mathematical Obligation: Lemma L10 / Theorem Clause 5 support, per CR-2 Option (b).
# Purpose: For Ω=3, to use SMT to determine if there exists any *alternative*
#          addition table (`alt_add`) that satisfies Axioms A1 (Totality),
#          A3 (U is Two-Sided Identity), A4 (Classical Regime/DFI-Haven),
#          A5 (Overflow Collapse), but *differs* from the standard AVCA ⊕_v1.1 table,
#          WITHOUT explicitly asserting commutativity (A2 for ⊕) for `alt_add`.
# Expected Result: UNSAT (proving uniqueness from A1, A3-two-sided, A4, A5,
#                  and implying commutativity is an emergent property of this unique table).

from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Core AVCA Components (adapted from previous scripts / AVCA Core DraftV4 App A) ---
# Using _GIT2b suffix
_Omega_GIT2b: int = 0

class Unio_GIT2b: # Renamed
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_GIT2b aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_GIT2b) 
    def __hash__(self) -> int:
        return hash(f"Unio_GIT2b_Algebraic_Singleton") 
    def __repr__(self) -> str:
        return f"Unio_GIT2b('{self.aspect}')"

ZERO_UNIO_GIT2b = Unio_GIT2b("zero")
AREO_UNIO_GIT2b = Unio_GIT2b("areo") 
AVCVal_GIT2b = Union[int, Unio_GIT2b] # This line now correctly uses the imported Union

def set_avca_omega_git2b(omega_value: int):
    global _Omega_GIT2b
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_GIT2b = omega_value

def _check_val_git2b(x: AVCVal_GIT2b, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega ({current_omega}) for {var_name} must be >= 1.")
    if isinstance(x, Unio_GIT2b): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Omega={current_omega}")
    if current_omega == 1 and isinstance(x, int):
        raise ValueError(f"Invalid DFI {x} for {var_name} for Omega=1. DFI empty.")
    if current_omega > 1 and not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI {x} for {var_name}. Omega={current_omega}, DFI [1,{current_omega-1}]")

# Standard AVCA Add (⊕_v1.1 logic) for comparison table
def avc_add_v1_1_git2b(a: AVCVal_GIT2b, b: AVCVal_GIT2b, current_omega: int) -> AVCVal_GIT2b:
    _check_val_git2b(a, current_omega, "add_v11_a")
    _check_val_git2b(b, current_omega, "add_v11_b")
    if isinstance(a, Unio_GIT2b): return b
    if isinstance(b, Unio_GIT2b): return a
    res_val: int = a + b # type: ignore
    return res_val if res_val < current_omega else AREO_UNIO_GIT2b 

# --- SMT Test Function ---
def test_uniqueness_of_addition_table_smt_no_comm(current_omega: int):
    print(f"\n====== Script GIT.2b: SMT Test for Uniqueness of ⊕ Table (No Commutativity Assumed for alt_add) for Ω={current_omega} ======")
    set_avca_omega_git2b(current_omega)

    if current_omega < 1:
        print("  Ω must be >= 1. Test skipped.")
        return
    if current_omega != 3:
        print(f"  This script variant is specifically configured for Ω=3 due to explicit DFI values. Current Ω={current_omega}. Test skipped.")
        return

    U_val_smt = Int(0) 
    D1_val_smt = Int(1) # Fp(1)
    D2_val_smt = Int(2) # Fp(2) for Omega=3
    
    s_omega_smt_elements = [U_val_smt, D1_val_smt, D2_val_smt]
    s_omega_py_elements_for_table = [ZERO_UNIO_GIT2b, 1, 2] # For generating std_table keys
    dfi_py_elements = [1, 2]

    print(f"  S_{current_omega} represented as SMT integers: {[e.constant_value() for e in s_omega_smt_elements]}")
    print(f"  (Where {U_val_smt.constant_value()} represents algebraic Unio U)")

    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    py_keys_for_smt = [U_val_smt.constant_value(), D1_val_smt.constant_value(), D2_val_smt.constant_value()]
    for r_py_key in py_keys_for_smt:
        for c_py_key in py_keys_for_smt:
            alt_add_results[(r_py_key, c_py_key)] = Symbol(f"res_nc_{r_py_key}_{c_py_key}", SMT_INT_TYPE)

    assertions = []

    # Axiom A1 (Totality)
    print("\n1. Asserting Axiom A1 (Totality) for alt_add results.")
    for r_key in py_keys_for_smt:
        for c_key in py_keys_for_smt:
            res_var = alt_add_results[(r_key, c_key)]
            assertions.append(Or(Equals(res_var, U_val_smt),
                                 Equals(res_var, D1_val_smt),
                                 Equals(res_var, D2_val_smt)))

    # Axiom A3 (Two-sided Identity U for alt_add)
    print("\n2. Asserting Axiom A3 (Two-sided Identity U) for alt_add:")
    # U + U = U
    assertions.append(Equals(alt_add_results[(U_val_smt.constant_value(), U_val_smt.constant_value())], U_val_smt))
    # U + D1 = D1 and D1 + U = D1
    assertions.append(Equals(alt_add_results[(U_val_smt.constant_value(), D1_val_smt.constant_value())], D1_val_smt))
    assertions.append(Equals(alt_add_results[(D1_val_smt.constant_value(), U_val_smt.constant_value())], D1_val_smt))
    # U + D2 = D2 and D2 + U = D2
    assertions.append(Equals(alt_add_results[(U_val_smt.constant_value(), D2_val_smt.constant_value())], D2_val_smt))
    assertions.append(Equals(alt_add_results[(D2_val_smt.constant_value(), U_val_smt.constant_value())], D2_val_smt))

    # Axiom A4 (Classical Regime/DFI-Haven for alt_add)
    # If a,b∈DFI and a+b < Ω, then alt_add(a,b) = a+b
    print("\n3. Asserting Axiom A4 (Classical Regime/DFI-Haven) for alt_add:")
    # For Ω=3, DFI={1,2}. Only 1+1=2 < 3.
    if current_omega == 3:
        assertions.append(Equals(alt_add_results[(D1_val_smt.constant_value(), D1_val_smt.constant_value())], D2_val_smt)) # 1+1=2
    
    # Axiom A5 (Overflow Collapse for alt_add)
    # If a,b∈DFI and a+b ≥ Ω, then alt_add(a,b) = U
    print("\n4. Asserting Axiom A5 (Overflow Collapse) for alt_add:")
    if current_omega == 3:
        # D1+D2 (1+2=3) >= 3 -> U
        assertions.append(Equals(alt_add_results[(D1_val_smt.constant_value(), D2_val_smt.constant_value())], U_val_smt))
        # D2+D1 (2+1=3) >= 3 -> U
        assertions.append(Equals(alt_add_results[(D2_val_smt.constant_value(), D1_val_smt.constant_value())], U_val_smt))
        # D2+D2 (2+2=4) >= 3 -> U
        assertions.append(Equals(alt_add_results[(D2_val_smt.constant_value(), D2_val_smt.constant_value())], U_val_smt))

    # Axiom A2 (Commutativity of ⊕) is NOT asserted for alt_add.

    # Generate standard AVCA ⊕_v1.1 table for Ω=3 for comparison
    std_avc_add_table_git2b: Dict[Tuple[int, int], int] = {}
    # Python elements to match keys of alt_add_results
    py_elements_for_std_table = [U_val_smt.constant_value(), D1_val_smt.constant_value(), D2_val_smt.constant_value()]
    
    for a_py_std_key in py_elements_for_std_table:
        # Convert SMT key back to AVCA value for op
        val_a_for_op = ZERO_UNIO_GIT2b if a_py_std_key == U_val_smt.constant_value() else a_py_std_key
        for b_py_std_key in py_elements_for_std_table:
            val_b_for_op = ZERO_UNIO_GIT2b if b_py_std_key == U_val_smt.constant_value() else b_py_std_key
            
            std_res_obj = avc_add_v1_1_git2b(val_a_for_op, val_b_for_op, current_omega)
            std_res_int = U_val_smt.constant_value() if isinstance(std_res_obj, Unio_GIT2b) else std_res_obj
            std_avc_add_table_git2b[(a_py_std_key, b_py_std_key)] = std_res_int
            
    # Assert Difference from standard avc_add_v1_1 table
    print("\n5. Asserting alt_add differs from standard avc_add_v1_1 for at least one pair:")
    difference_clauses = []
    for r_key in py_keys_for_smt:
        for c_key in py_keys_for_smt:
            std_result_int = std_avc_add_table_git2b[(r_key, c_key)]
            difference_clauses.append(NotEquals(alt_add_results[(r_key, c_key)], Int(std_result_int)))
    assertions.append(Or(difference_clauses))

    print("\nAll assertions prepared. Solving with Z3...")
    with Solver(name="z3", logic="LIA") as s: 
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()

        print("\n--- GIT.2b: No Commutativity Assumed for alt_add (Axioms A1, A3-two-sided, A4, A5 enforced) ---")
        if result:
            print("Status: SAT")
            print("  This is UNEXPECTED if A1, A3-two-sided, A4, A5 truly uniquely determine ⊕_v1.1 (and its emergent commutativity).")
            print(f"  An alternative addition table for Ω={current_omega} was found that satisfies these axioms but differs from std ⊕_v1.1.")
            model = s.get_model()
            print(f"\n  Alternative 'alt_add' Table (Model) for Ω={current_omega} (U=0, D1=1, D2=2):")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_py_val in py_keys_for_smt:
                row_str = f"     {r_py_val:<2}| "
                for c_py_val in py_keys_for_smt:
                    val = model.get_value(alt_add_results[(r_py_val, c_py_val)])
                    row_str += f" {val}  | "
                print(row_str)
            
            print(f"\n  Standard avc_add_v1_1 Table for Ω={current_omega} for comparison:")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_py_val_std in py_keys_for_smt:
                row_str_std = f"     {r_py_val_std:<2}| "
                for c_py_val_std in py_keys_for_smt:
                    val_std = std_avc_add_table_git2b[(r_py_val_std, c_py_val_std)]
                    row_str_std += f" {val_std}  | "
                print(row_str_std)
        else:
            print("Status: UNSAT")
            print("  This is EXPECTED. It means NO alternative addition table exists for Ω=3")
            print("  that satisfies Axioms A1 (Totality), A3 (Two-Sided Identity U),")
            print("  A4 (Classical Regime/DFI-Haven), and A5 (Overflow Collapse) AND also differs")
            print("  from the standard AVCA ⊕_v1.1 table.")
            print("  This provides strong SMT evidence that these four axioms for ⊕ uniquely determine")
            print("  the ⊕_v1.1 table (which will also be commutative).")

    print(f"\n====== GIT.2b Script for Ω={current_omega} Finished ======")

# --- Main Execution ---
if __name__ == "__main__":
    # This script is specifically designed for Omega=3 as per math LLM's L10 suggestion
    # for SMT proof of uniqueness for a small critical Omega.
    test_uniqueness_of_addition_table_smt_no_comm(current_omega=3)