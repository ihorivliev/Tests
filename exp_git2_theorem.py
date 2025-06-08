# Script GIT.2: SMT Test for Uniqueness of ⊕ Table under Axioms A1-A5 (Ω=3)
# Mathematical Obligation: Direct SMT verification for Lemma L10 / Theorem Clause 5.
# Purpose: For Ω=3, to use SMT to determine if there exists any *alternative*
#          addition table (`alt_add`) that satisfies all axioms A1-A5
#          (Totality, Commutativity, Identity U, Classical Regime/DFI-Haven, Overflow Collapse)
#          but *differs* from the standard AVCA ⊕_v1.1 table.
# Expected Result: UNSAT (proving uniqueness for Ω=3 under A1-A5).

from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Core AVCA Components (adapted from previous scripts / AVCA Core DraftV4 App A) ---
# Using _GIT2 suffix for clarity
_Omega_GIT2: int = 0

class Unio_GIT2:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_GIT2 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_GIT2) 
    def __hash__(self) -> int:
        return hash(f"Unio_GIT2_Algebraic_Singleton") 
    def __repr__(self) -> str:
        return f"Unio_GIT2('{self.aspect}')"

ZERO_UNIO_GIT2 = Unio_GIT2("zero")
AREO_UNIO_GIT2 = Unio_GIT2("areo") 
AVCVal_GIT2 = Union[int, Unio_GIT2] # This line now correctly uses the imported Union

def set_avca_omega_git2(omega_value: int):
    global _Omega_GIT2
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega parameter must be an integer >= 1.")
    _Omega_GIT2 = omega_value

def _check_val_git2(x: AVCVal_GIT2, current_omega: int, var_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega ({current_omega}) for {var_name} must be >= 1.")
    if isinstance(x, Unio_GIT2): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Omega={current_omega}")
    if current_omega == 1 and isinstance(x, int):
        raise ValueError(f"Invalid DFI {x} for {var_name} for Omega=1. DFI empty.")
    if current_omega > 1 and not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI {x} for {var_name}. Omega={current_omega}, DFI [1,{current_omega-1}]")

# Standard AVCA Add (⊕_v1.1 logic)
def avc_add_v1_1_git2(a: AVCVal_GIT2, b: AVCVal_GIT2, current_omega: int) -> AVCVal_GIT2:
    _check_val_git2(a, current_omega, "add_v11_a")
    _check_val_git2(b, current_omega, "add_v11_b")
    if isinstance(a, Unio_GIT2): return b
    if isinstance(b, Unio_GIT2): return a
    res_val: int = a + b # type: ignore
    # For standard AVCA ⊕_v1.1, overflow result is AREO_UNIO_GIT2 (algebraically Unio)
    return res_val if res_val < current_omega else AREO_UNIO_GIT2 

# --- SMT Test Function ---
def test_uniqueness_of_addition_table_smt(current_omega: int):
    print(f"\n====== Script GIT.2: SMT Test for Uniqueness of ⊕ Table (Axioms A1-A5) for Ω={current_omega} ======")
    set_avca_omega_git2(current_omega)

    if current_omega < 1:
        print("  Ω must be >= 1. Test skipped.")
        return

    # Define S_Omega elements as SMT Integers for convenience
    # U_val will represent algebraic Unio. DFI elements are their int values.
    U_val_smt = Int(0) # Algebraic Unio representation in SMT
    s_omega_smt_elements: List[FNode] = [U_val_smt]
    dfi_py_elements: List[int] = []

    if current_omega == 1:
        s_omega_py_elements_for_table = [ZERO_UNIO_GIT2] # For creating std table
    else:
        s_omega_py_elements_for_table = [ZERO_UNIO_GIT2] + list(range(1, current_omega))
        dfi_py_elements = list(range(1, current_omega))
        s_omega_smt_elements.extend([Int(i) for i in dfi_py_elements])
    
    print(f"  S_{current_omega} represented as SMT integers: {[e.constant_value() for e in s_omega_smt_elements]}")
    print(f"  (Where {U_val_smt.constant_value()} represents algebraic Unio U)")


    # Define symbolic results for each cell of the alt_add table: res_ab = alt_add(a,b)
    alt_add_results: Dict[Tuple[int, int], FNode] = {}
    for a_py in s_omega_py_elements_for_table: # Use Python values for keys
        val_a_smt = U_val_smt if isinstance(a_py, Unio_GIT2) else Int(a_py)
        for b_py in s_omega_py_elements_for_table:
            val_b_smt = U_val_smt if isinstance(b_py, Unio_GIT2) else Int(b_py)
            # Ensure consistent keying, e.g. using integer representations
            key_a = U_val_smt.constant_value() if isinstance(a_py, Unio_GIT2) else a_py
            key_b = U_val_smt.constant_value() if isinstance(b_py, Unio_GIT2) else b_py
            alt_add_results[(key_a, key_b)] = Symbol(f"res_{key_a}_{key_b}", SMT_INT_TYPE)

    assertions = []

    # Axiom A1 (Totality): Each res_X_Y must be in S_omega (0, 1, ..., Omega-1 if U is 0)
    print("\n1. Asserting Axiom A1 (Totality) for alt_add results:")
    for r_py_val_key in s_omega_py_elements_for_table: # Iterate Python values for consistent keys
        key_a = U_val_smt.constant_value() if isinstance(r_py_val_key, Unio_GIT2) else r_py_val_key
        for c_py_val_key in s_omega_py_elements_for_table:
            key_b = U_val_smt.constant_value() if isinstance(c_py_val_key, Unio_GIT2) else c_py_val_key
            res_var = alt_add_results[(key_a, key_b)]
            
            is_in_s_omega_clauses = [Equals(res_var, smt_elem) for smt_elem in s_omega_smt_elements]
            assertions.append(Or(is_in_s_omega_clauses))
            # print(f"  alt_add({key_a},{key_b}) ∈ S_{current_omega}")

    # Axiom A2 (Commutativity for alt_add)
    print("\n2. Asserting Axiom A2 (Commutativity) for alt_add:")
    # Only need to assert for unique pairs (a < b)
    py_keys_for_comm = [U_val_smt.constant_value() if isinstance(e, Unio_GIT2) else e for e in s_omega_py_elements_for_table]
    for i in range(len(py_keys_for_comm)):
        for j in range(i + 1, len(py_keys_for_comm)):
            key_a = py_keys_for_comm[i]
            key_b = py_keys_for_comm[j]
            comm_assert = Equals(alt_add_results[(key_a, key_b)], alt_add_results[(key_b, key_a)])
            assertions.append(comm_assert)
            # print(f"  alt_add({key_a},{key_b}) = alt_add({key_b},{key_a})")

    # Axiom A3 (Identity U for alt_add) - U_val_smt is Int(0)
    print("\n3. Asserting Axiom A3 (Identity U) for alt_add:")
    for x_smt in s_omega_smt_elements: # x is an SMT Int constant from s_omega_smt_elements
        # U + x = x
        key_x_py = x_smt.constant_value()
        assertions.append(Equals(alt_add_results[(U_val_smt.constant_value(), key_x_py)], x_smt))
        # x + U = x (covered by commutativity if asserted for U with others, or assert explicitly)
        if not any(comm_assert.arg(0) == alt_add_results[(U_val_smt.constant_value(), key_x_py)] and 
                   comm_assert.arg(1) == alt_add_results[(key_x_py, U_val_smt.constant_value())] 
                   for comm_assert in assertions if comm_assert.is_equals()): # Check if already covered
             assertions.append(Equals(alt_add_results[(key_x_py, U_val_smt.constant_value())], x_smt))


    # Axiom A4 (Classical Regime/DFI-Haven for alt_add)
    # If a,b∈DFI and a+b < Ω, then alt_add(a,b) = a+b (standard integer sum)
    print("\n4. Asserting Axiom A4 (Classical Regime/DFI-Haven) for alt_add:")
    if current_omega > 1: # DFI exists
        for a_dfi_val in dfi_py_elements:
            for b_dfi_val in dfi_py_elements:
                if (a_dfi_val + b_dfi_val) < current_omega:
                    classical_sum = a_dfi_val + b_dfi_val
                    # Ensure classical_sum is actually a DFI value itself, if not, this case shouldn't apply for DFI result
                    # This condition a+b < Omega already implies classical_sum is DFI if a,b are DFI.
                    if 1 <= classical_sum < current_omega: # The result must be a DFI
                         assertions.append(Equals(alt_add_results[(a_dfi_val, b_dfi_val)], Int(classical_sum)))
                    # else: result is not DFI, so A4 does not apply to force it to be a+b.
                    # For example, if Omega=3, a=1,b=1, a+b=2. A4 applies: alt_add(1,1)=2.
                    # What if Omega=2, a=1,b=1? a+b=2. Not < Omega. A4 does not apply. A5 applies.
                    # What if Omega=4, a=1,b=1? a+b=2 < Omega. A4 applies: alt_add(1,1)=2.
                    # What if Omega=4, a=1,b=2? a+b=3 < Omega. A4 applies: alt_add(1,2)=3.
    
    # Axiom A5 (Overflow Collapse for alt_add)
    # If a,b∈DFI and a+b ≥ Ω, then alt_add(a,b) = U
    print("\n5. Asserting Axiom A5 (Overflow Collapse) for alt_add:")
    if current_omega > 1: # DFI exists
        for a_dfi_val in dfi_py_elements:
            for b_dfi_val in dfi_py_elements:
                if (a_dfi_val + b_dfi_val) >= current_omega:
                    assertions.append(Equals(alt_add_results[(a_dfi_val, b_dfi_val)], U_val_smt))

    # Generate standard AVCA ⊕_v1.1 table for comparison
    std_avc_add_table_git2: Dict[Tuple[int, int], int] = {}
    for a_py_std in s_omega_py_elements_for_table:
        val_a_for_op = a_py_std
        key_a_std = U_val_smt.constant_value() if isinstance(a_py_std, Unio_GIT2) else a_py_std
        for b_py_std in s_omega_py_elements_for_table:
            val_b_for_op = b_py_std
            key_b_std = U_val_smt.constant_value() if isinstance(b_py_std, Unio_GIT2) else b_py_std
            
            std_res_obj = avc_add_v1_1_git2(val_a_for_op, val_b_for_op, current_omega)
            std_res_int = U_val_smt.constant_value() if isinstance(std_res_obj, Unio_GIT2) else std_res_obj
            std_avc_add_table_git2[(key_a_std, key_b_std)] = std_res_int
            
    # Assert Difference from standard avc_add_v1_1 table
    print("\n6. Asserting alt_add differs from standard avc_add_v1_1 for at least one pair:")
    difference_clauses = []
    for r_py_val_key in s_omega_py_elements_for_table:
        key_a = U_val_smt.constant_value() if isinstance(r_py_val_key, Unio_GIT2) else r_py_val_key
        for c_py_val_key in s_omega_py_elements_for_table:
            key_b = U_val_smt.constant_value() if isinstance(c_py_val_key, Unio_GIT2) else c_py_val_key
            
            std_result_int = std_avc_add_table_git2[(key_a, key_b)]
            difference_clauses.append(NotEquals(alt_add_results[(key_a, key_b)], Int(std_result_int)))
    assertions.append(Or(difference_clauses))

    print("\nAll assertions prepared. Solving with Z3...")
    with Solver(name="z3", logic="LIA") as s: 
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()

        if result:
            print("Status: SAT")
            print("  This is UNEXPECTED if all axioms A1-A5 truly uniquely determine ⊕_v1.1.")
            print("  An alternative addition table for Ω=3 was found that satisfies A1-A5 but differs from std ⊕_v1.1.")
            model = s.get_model()
            print("\n  Alternative 'alt_add' Table (Model) for Ω=3 (U=0, D1=1, D2=2):")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_py_val in s_omega_py_elements_for_table:
                row_str = f"     {U_val_smt.constant_value() if isinstance(r_py_val, Unio_GIT2) else r_py_val: <2}| "
                for c_py_val in s_omega_py_elements_for_table:
                    val = model.get_value(alt_add_results[(U_val_smt.constant_value() if isinstance(r_py_val, Unio_GIT2) else r_py_val, 
                                                           U_val_smt.constant_value() if isinstance(c_py_val, Unio_GIT2) else c_py_val)])
                    row_str += f" {val}  | "
                print(row_str)
            
            print("\n  Standard avc_add_v1_1 Table for Ω=3 for comparison:")
            print("    a\\b |  0  |  1  |  2  ")
            print("    ----|-----|-----|-----")
            for r_py_val_std in s_omega_py_elements_for_table:
                row_str_std = f"     {U_val_smt.constant_value() if isinstance(r_py_val_std, Unio_GIT2) else r_py_val_std:<2}| "
                for c_py_val_std in s_omega_py_elements_for_table:
                    val_std = std_avc_add_table_git2[(U_val_smt.constant_value() if isinstance(r_py_val_std, Unio_GIT2) else r_py_val_std, 
                                                      U_val_smt.constant_value() if isinstance(c_py_val_std, Unio_GIT2) else c_py_val_std)]
                    row_str_std += f" {val_std}  | "
                print(row_str_std)
        else:
            print("Status: UNSAT")
            print("  This is EXPECTED. It means NO alternative addition table exists for Ω=3")
            print("  that satisfies all Axioms A1-A5 (Totality, Commutativity, Identity U,")
            print("  Classical Regime/DFI-Haven, and Overflow Collapse) AND also differs")
            print("  from the standard AVCA ⊕_v1.1 table.")
            print("  This provides strong SMT evidence for the uniqueness of the ⊕_v1.1 table under these axioms.")

    print(f"\n====== GIT.2 Script for Ω={current_omega} Finished ======")

# --- Main Execution ---
if __name__ == "__main__":
    test_uniqueness_of_addition_table_smt(current_omega=3)
    # To test for other Omega, change the value above, e.g., test_uniqueness_of_addition_table_smt(current_omega=4)
    # Note: Omega=2 is associative, and its table is also uniquely determined by these axioms.
    # test_uniqueness_of_addition_table_smt(current_omega=2)