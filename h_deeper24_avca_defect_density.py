import itertools
from typing import List, Dict, Tuple, Callable, Any, Optional

# --- Python AVCA Kernel (Adapted from SMT Proof Script V12) ---
_Omega_py: Optional[int] = None
_ZERO_UNIO_py_repr = "Unio('zero')" # Represents algebraic U_alg, with zero aspect
_AREO_UNIO_py_repr = "Unio('areo')"   # Represents algebraic U_alg, with areo aspect
PyAVCVal = Any # Can be int (DFI) or str (Unio sentinel)

def set_py_avca_omega(omega_val: int):
    """Sets the global Omega for the Python AVCA operations."""
    global _Omega_py
    if not isinstance(omega_val, int) or omega_val < 1:
        raise ValueError("Python AVCA Omega must be an integer >= 1.")
    _Omega_py = omega_val

def _check_py_val(x: PyAVCVal, omega: int, op_name: str = "py_op", arg_name: str = "input"):
    """Validates a Python AVCA value."""
    if x == _ZERO_UNIO_py_repr or x == _AREO_UNIO_py_repr:
        return
    if not isinstance(x, int):
        raise TypeError(f"Py AVCA val for {op_name}/{arg_name} must be int or Unio sentinel string: got {x} (type {type(x)})")
    if omega == 1 and isinstance(x, int): # S_alg_1 = {U_alg} only
        raise ValueError(f"DFI value {x} is invalid for {op_name}/{arg_name} when Python AVCA Omega is 1.")
    if omega > 1 and not (1 <= x < omega): # DFI values are 1 to omega-1
        raise ValueError(f"DFI value {x} is out of range [1, {omega-1}] for {op_name}/{arg_name} for Python AVCA Omega={omega}.")

def py_avca_add(a: PyAVCVal, b: PyAVCVal) -> PyAVCVal:
    """
    Python AVCA Addition (⊕) - 'avc_add_v1.1' logic from DraftV5.
    - U_alg (represented by Unio sentinels) is the two-sided additive identity.
    - DFI_alg + DFI_alg behaves as standard integer addition if sum < Ω.
    - DFI_alg + DFI_alg results in AREO_UNIO_obj if sum ≥ Ω (overflow).
    """
    if _Omega_py is None:
        raise ValueError("Python AVCA Omega not set. Call set_py_avca_omega(value) first.")
    
    _check_py_val(a, _Omega_py, "py_avca_add", "a")
    _check_py_val(b, _Omega_py, "py_avca_add", "b")

    # Rule 1: U_alg is universal additive identity.
    # Any Unio sentinel acts as U_alg here.
    # The specific aspect of Unio ('zero' or 'areo') does not change its identity role in addition.
    if a == _ZERO_UNIO_py_repr or a == _AREO_UNIO_py_repr:
        return b  # U_alg ⊕ x = x
    if b == _ZERO_UNIO_py_repr or b == _AREO_UNIO_py_repr:
        return a  # x ⊕ U_alg = x

    # Rule 2: Both a and b are DFI_alg elements (integers)
    # Type hinting for clarity after checks
    val_a: int = a
    val_b: int = b
    
    dfi_sum = val_a + val_b

    if dfi_sum < _Omega_py:
        # DFI Classicality (Interior)
        return dfi_sum 
    else:
        # DFI Overflow to U_alg (specifically AREO_UNIO_obj as per avc_add_v1.1)
        return _AREO_UNIO_py_repr

# --- Defect Density Calculation (Task ② from comments) ---
def defect_density_associativity(max_omega_to_test: int = 100, verbose: bool = False):
    """
    Calculates the ⊕-associativity defect density for AVCA.
    Loops Ω from 3 to max_omega_to_test.
    Counts triples (a,b,c) where (a⊕b)⊕c ≠ a⊕(b⊕c).
    """
    print(f"Calculating AVCA ⊕-Associativity Defect Density from Ω=3 to Ω={max_omega_to_test}")
    print("-" * 70)
    print(f"{'Ω':<5} | {'Failing Triples':<15} | {'Total Triples':<15} | {'Defect Density':<15}")
    print("-" * 70)

    table_data = []

    for current_omega_val in range(3, max_omega_to_test + 1):
        set_py_avca_omega(current_omega_val)
        
        # S_alg_Ω elements: U_alg (represented by _ZERO_UNIO_py_repr for iteration, could be _AREO_UNIO_py_repr too)
        # and DFI elements (1 to current_omega_val-1)
        s_alg_elements = [_ZERO_UNIO_py_repr] + list(range(1, current_omega_val))
        
        total_triples = len(s_alg_elements) ** 3
        non_associative_count = 0

        if verbose:
            print(f"\nTesting Ω = {current_omega_val} with elements: {s_alg_elements}")

        for a_val in s_alg_elements:
            for b_val in s_alg_elements:
                for c_val in s_alg_elements:
                    try:
                        # (a⊕b)⊕c
                        lhs = py_avca_add(py_avca_add(a_val, b_val), c_val)
                        # a⊕(b⊕c)
                        rhs = py_avca_add(a_val, py_avca_add(b_val, c_val))

                        # Algebraic comparison: Unio aspects are ignored for equality
                        lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
                        rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)

                        is_associative = False
                        if lhs_is_unio and rhs_is_unio:
                            is_associative = True # Both are U_alg, hence algebraically equal
                        elif lhs == rhs: # Covers DFI == DFI
                            is_associative = True
                        
                        if not is_associative:
                            non_associative_count += 1
                            if verbose:
                                print(f"  Ω={current_omega_val}: Non-associative triplet ({a_val}, {b_val}, {c_val}) -> LHS={lhs}, RHS={rhs}")
                    
                    except Exception as e:
                        print(f"Error during calculation for Ω={current_omega_val}, triplet ({a_val},{b_val},{c_val}): {e}")
                        # Optionally, count errors as non-associative or handle differently
                        non_associative_count += 1 # Counting errors as defects for safety

        density = non_associative_count / total_triples if total_triples > 0 else 0.0
        table_data.append((current_omega_val, non_associative_count, total_triples, density))
        print(f"{current_omega_val:<5} | {non_associative_count:<15} | {total_triples:<15} | {density:<15.4f}")

    print("-" * 70)
    return table_data

# --- Main Execution ---
if __name__ == "__main__":
    # You can change max_omega here. Higher values will take significantly longer.
    # The SMT script output went up to MAX_OMEGA_TEST = 3 for its full suite.
    # For just the defect density, you might try a bit higher, e.g., 7 or 10,
    # but be mindful of the O(N^3) complexity per Omega.
    max_omega_for_density_check = 7 
    
    print("Starting AVCA ⊕-Associativity Defect Density Calculation Script...")
    
    results = defect_density_associativity(max_omega_for_density_check, verbose=False)
    
    print("\nSummary Table Data (Ω, Failing Triples, Total Triples, Defect Density):")
    for row in results:
        print(row)
    
    print("\nScript finished.")
    print("You can now take this data and use tools like sympy or numpy to fit a curve if desired.")
    print("The V12 SMT script's Python output for Ω=3 was: Failing Triples = 4, Total Triples = 27, Defect Density = 0.1481")