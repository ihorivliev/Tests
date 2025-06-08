import itertools
from typing import List, Dict, Tuple, Callable, Any, Optional

# --- Python AVCA Kernel (from our previous scripts) ---
_Omega_py: Optional[int] = None
_ZERO_UNIO_py_repr = "Unio('zero')" 
_AREO_UNIO_py_repr = "Unio('areo')" # Though for table generation, we'll map Unio output to 0
PyAVCVal = Any 

def set_py_avca_omega(omega_val: int):
    global _Omega_py
    if not isinstance(omega_val, int) or omega_val < 1:
        raise ValueError("Python AVCA Omega must be an integer >= 1.")
    _Omega_py = omega_val

def _check_py_val(x: PyAVCVal, omega: int, op_name: str = "py_op", arg_name: str = "input"):
    if x == _ZERO_UNIO_py_repr or x == _AREO_UNIO_py_repr: return
    if not isinstance(x, int):
        raise TypeError(f"Py AVCA val for {op_name}/{arg_name} must be int or Unio sentinel string: got {x} (type {type(x)})")
    if omega == 1 and isinstance(x, int):
        raise ValueError(f"DFI value {x} is invalid for {op_name}/{arg_name} when Python AVCA Omega is 1.")
    if omega > 1 and not (1 <= x < omega): # DFI values are 1 to omega-1
        raise ValueError(f"DFI value {x} is out of range [1, {omega-1}] for {op_name}/{arg_name} for Python AVCA Omega={omega}.")

def py_avca_add(a: PyAVCVal, b: PyAVCVal) -> PyAVCVal:
    """
    Python AVCA Addition (⊕) - 'avc_add_v1.1' logic.
    U_alg is identity. DFI+DFI overflows to AREO_UNIO_obj (U_alg).
    Inputs: a, b can be int (for DFI) or _ZERO_UNIO_py_repr/_AREO_UNIO_py_repr for U_alg.
    Output: int (for DFI result) or _AREO_UNIO_py_repr (if U_alg result from overflow)
            or b if a is U_alg, or a if b is U_alg.
    """
    if _Omega_py is None: raise ValueError("Python AVCA Omega not set.")
    # Note: _check_py_val is important if inputs are not guaranteed to be correct.
    # For table generation, we will construct inputs carefully.
    
    # Handle identity cases first
    a_is_unio = (a == _ZERO_UNIO_py_repr or a == _AREO_UNIO_py_repr)
    b_is_unio = (b == _ZERO_UNIO_py_repr or b == _AREO_UNIO_py_repr)

    if a_is_unio: return b
    if b_is_unio: return a
    
    # Both are integers (DFIs)
    val_a: int = a 
    val_b: int = b
    _check_py_val(val_a, _Omega_py, "py_avca_add", "a_int") # Ensure DFI values are valid
    _check_py_val(val_b, _Omega_py, "py_avca_add", "b_int")

    dfi_sum = val_a + val_b

    if dfi_sum < _Omega_py:
        return dfi_sum 
    else: # Overflow
        return _AREO_UNIO_py_repr # V1 axioms cause overflow to U_alg

def generate_avca_oplus_cayley_table(omega_val: int) -> List[List[int]]:
    """
    Generates the Cayley (multiplication) table for AVCA-⊕ for a given Omega.
    Elements are represented as 0 (for U_alg) and 1 to omega_val-1 (for DFIs).
    """
    if omega_val < 1:
        raise ValueError("Omega must be >= 1 for Cayley table generation.")
        
    set_py_avca_omega(omega_val)
    
    # Elements in S_alg_Omega for table generation (0 for U_alg, 1..Omega-1 for DFI)
    # These are the Python int values that will be mapped to PyAVCVal for py_avca_add
    s_alg_indices = list(range(omega_val)) 
    
    cayley_table: List[List[int]] = []

    print(f"\n--- Cayley Table for AVCA-⊕ with Ω = {omega_val} ---")
    print("Elements are represented as 0 (U_alg), 1 (DFI_1), ..., Omega-1 (DFI_{Omega-1})")
    
    header = "⊕ | " + " | ".join(map(str, s_alg_indices))
    print(header)
    print("-" * len(header))

    for i in s_alg_indices: # Row element
        row_values: List[int] = []
        # Map Python int index to the representation py_avca_add expects
        val_a_for_op: PyAVCVal = _ZERO_UNIO_py_repr if i == 0 else i
        
        row_str = f"{i} | "
        for j in s_alg_indices: # Column element
            val_b_for_op: PyAVCVal = _ZERO_UNIO_py_repr if j == 0 else j
            
            result_pyavcval = py_avca_add(val_a_for_op, val_b_for_op)
            
            # Convert result back to integer representation for the table
            result_int: int
            if result_pyavcval == _ZERO_UNIO_py_repr or result_pyavcval == _AREO_UNIO_py_repr:
                result_int = 0 # Map Unio result to 0
            elif isinstance(result_pyavcval, int):
                result_int = result_pyavcval
            else:
                # Should not happen if py_avca_add is correct
                raise ValueError(f"Unexpected result type from py_avca_add: {result_pyavcval}")
            
            row_values.append(result_int)
            row_str += f"{str(result_int).center(len(str(j)))} | " # Basic formatting
        
        print(row_str.strip())
        cayley_table.append(row_values)
        
    return cayley_table

# --- Main Execution ---
if __name__ == "__main__":
    # Set the Omega value for which you want to generate the table
    # The math LLM suggested Ω=6 as an interesting case.
    # For Ω > 2, the structure is not a loop due to the specific overflow rule.
    # However, the table for the defined operation can still be generated.
    
    omega_to_test = 6 
    # You can change this to 3, 4, 5, or other values.
    # For Ω=3, your py_avca_add based on V1 axioms for ⊕ gives:
    #   0 1 2
    # 0[0,1,2]
    # 1[1,2,0] (1+2=3 >= 3 -> U_alg=0)
    # 2[2,0,0] (2+1=3 >= 3 -> U_alg=0; 2+2=4 >= 3 -> U_alg=0)
    # This table for Ω=3 is NOT a Latin Square (row 2 has duplicate 0s), so not a loop.

    print(f"Generating Cayley table for AVCA-⊕ with Ω = {omega_to_test}.")
    print("Note: The AVCA-⊕ operation as defined by the V1 axioms")
    print("(U_alg=0, DFI_k=k; a+b if a+b<Ω, else U_alg for DFIs)")
    print("results in a commutative groupoid with identity.")
    print("For Ω > 2, it is generally NOT a loop (fails Latin Square property).")
    print("The table represents this specific operation.")


    table = generate_avca_oplus_cayley_table(omega_to_test)

    # Outputting the table in a format that might be easier to copy into GAP
    # GAP often uses 1-based indexing for elements, or lists of lists for tables.
    # This script generates a 0-indexed table [0...Omega-1].
    # If GAP needs 1-based elements [1...Omega], you'd need to map them.
    # For now, just printing the Python list of lists.
    print("\nCayley Table as Python list of lists (0-indexed):")
    # Example: For U_alg=0, DFI_1=1, DFI_2=2 etc.
    # table[i][j] will contain the result of i ⊕ j
    for i, row in enumerate(table):
        print(f"Row for element {i}: {row}")

    print("\nScript finished.")
    print("You can now use this table for further analysis, e.g., with GAP LOOPS.")
    print("Remember that for GAP, you might need to adjust indexing (e.g., to 1-based) ")
    print("and format the table as required by its 'IsIsomorphic' routines or table input methods.")