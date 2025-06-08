import itertools
from typing import List, Dict, Tuple, Callable, Any, Optional

# --- Python AVCA Kernel (from previous script, unchanged) ---
_Omega_py: Optional[int] = None
_ZERO_UNIO_py_repr = "Unio('zero')" 
_AREO_UNIO_py_repr = "Unio('areo')" 
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
    if omega > 1 and not (1 <= x < omega): 
        raise ValueError(f"DFI value {x} is out of range [1, {omega-1}] for {op_name}/{arg_name} for Python AVCA Omega={omega}.")

def py_avca_add(a: PyAVCVal, b: PyAVCVal) -> PyAVCVal:
    if _Omega_py is None: raise ValueError("Python AVCA Omega not set.")
    a_is_unio = (a == _ZERO_UNIO_py_repr or a == _AREO_UNIO_py_repr)
    b_is_unio = (b == _ZERO_UNIO_py_repr or b == _AREO_UNIO_py_repr)
    if a_is_unio: return b
    if b_is_unio: return a
    val_a: int = a; val_b: int = b
    _check_py_val(val_a, _Omega_py, "py_avca_add", "a_int")
    _check_py_val(val_b, _Omega_py, "py_avca_add", "b_int")
    dfi_sum = val_a + val_b
    return dfi_sum if dfi_sum < _Omega_py else _AREO_UNIO_py_repr

def generate_avca_oplus_cayley_table(omega_val: int, verbose_print: bool = True) -> List[List[int]]:
    """
    Generates the 0-indexed Cayley table for AVCA-⊕.
    Elements are 0 (U_alg) to omega_val-1.
    """
    if omega_val < 1:
        raise ValueError("Omega must be >= 1 for Cayley table generation.")
    set_py_avca_omega(omega_val)
    s_alg_indices = list(range(omega_val)) 
    cayley_table: List[List[int]] = []

    if verbose_print:
        print(f"\n--- Generating 0-indexed Cayley Table for AVCA-⊕ with Ω = {omega_val} ---")
        header = "⊕ | " + " | ".join(map(str, s_alg_indices))
        print(header)
        print("-" * len(header))

    for i in s_alg_indices: 
        row_values: List[int] = []
        val_a_for_op: PyAVCVal = _ZERO_UNIO_py_repr if i == 0 else i
        row_str = f"{i} | " if verbose_print else ""
        for j in s_alg_indices: 
            val_b_for_op: PyAVCVal = _ZERO_UNIO_py_repr if j == 0 else j
            result_pyavcval = py_avca_add(val_a_for_op, val_b_for_op)
            result_int: int
            if result_pyavcval == _ZERO_UNIO_py_repr or result_pyavcval == _AREO_UNIO_py_repr:
                result_int = 0 
            elif isinstance(result_pyavcval, int):
                result_int = result_pyavcval
            else:
                raise ValueError(f"Unexpected result type from py_avca_add: {result_pyavcval}")
            row_values.append(result_int)
            if verbose_print: row_str += f"{str(result_int).center(len(str(j)))} | "
        if verbose_print: print(row_str.strip())
        cayley_table.append(row_values)
    if verbose_print: print("-" * len(header) if header else "")
    return cayley_table

# --- New Function to Convert and Print for GAP ---
def format_table_for_gap(cayley_table_0_indexed: List[List[int]], omega_val: int) -> str:
    """
    Converts a 0-indexed Cayley table to a 1-indexed table and formats it as a GAP string.
    In the 1-indexed table, element '1' will correspond to original '0' (U_alg).
    """
    if not cayley_table_0_indexed or len(cayley_table_0_indexed) != omega_val:
        return "Error: Invalid 0-indexed table provided."

    # Create 1-indexed table by adding 1 to each element
    # If original table has U_alg=0, DFI_1=1, ..., DFI_omega-1 = omega-1
    # New table will have U_alg=1, DFI_1=2, ..., DFI_omega-1 = omega
    cayley_table_1_indexed: List[List[int]] = []
    for i in range(omega_val):
        new_row = []
        for j in range(omega_val):
            original_value = cayley_table_0_indexed[i][j]
            new_row.append(original_value + 1) # Shift all values by +1
        cayley_table_1_indexed.append(new_row)

    # Format for GAP: list of lists, e.g., "[[1,2,3],[2,3,1],[3,1,2]];"
    gap_string = "["
    for i, row in enumerate(cayley_table_1_indexed):
        gap_string += "[" + ",".join(map(str, row)) + "]"
        if i < len(cayley_table_1_indexed) - 1:
            gap_string += ",\n " # Newline and space for readability for next row
        else:
            gap_string += "\n"
    gap_string += "];"
    
    return gap_string

# --- Main Execution ---
if __name__ == "__main__":
    omega_to_test = 6 
    # You can change this to 3, 4, 5, or other values.
    
    print(f"Generating Cayley table for AVCA-⊕ with Ω = {omega_to_test}.")
    
    # Generate the 0-indexed table (this will also print it in human-readable form)
    table_0_indexed = generate_avca_oplus_cayley_table(omega_to_test, verbose_print=True)

    # Convert to 1-indexed and format for GAP
    gap_formatted_table = format_table_for_gap(table_0_indexed, omega_to_test)

    print("\nCayley Table in GAP format (1-indexed, where 1 represents original U_alg=0):")
    print(gap_formatted_table)
    
    print(f"\nTo use in GAP (assuming elements are 1..{omega_to_test}):")
    print(f"  L := LoopByCayleyTable({gap_formatted_table});")
    print(f"  # Or for a general magma if it's not a loop:")
    print(f"  M := MagmaByCayleyTable({gap_formatted_table});")
    print(f"  SetIdentification(M, [1..{omega_to_test}]); # If needed")
    print(f"  IsLoop(M); # Check if GAP considers it a loop")
    print(f"  # Then potentially use IsIsomorphicLoop(M, OtherLoopFromLibrary);")

    print("\nScript finished.")