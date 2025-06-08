import itertools
import sympy as sp
from typing import List, Tuple, Any, Optional

# --- Python AVCA Kernel (Adapted from SMT Proof Script V12 & previous defect script) ---
_Omega_py: Optional[int] = None
_ZERO_UNIO_py_repr = "Unio('zero')" # Represents algebraic U_alg
_AREO_UNIO_py_repr = "Unio('areo')"   # Represents algebraic U_alg
PyAVCVal = Any 

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
    if omega == 1 and isinstance(x, int):
        raise ValueError(f"DFI value {x} is invalid for {op_name}/{arg_name} when Python AVCA Omega is 1.")
    if omega > 1 and not (1 <= x < omega):
        raise ValueError(f"DFI value {x} is out of range [1, {omega-1}] for {op_name}/{arg_name} for Python AVCA Omega={omega}.")

def py_avca_add(a: PyAVCVal, b: PyAVCVal) -> PyAVCVal:
    """Python AVCA Addition (⊕) - 'avc_add_v1.1' logic."""
    if _Omega_py is None:
        raise ValueError("Python AVCA Omega not set. Call set_py_avca_omega(value) first.")
    _check_py_val(a, _Omega_py, "py_avca_add", "a")
    _check_py_val(b, _Omega_py, "py_avca_add", "b")

    if a == _ZERO_UNIO_py_repr or a == _AREO_UNIO_py_repr: return b
    if b == _ZERO_UNIO_py_repr or b == _AREO_UNIO_py_repr: return a
    
    val_a: int = a
    val_b: int = b
    dfi_sum = val_a + val_b
    return dfi_sum if dfi_sum < _Omega_py else _AREO_UNIO_py_repr

def brute_force_failing_triples(omega_val: int) -> int:
    """
    Counts non-associative triples for (S_omega_alg, py_avca_add)
    using brute-force enumeration.
    """
    if omega_val < 3: # Associativity holds for Omega = 1, 2
        return 0
        
    set_py_avca_omega(omega_val)
    s_alg_elements = [_ZERO_UNIO_py_repr] + list(range(1, omega_val))
    non_associative_count = 0

    for a_val in s_alg_elements:
        for b_val in s_alg_elements:
            for c_val in s_alg_elements:
                try:
                    lhs = py_avca_add(py_avca_add(a_val, b_val), c_val)
                    rhs = py_avca_add(a_val, py_avca_add(b_val, c_val))

                    lhs_is_unio = (lhs == _ZERO_UNIO_py_repr or lhs == _AREO_UNIO_py_repr)
                    rhs_is_unio = (rhs == _ZERO_UNIO_py_repr or rhs == _AREO_UNIO_py_repr)

                    is_associative = False
                    if lhs_is_unio and rhs_is_unio: is_associative = True
                    elif lhs == rhs: is_associative = True
                    
                    if not is_associative:
                        non_associative_count += 1
                except Exception as e:
                    print(f"Error in brute_force_failing_triples for Ω={omega_val}, triplet ({a_val},{b_val},{c_val}): {e}")
                    non_associative_count +=1 # Count as failure
    return non_associative_count

def analyze_defect_density_with_formula(
    max_omega_for_brute_force_check: int = 30, 
    max_omega_for_formula_table: int = 100
    ):
    """
    Analyzes the ⊕-associativity defect density using the closed-form formula,
    with an optional brute-force sanity check for smaller Omega values.
    """
    print("--- Task ②: Exact Defect-Density Curve Analysis (Revised Asymptotic Printout & Brute-Force Guard) ---")
    
    Omega_sym = sp.symbols('Ω', positive=True, integer=True)
    f_exact_formula = (sp.Rational(2,3) * Omega_sym * (Omega_sym - 1) * (Omega_sym - 2))
    print(f"\nExact formula for number of failing triples f(Ω): {f_exact_formula}")

    density_formula_symbolic = f_exact_formula / (Omega_sym**3)
    simplified_density = sp.simplify(density_formula_symbolic)
    print(f"Symbolic density d(Ω) = f(Ω)/Ω³ simplifies to: {simplified_density}")
    
    # Asymptotic form as suggested: d(Ω) = 2/3 – 2/Ω + 4/(3Ω²) -> limit 2/3
    # This can be obtained from series expansion or by direct algebraic manipulation
    # For printing, we can construct the string or rely on Sympy's series output
    asymptotic_series_terms = sp.series(simplified_density, Omega_sym, x0=sp.oo, n=3).removeO()
    print(f"Asymptotic form (series expansion for large Ω): d(Ω) = {asymptotic_series_terms}  -> limit 2/3")

    print(f"\nSanity-checking formula against brute-force for Ω up to {max_omega_for_brute_force_check}:")
    
    sanity_check_data = []
    all_sanity_checks_match = True

    # Loop for sanity checking (brute-force vs formula)
    # Only run brute force up to 'max_omega_for_brute_force_check'
    # Ensure the loop doesn't try to check for Omega < 3
    actual_brute_force_check_limit = max(2, max_omega_for_brute_force_check)

    for n_val in range(3, actual_brute_force_check_limit + 1):
        fails_from_formula_exact = f_exact_formula.subs(Omega_sym, n_val)
        fails_from_formula = int(fails_from_formula_exact) # Formula should yield integer

        fails_brute_force = brute_force_failing_triples(n_val)
        match = (fails_from_formula == fails_brute_force)
        
        print(f"  Ω={n_val}: Formula_f(Ω)={fails_from_formula}, BruteForce_f(Ω)={fails_brute_force} -> {'Match ✅' if match else 'Mismatch ❌'}")
        if not match:
            all_sanity_checks_match = False
        sanity_check_data.append((n_val, fails_from_formula, fails_brute_force, n_val**3, fails_from_formula/(n_val**3) if n_val > 0 else 0))

    if all_sanity_checks_match and actual_brute_force_check_limit >=3 :
        print(f"\nFormula for f(Ω) matches brute-force counts for all tested Ω values (up to Ω={actual_brute_force_check_limit})! 👍")
    elif actual_brute_force_check_limit < 3:
        print("\nBrute-force sanity check not run for Ω < 3.")
    else:
        print(f"\nFormula for f(Ω) shows mismatches with brute-force counts for some Ω values (up to Ω={actual_brute_force_check_limit})! Needs review. 👎")

    print("\nData table using ONLY the closed-form formula:")
    print(f"(Ω from 3 to {max_omega_for_formula_table})")
    print(f"{'Ω':<5} | {'Failing f(Ω)':<15} | {'Total Ω³':<15} | {'Density d(Ω)':<15}")
    print("-" * 55)
    
    # Loop for generating table data using the formula
    # Ensure loop starts from 3
    actual_formula_table_start = max(3, min(3, max_omega_for_formula_table + 1) ) 

    for n_val_ext in range(actual_formula_table_start, max_omega_for_formula_table + 1):
        f_val_exact = f_exact_formula.subs(Omega_sym, n_val_ext)
        f_val = int(f_val_exact) # Should be integer
        total_triples_ext = n_val_ext**3
        density_val_exact = simplified_density.subs(Omega_sym, n_val_ext)
        density_val = float(density_val_exact)
        print(f"{n_val_ext:<5} | {f_val:<15} | {total_triples_ext:<15} | {density_val:<15.4f}")
    print("-" * 55)

# --- Main Execution ---
if __name__ == "__main__":
    # Configuration:
    # max_omega_for_brute_force_check: How far to run the slow brute-force comparison.
    #                                   The math LLM suggests up to ~30.
    # max_omega_for_formula_table: How far to generate the data table using the fast formula.
    #                                 You ran it up to 100/150 previously.
    
    BRUTE_FORCE_CHECK_LIMIT = 50  # As suggested by math LLM
    FORMULA_TABLE_LIMIT = 10000     # Example: like your previous "hardcore" run table
                                  # Set to 150 if you want to match math LLM's table header

    analyze_defect_density_with_formula(
        max_omega_for_brute_force_check=BRUTE_FORCE_CHECK_LIMIT,
        max_omega_for_formula_table=FORMULA_TABLE_LIMIT
    )
    
    print("\nScript finished.")
    print(f"The brute-force check for f(Ω) was performed up to Ω={BRUTE_FORCE_CHECK_LIMIT}.")
    print(f"The data table using the formula was generated up to Ω={FORMULA_TABLE_LIMIT}.")
    print("With these tweaks, Task ② is effectively complete for numerical analysis.")