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

def analyze_defect_density_with_formula():
    """
    Analyzes the ⊕-associativity defect density using the provided closed-form formula.
    """
    print("--- Task ②: Exact Defect-Density Curve Analysis (Revised Asymptotic Printout) ---")
    
    # Define Omega as a Sympy symbol
    Omega_sym = sp.symbols('Ω', positive=True, integer=True)

    # Candidate formula for the number of failing triples
    # f(Ω) = (2/3) * Ω * (Ω-1) * (Ω-2)
    f_exact_formula = (sp.Rational(2,3) * Omega_sym * (Omega_sym - 1) * (Omega_sym - 2))
    print(f"\nProposed formula for number of failing triples f(Ω): {f_exact_formula}")

    # Density formula d(Ω) = f(Ω) / Ω^3
    density_formula_symbolic = f_exact_formula / (Omega_sym**3)
    simplified_density = sp.simplify(density_formula_symbolic)
    print(f"Symbolic density d(Ω) = f(Ω)/Ω³ simplifies to: {simplified_density}")
    
    # Asymptotic behavior - revised printout
    # The math LLM suggests printing: d(Ω) = 2/3 – 2/Ω + 4/(3Ω²)
    # We can get this by expanding the simplified_density or using series expansion.
    # Using series expansion for large Ω (around oo), showing terms up to Ω^-2
    # n=3 in sp.series gives terms up to (1/Ω)^(3-1) = (1/Ω)^2
    asymptotic_series = sp.series(simplified_density, Omega_sym, x0=sp.oo, n=3).removeO()
    print(f"Asymptotic form of d(Ω) (series expansion for large Ω): {asymptotic_series}")
    # This should print: 2/3 - 2/Ω + 4/(3*Ω**2)
    # which matches the math LLM's expectation.

    print("\nSanity-checking formula against brute-force for small Ω values:")
    data_from_formula = []
    # You can adjust max_omega_check; set to a small number for quick test,
    # larger (like your Ω=100 run) for thorough validation if time permits.
    max_omega_check = 100 

    all_match = True
    for n_val in range(3, max_omega_check + 1):
        fails_formula_exact = f_exact_formula.subs(Omega_sym, n_val)
        if not fails_formula_exact.is_integer:
            print(f"Warning: Formula for f({n_val}) did not result in an integer: {fails_formula_exact}")
            fails_from_formula = round(float(fails_formula_exact))
        else:
            fails_from_formula = int(fails_formula_exact)
            
        fails_brute_force = brute_force_failing_triples(n_val)
        
        match = (fails_from_formula == fails_brute_force)
        print(f"  Ω={n_val}: Formula_f(Ω)={fails_from_formula}, BruteForce_f(Ω)={fails_brute_force} -> {'Match ✅' if match else 'Mismatch ❌'}")
        if not match:
            all_match = False
        data_from_formula.append((n_val, fails_from_formula, fails_brute_force, n_val**3, fails_from_formula/(n_val**3) if n_val > 0 else 0))

    if all_match:
        print(f"\nFormula for f(Ω) matches brute-force counts for tested Ω values (up to Ω={max_omega_check})! 👍")
    else:
        print(f"\nFormula for f(Ω) shows mismatches with brute-force counts for some Ω values! Needs review. 👎")

    print("\nData based on the closed-form formula f(Ω): (Ω, Failing Triples, Total Triples, Density)")
    # Print data for a few values using the formula, as the brute-force check is now separate
    # (or you can iterate through data_from_formula if you want to show the brute_force_fails column too)
    # For consistency with your previous extended output, let's use data_from_formula
    # which now only goes up to max_omega_check.
    # If you want the table up to 100 using the formula (without brute force for each),
    # you'd generate it separately like this:
    
    print("(This table shows data from formula up to the sanity check limit)")
    for n_val_print, f_form, _, total_t, dens_form in data_from_formula: 
        print(f"({n_val_print}, {f_form}, {total_t}, {dens_form:.4f})")

    # To generate extended table using ONLY the formula (fast):
    print("\nExtended data table using ONLY the closed-form formula (Ω=3 to 20):")
    print(f"{'Ω':<5} | {'Failing f(Ω)':<15} | {'Total Ω³':<15} | {'Density d(Ω)':<15}")
    print("-" * 55)
    for n_val_ext in range(3, 21): # e.g., up to 20
        f_val = f_exact_formula.subs(Omega_sym, n_val_ext)
        total_triples_ext = n_val_ext**3
        density_val = simplified_density.subs(Omega_sym, n_val_ext)
        print(f"{n_val_ext:<5} | {int(f_val):<15} | {total_triples_ext:<15} | {float(density_val):<15.4f}")
    print("-" * 55)


# --- Main Execution ---
if __name__ == "__main__":
    analyze_defect_density_with_formula()
    
    print("\nScript finished.")
    print("The asymptotic form of d(Ω) should now clearly show the series expansion.")