# H_E1_Entropy_Test.py
# Test for Hypothesis H-E1: Second-Law Inequality for Entropy
# H(out) >= max(H(in1), H(in2))
# Using "Best Combination" AVCA kernel.

from typing import Literal, Union, Any, List, Tuple, Dict
import math

# --- AVCA Core Components (from Appendix S.A "Best Combination") ---
_Omega_BC_H_E1: int = 0

class Unio_H_E1:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_H_E1 aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Unio_H_E1)
    def __hash__(self) -> int:
        return hash(f"Unio_H_E1_Algebraic_Singleton_{self.aspect}") # Aspect matters for H
    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"
    def __lt__(self, other): # For sorting in S_Omega generation
        if isinstance(other, Unio_H_E1):
            return self.aspect == "zero" and other.aspect == "areo"
        if isinstance(other, int): # DFI
            return True # Unios are "less than" DFIs in a canonical sort order sense
        return NotImplemented


ZERO_UNIO_H_E1 = Unio_H_E1("zero")
AREO_UNIO_H_E1 = Unio_H_E1("areo")
AVCVal_H_E1 = Union[int, Unio_H_E1]

def set_avca_omega_bc_H_E1(omega_value: int, verbose: bool = False):
    global _Omega_BC_H_E1
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_BC_H_E1 parameter must be an integer >= 1.")
    _Omega_BC_H_E1 = omega_value
    if verbose:
        print(f"H_E1 Test: Omega_BC_H_E1 set to {_Omega_BC_H_E1}")

def _check_val_bc_H_E1(x: AVCVal_H_E1, current_omega: int, op_name: str = "op", arg_name: str = "input"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega for {op_name} must be >= 1. Got: {current_omega!r}")
    if isinstance(x, Unio_H_E1): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid {arg_name} for {op_name}: {x!r} (type {type(x)}) for Ω={current_omega}.")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI {arg_name} for {op_name} when Omega=1: {x!r}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI {arg_name} for {op_name}: {x!r}. For Omega={current_omega}, DFI in [1, {current_omega-1}].")

# AVCA Operations ("Best Combination" Logic)
def avc_add_v1_1_bc_H_E1(a: AVCVal_H_E1, b: AVCVal_H_E1) -> AVCVal_H_E1:
    global _Omega_BC_H_E1
    if _Omega_BC_H_E1 == 0: raise ValueError("Global Omega_BC_H_E1 not set.")
    _check_val_bc_H_E1(a, _Omega_BC_H_E1, "add", "a"); _check_val_bc_H_E1(b, _Omega_BC_H_E1, "add", "b")
    if isinstance(a, Unio_H_E1): return b
    if isinstance(b, Unio_H_E1): return a
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < _Omega_BC_H_E1 else AREO_UNIO_H_E1

def avc_sub_v1_0_bc_H_E1(a: AVCVal_H_E1, b: AVCVal_H_E1) -> AVCVal_H_E1:
    global _Omega_BC_H_E1
    if _Omega_BC_H_E1 == 0: raise ValueError("Global Omega_BC_H_E1 not set.")
    _check_val_bc_H_E1(a, _Omega_BC_H_E1, "sub", "a"); _check_val_bc_H_E1(b, _Omega_BC_H_E1, "sub", "b")
    if isinstance(b, Unio_H_E1): return a
    if isinstance(a, Unio_H_E1): return AREO_UNIO_H_E1
    if a > b: return a - b # type: ignore
    else: return AREO_UNIO_H_E1

def avc_mul_v1_2_bc_H_E1(a: AVCVal_H_E1, b: AVCVal_H_E1) -> AVCVal_H_E1:
    global _Omega_BC_H_E1
    if _Omega_BC_H_E1 == 0: raise ValueError("Global Omega_BC_H_E1 not set.")
    _check_val_bc_H_E1(a, _Omega_BC_H_E1, "mul", "a"); _check_val_bc_H_E1(b, _Omega_BC_H_E1, "mul", "b")
    a_is_unio = isinstance(a, Unio_H_E1); b_is_unio = isinstance(b, Unio_H_E1)
    if a_is_unio or b_is_unio:
        a_is_areo = a_is_unio and a.aspect == "areo" # type: ignore
        b_is_areo = b_is_unio and b.aspect == "areo" # type: ignore
        return AREO_UNIO_H_E1 if a_is_areo or b_is_areo else ZERO_UNIO_H_E1
    else:
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < _Omega_BC_H_E1 else AREO_UNIO_H_E1

def _dfi_div_logic_bc_H_E1(a_dfi: int, b_dfi: int, current_omega: int) -> AVCVal_H_E1:
    if b_dfi == 0: raise ZeroDivisionError("Internal: DFI division by zero")
    quotient, remainder = divmod(a_dfi, b_dfi)
    return quotient if remainder == 0 and (1 <= quotient < current_omega) else AREO_UNIO_H_E1

def avc_div_AltD_Balanced_bc_H_E1(a: AVCVal_H_E1, b: AVCVal_H_E1) -> AVCVal_H_E1:
    global _Omega_BC_H_E1
    if _Omega_BC_H_E1 == 0: raise ValueError("Global Omega_BC_H_E1 not set.")
    _check_val_bc_H_E1(a, _Omega_BC_H_E1, "div", "a"); _check_val_bc_H_E1(b, _Omega_BC_H_E1, "div", "b")
    if isinstance(b, int): # Divisor is DFI
        if a is ZERO_UNIO_H_E1: return ZERO_UNIO_H_E1
        if a is AREO_UNIO_H_E1: return AREO_UNIO_H_E1
        if isinstance(a, int): return _dfi_div_logic_bc_H_E1(a,b,_Omega_BC_H_E1)
    elif isinstance(b, Unio_H_E1): # Divisor is Unio
        if isinstance(a, int): return AREO_UNIO_H_E1
        elif isinstance(a, Unio_H_E1):
            return AREO_UNIO_H_E1 if b.aspect == "areo" else a
    raise RuntimeError(f"Internal logic error in div_AltD with a={a!r}, b={b!r}")

# --- Entropy Function H ---
def H_entropy(val: AVCVal_H_E1, current_omega: int) -> float:
    if val is ZERO_UNIO_H_E1:
        return 0.0
    elif val is AREO_UNIO_H_E1:
        return 1.0
    elif isinstance(val, int): # DFI
        if current_omega <= 1 : return 0.0 # Should not happen if DFI val is valid for omega
        # Scaled DFI value to be between 0.1 and 0.8 (roughly)
        return 0.1 + (0.7 * (float(val) / float(current_omega)))
    else: # Should be an unhandled Unio object if aspects are dynamically created
        raise TypeError(f"Unknown AVCA value type for H_entropy: {val!r}")

# --- Test Runner for H-E1 ---
def test_H_E1_entropy_inequality(omega_to_test: int):
    print(f"\n--- Testing H-E1: Entropy Inequality for Omega={omega_to_test} ---")
    set_avca_omega_bc_H_E1(omega_to_test)

    s_omega: List[AVCVal_H_E1] = []
    if omega_to_test == 1:
        s_omega = [ZERO_UNIO_H_E1, AREO_UNIO_H_E1] # Algebraically one, but distinct for H
    else:
        s_omega = [ZERO_UNIO_H_E1, AREO_UNIO_H_E1] + list(range(1, omega_to_test))
    
    # Ensure unique objects if aspects are the primary distinguisher for H
    # For this H function, object identity ZU vs AU matters.
    # list(set(...)) won't work well if hash only uses algebraic U.
    # The s_omega list is fine as constructed.

    operations = {
        "Add(v1.1)": avc_add_v1_1_bc_H_E1,
        "Sub(v1.0)": avc_sub_v1_0_bc_H_E1,
        "Mul(v1.2)": avc_mul_v1_2_bc_H_E1,
        "Div(AltD)": avc_div_AltD_Balanced_bc_H_E1
    }

    all_ops_hold = True

    for op_name, op_func in operations.items():
        op_holds = True
        print(f"  Testing Operation: {op_name}")
        for in1 in s_omega:
            for in2 in s_omega:
                try:
                    # Need to handle Omega=1 DFI check specifically for op_func calls
                    # The _check_val_bc_H_E1 in each op_func should handle it.
                    out_op = op_func(in1, in2)
                    
                    h_out = H_entropy(out_op, omega_to_test)
                    h_in1 = H_entropy(in1, omega_to_test)
                    h_in2 = H_entropy(in2, omega_to_test)
                    max_h_in = max(h_in1, h_in2)

                    if not (h_out >= max_h_in):
                        # Add a small tolerance for floating point comparisons
                        if not math.isclose(h_out, max_h_in) and h_out < max_h_in:
                            print(f"    COUNTEREXAMPLE for {op_name}:")
                            print(f"      in1={in1!r} (H={h_in1:.3f}), in2={in2!r} (H={h_in2:.3f})")
                            print(f"      out={out_op!r} (H={h_out:.3f})")
                            print(f"      Condition H(out) >= max(H(in1), H(in2)) FAILED: {h_out:.3f} < {max_h_in:.3f}")
                            op_holds = False
                            all_ops_hold = False
                            break 
                except ValueError as e: # Catches _check_val errors if inputs are invalid for Omega
                    # This can happen if Omega=1 and a DFI from s_omega list is passed
                    if omega_to_test == 1 and isinstance(in1, int) or isinstance(in2, int):
                        pass # Expected for Omega=1 if trying to use DFI
                    else:
                        print(f"    ERROR during {op_name}({in1!r}, {in2!r}): {e}")
                        op_holds = False; all_ops_hold = False; break
                except Exception as e:
                    print(f"    UNEXPECTED ERROR during {op_name}({in1!r}, {in2!r}): {e}")
                    op_holds = False; all_ops_hold = False; break
            if not op_holds: break
        
        if op_holds:
            print(f"    Property H(out) >= max(H(in1), H(in2)) HOLDS for {op_name}.")

    return all_ops_hold

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_E1_Entropy_Test: ======")
    
    omegas_to_test_H_E1 = [3, 4] # Test for a couple of small Omegas

    overall_H_E1_holds = True
    for omega_val in omegas_to_test_H_E1:
        result = test_H_E1_entropy_inequality(omega_val)
        if not result:
            overall_H_E1_holds = False
            print(f"H-E1 FAILED for Omega={omega_val} with the current H function.")
            # As per hypothesis: if fails, refine H or entropy narrative is false.
            # For this quick exploration, we stop on first failure for an Omega.
            break 
        else:
            print(f"H-E1 HOLDS for Omega={omega_val} with the current H function.")
            
    print("\n--- Overall Summary of H-E1 Test ---")
    if overall_H_E1_holds:
        print("Hypothesis H-E1 (Second-Law Inequality) appears to HOLD for all tested Omegas with the defined H function.")
    else:
        print("Hypothesis H-E1 (Second-Law Inequality) FAILED for at least one Omega with the defined H function.")
        print("This suggests either the H function needs refinement, or the entropy narrative might not apply this simply.")

    print("\n====== H_E1_Entropy_Test Script Finished ======")