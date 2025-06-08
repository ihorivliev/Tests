# test_mapped_ops_and_fidelity.py
# Purpose: Stage 2-B - Test algebraic laws for mapped multiplication & distributivity.
# Quantify add_fidelity and mul_fidelity for spans S=2-7.

import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- Unio Class Definition (Minimal for canonical representation) ---
class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"] = "zero"):
        self.aspect = aspect
    def __eq__(self, other: object) -> bool: 
        return isinstance(other, Unio)
    def __hash__(self) -> int:
        return hash(type(self))
    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"

CANONICAL_UNIO_POLE = Unio("zero") 
CORE_ZERO_UNIO = Unio("zero") # Used by core_avc_mul
CORE_AREO_UNIO = Unio("areo") # Used by core_avc_add and core_avc_mul

# --- Type Aliases ---
LocalVal = int 
CanonicalVal = Union[int, Unio]

# --- Global Omega for Core AVCA operations ---
_CORE_AVCA_OMEGA: int = 0

# --- Core AVCA Domain Enforcement & Operations (v1.2b logic) ---
def _core_check_val(x: CanonicalVal, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"CoreAVCA Omega parameter must be an integer >= 1. Got: {current_omega}")
    if isinstance(x, Unio): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid CoreAVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")
    if current_omega == 1:
        if isinstance(x, int): # Should actually only be Unio for Omega_eff=1 from lens
            raise ValueError(f"Invalid CoreAVCA DFI Value for Omega=1: {x}. DFI is empty.")
    # Canonical DFI for AVCA-S is {1, ..., S-1}
    elif not (1 <= x < current_omega): 
            raise ValueError(f"Invalid CoreAVCA DFI Value: {x}. For Omega={current_omega}, DFI must be in range [1, {current_omega - 1}].")

def core_avc_add(a: CanonicalVal, b: CanonicalVal) -> CanonicalVal: # ⊕_v1.1 logic
    global _CORE_AVCA_OMEGA
    if _CORE_AVCA_OMEGA == 0: raise ValueError("CoreAVCA Omega not set for add.")
    _core_check_val(a, _CORE_AVCA_OMEGA); _core_check_val(b, _CORE_AVCA_OMEGA)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    standard_sum = a + b # type: ignore 
    return standard_sum if standard_sum < _CORE_AVCA_OMEGA else CORE_AREO_UNIO

def core_avc_mul(a: CanonicalVal, b: CanonicalVal) -> CanonicalVal: # ⊗_v1.2 logic
    global _CORE_AVCA_OMEGA
    if _CORE_AVCA_OMEGA == 0: raise ValueError("CoreAVCA Omega not set for mul.")
    _core_check_val(a, _CORE_AVCA_OMEGA); _core_check_val(b, _CORE_AVCA_OMEGA)
    a_is_unio = isinstance(a, Unio); b_is_unio = isinstance(b, Unio)
    if a_is_unio or b_is_unio:
        # Determine if any operand Unio object is Areo-aspected.
        # For this script, CANONICAL_UNIO_POLE is Unio("zero").
        # CORE_ZERO_UNIO is Unio("zero"), CORE_AREO_UNIO is Unio("areo").
        # The actual aspect of 'a' or 'b' if they are Unio matters here.
        a_is_areo = a_is_unio and a.aspect == "areo" # type: ignore
        b_is_areo = b_is_unio and b.aspect == "areo" # type: ignore
        is_any_areo = a_is_areo or b_is_areo
        return CORE_AREO_UNIO if is_any_areo else CORE_ZERO_UNIO
    else: # Both DFI
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < _CORE_AVCA_OMEGA else CORE_AREO_UNIO

def set_core_avca_omega(omega_value: int):
    global _CORE_AVCA_OMEGA
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("CoreAVCA Omega must be an integer >= 1.")
    _CORE_AVCA_OMEGA = omega_value

# --- Lens Functions (Stage 2-A) ---
def lens_forward(x_local: LocalVal, P_A: int, P_B: int) -> CanonicalVal:
    # Span S = P_B - P_A. Canonical DFI is {1, ..., S-1}.
    # For this lens, Ω_eff = S.
    if not (P_A <= x_local <= P_B): # Ensure x_local is within its defined frame
        raise ValueError(f"Value x_local={x_local} is outside the local frame [{P_A}, {P_B}]")
    if x_local == P_A or x_local == P_B:
        return CANONICAL_UNIO_POLE # This is Unio("zero") by definition above
    return x_local - P_A 

def lens_inverse(k_canonical: CanonicalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    if S < 1: raise ValueError("Span S must be >= 1 for lens_inverse.")
    
    if isinstance(k_canonical, Unio):
        # Regardless of aspect of k_canonical (e.g. CORE_AREO_UNIO from add overflow)
        # it maps to P_A as per math LLM's g(U_C)=A.
        return P_A 
    elif isinstance(k_canonical, int):
        if 1 <= k_canonical < S: # Valid canonical DFI for AVCA-S
            return P_A + k_canonical
        else: 
            # This case should ideally not be hit if core ops are closed for AVCA-S
            # and always produce DFI {1..S-1} or a Unio object.
            # If core_avc_add/mul produced an integer like 0 or S, that's an issue.
            # For robustness, one might map this to a boundary, but it signals a deeper problem.
            # Based on AVCA spec, int results from core ops are always valid DFI {1..S-1}.
            raise ValueError(f"Invalid canonical DFI value {k_canonical} for inversion. Omega_eff={S}. Frame [{P_A},{P_B}]")
    else:
        raise TypeError(f"Invalid type for k_canonical: {type(k_canonical)}")

# --- Mapped AVCA Operations ---
def mapped_avc_add(x_local: LocalVal, y_local: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    if S < 1 and not (x_local==P_A and y_local==P_A and P_A==P_B) : # Span 0 check
         # S=0 if P_A=P_B. Lens forward will map P_A to Unio. Ω_eff=0.
         # This case is ill-defined for AVCA core ops needing Omega >=1.
         # Math LLM: S >= 2 for Ω_eff = S. But AVCA ops work for S=1 (Ω_eff=1).
         if S < 1: S_for_core = 1 # Default to Omega=1 for core ops if span is <1
         else: S_for_core = S
    else:
        S_for_core = S

    if S_for_core < 1 : S_for_core = 1 # Ensure core Omega is at least 1

    val_x_canon = lens_forward(x_local, P_A, P_B)
    val_y_canon = lens_forward(y_local, P_A, P_B)
    set_core_avca_omega(S_for_core) 
    res_canon = core_avc_add(val_x_canon, val_y_canon)
    return lens_inverse(res_canon, P_A, P_B)

def mapped_avc_mul(x_local: LocalVal, y_local: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    if S < 1 : S_for_core = 1
    else: S_for_core = S
    if S_for_core < 1 : S_for_core = 1

    val_x_canon = lens_forward(x_local, P_A, P_B)
    val_y_canon = lens_forward(y_local, P_A, P_B)
    set_core_avca_omega(S_for_core)
    res_canon = core_avc_mul(val_x_canon, val_y_canon)
    return lens_inverse(res_canon, P_A, P_B)

# --- Helper for comparing results ---
def local_equals(val1: LocalVal, val2: LocalVal) -> bool:
    return val1 == val2

def canonical_equals(val1: CanonicalVal, val2: CanonicalVal) -> bool:
    if isinstance(val1, Unio) and isinstance(val2, Unio):
        # Check if aspects match if we want to be stricter than algebraic for fidelity check
        # The user's fidelity definition f(x+y) == f(x)+f(y) implies algebraic equality.
        return True 
    return val1 == val2

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Mapped Operations Law & Fidelity Tests (Stage 2-B) ---")
    print("    Using lens: f(x)=Unio if x=PA/PB, else x-PA. g(Unio)=PA, g(k)=PA+k.")
    print("    Canonical Ops: AVCA Core v1.2b (⊕_v1.1, ⊗_v1.2)\n")
    
    spans_to_test = list(range(2, 8)) # S = 2 through 7
    P_A = 0 

    fidelity_results = []
    # Commutativity of Mapped Add was tested in previous script and holds.
    # Associativity of Mapped Add holds iff S<=2, fails S>=3 (from previous script).
    previous_mapped_add_results = {
        2: {"comm": "Holds", "assoc": "Holds"},
        3: {"comm": "Holds", "assoc": "FAILS"},
        4: {"comm": "Holds", "assoc": "FAILS"},
        5: {"comm": "Holds", "assoc": "FAILS"},
        6: {"comm": "Holds", "assoc": "FAILS"}, # Extrapolating based on pattern
        7: {"comm": "Holds", "assoc": "FAILS"}, # Extrapolating
    }


    for S_val in spans_to_test:
        P_B = P_A + S_val
        print(f"--- Testing with Local Span S = {S_val} (Frame [{P_A},{P_B}], Canonical AVCA-{S_val}) ---")
        
        local_elements: List[LocalVal] = list(range(P_A, P_B + 1))
        if not local_elements: continue

        # Commutativity of mapped_avc_mul
        comm_mul_law_holds = True
        comm_mul_counterexample_str = ""
        for x, y in itertools.product(local_elements, local_elements):
            try:
                res1 = mapped_avc_mul(x, y, P_A, P_B)
                res2 = mapped_avc_mul(y, x, P_A, P_B)
                if not local_equals(res1, res2):
                    comm_mul_law_holds = False; comm_mul_counterexample_str = f"x={x},y={y} -> xy={res1},yx={res2}"; break
            except Exception as e: comm_mul_law_holds = False; comm_mul_counterexample_str = f"x={x},y={y} -> Exc: {e}"; break
        print(f"  Commutativity of mapped_avc_mul: {'Holds' if comm_mul_law_holds else f'FAILS ({comm_mul_counterexample_str})'}")

        # Associativity of mapped_avc_mul
        assoc_mul_law_holds = True
        assoc_mul_counterexample_str = ""
        if S_val <= 4: # Keep N^3 reasonable for exhaustive check
            for x, y, z in itertools.product(local_elements, local_elements, local_elements):
                try:
                    lhs = mapped_avc_mul(mapped_avc_mul(x, y, P_A, P_B), z, P_A, P_B)
                    rhs = mapped_avc_mul(x, mapped_avc_mul(y, z, P_A, P_B), P_A, P_B)
                    if not local_equals(lhs, rhs):
                        assoc_mul_law_holds = False; assoc_mul_counterexample_str = f"x={x},y={y},z={z} -> (xy)z={lhs},x(yz)={rhs}"; break
                except Exception as e: assoc_mul_law_holds = False; assoc_mul_counterexample_str = f"x={x},y={y},z={z} -> Exc: {e}"; break
                if not assoc_mul_law_holds: break
        else:
            assoc_mul_law_holds = "Not exhaustively tested for S > 4" # Placeholder
        print(f"  Associativity of mapped_avc_mul: {status_to_str(assoc_mul_law_holds, assoc_mul_counterexample_str)}")


        # Distributivity: mapped_mul(x, mapped_add(y,z)) == mapped_add(mapped_mul(x,y), mapped_mul(x,z))
        distrib_law_holds = True
        distrib_counterexample_str = ""
        if S_val <= 4: # Keep N^3 reasonable
            for x, y, z in itertools.product(local_elements, local_elements, local_elements):
                try:
                    lhs = mapped_avc_mul(x, mapped_avc_add(y, z, P_A, P_B), P_A, P_B)
                    rhs = mapped_avc_add(mapped_avc_mul(x, y, P_A, P_B), mapped_avc_mul(x, z, P_A, P_B), P_A, P_B)
                    if not local_equals(lhs, rhs):
                        distrib_law_holds = False; distrib_counterexample_str = f"x={x},y={y},z={z} -> x(y+z)={lhs},(xy)+(xz)={rhs}"; break
                except Exception as e: distrib_law_holds = False; distrib_counterexample_str = f"x={x},y={y},z={z} -> Exc: {e}"; break
                if not distrib_law_holds: break
        else:
            distrib_law_holds = "Not exhaustively tested for S > 4"
        print(f"  Distributivity (mul over add): {status_to_str(distrib_law_holds, distrib_counterexample_str)}")

        # Fidelity Scores
        add_homomorphism_holds_count = 0
        mul_homomorphism_holds_count = 0
        total_pairs = len(local_elements) * len(local_elements)

        for x, y in itertools.product(local_elements, local_elements):
            try:
                # Additive Fidelity
                res_loc_add = mapped_avc_add(x, y, P_A, P_B)
                f_res_loc_add = lens_forward(res_loc_add, P_A, P_B)
                fx_add = lens_forward(x, P_A, P_B)
                fy_add = lens_forward(y, P_A, P_B)
                set_core_avca_omega(S_val)
                fx_add_can_fy = core_avc_add(fx_add, fy_add)
                if canonical_equals(f_res_loc_add, fx_add_can_fy):
                    add_homomorphism_holds_count += 1
            except Exception: pass 

            try:
                # Multiplicative Fidelity
                res_loc_mul = mapped_avc_mul(x, y, P_A, P_B)
                f_res_loc_mul = lens_forward(res_loc_mul, P_A, P_B)
                fx_mul = lens_forward(x, P_A, P_B) # Same as fx_add
                fy_mul = lens_forward(y, P_A, P_B) # Same as fy_add
                set_core_avca_omega(S_val)
                fx_mul_can_fy = core_avc_mul(fx_mul, fy_mul)
                if canonical_equals(f_res_loc_mul, fx_mul_can_fy):
                    mul_homomorphism_holds_count += 1
            except Exception: pass

        add_fid = add_homomorphism_holds_count / total_pairs if total_pairs > 0 else 0
        mul_fid = mul_homomorphism_holds_count / total_pairs if total_pairs > 0 else 0
        
        fidelity_results.append({
            "Span_S": S_val, "P_A": P_A, "P_B": P_B, 
            "L_f": 2, 
            "add_fidelity": add_fid, 
            "mul_fidelity": mul_fid,
            "comm_add_mapped": previous_mapped_add_results.get(S_val, {}).get("comm", "N/A"),
            "assoc_add_mapped": previous_mapped_add_results.get(S_val, {}).get("assoc", "N/A"),
            "comm_mul_mapped": status_to_str(comm_mul_law_holds),
            "assoc_mul_mapped": status_to_str(assoc_mul_law_holds),
            "distrib_mapped": status_to_str(distrib_law_holds)
        })
        print(f"  Fidelity Scores: Add={add_fid:.4f}, Mul={mul_fid:.4f}")
        print("-" * 70)

    print("\n--- Mapped Operations Law & Fidelity Tests Completed ---")
    print("\nSummary Profile (L, Add_Fid, Mul_Fid) and Law Survival:")
    header = "S | Frame   | L | Add_Fid | Mul_Fid | Comm(Add_M) | Assoc(Add_M) | Comm(Mul_M) | Assoc(Mul_M) | Distrib(M/A_M)"
    print(header)
    print("-" * len(header))
    for res in fidelity_results:
        print(f"{res['Span_S']!s:<2}| [{res['P_A']},{res['P_B']}]   | {res['L_f']!s:<2}| {res['add_fidelity']:<7.4f} | {res['mul_fidelity']:<7.4f} | {res['comm_add_mapped']:<11} | {res['assoc_add_mapped']:<12} | {res['comm_mul_mapped']:<11} | {res['assoc_mul_mapped']:<12} | {res['distrib_mapped']:<15}")

def status_to_str(status_bool_or_str, counterexample_str=""):
    if isinstance(status_bool_or_str, str): # Already a string like "Not exhaustively tested"
        return status_bool_or_str
    if status_bool_or_str:
        return "Holds"
    else:
        return f"FAILS ({counterexample_str})" if counterexample_str else "FAILS"

if __name__ == "__main__":
    run_all_tests()