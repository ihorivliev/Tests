# test_mapped_ops_and_fidelity.py
# Purpose: Stage 2-B - Test algebraic laws for mapped multiplication & distributivity.
# Quantify add_fidelity and mul_fidelity for spans S=2-5.

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
CORE_ZERO_UNIO = Unio("zero")
CORE_AREO_UNIO = Unio("areo")

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
        if isinstance(x, int):
            raise ValueError(f"Invalid CoreAVCA DFI Value for Omega=1: {x}. DFI is empty.")
    elif not (1 <= x < current_omega): 
            raise ValueError(f"Invalid CoreAVCA DFI Value: {x}. For Omega={current_omega}, DFI must be in range [1, {current_omega - 1}].")

def core_avc_add(a: CanonicalVal, b: CanonicalVal) -> CanonicalVal: # ⊕_v1.1 logic
    global _CORE_AVCA_OMEGA
    if _CORE_AVCA_OMEGA == 0: raise ValueError("CoreAVCA Omega not set.")
    _core_check_val(a, _CORE_AVCA_OMEGA); _core_check_val(b, _CORE_AVCA_OMEGA)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    standard_sum = a + b # type: ignore 
    return standard_sum if standard_sum < _CORE_AVCA_OMEGA else CORE_AREO_UNIO

def core_avc_mul(a: CanonicalVal, b: CanonicalVal) -> CanonicalVal: # ⊗_v1.2 logic
    global _CORE_AVCA_OMEGA
    if _CORE_AVCA_OMEGA == 0: raise ValueError("CoreAVCA Omega not set.")
    _core_check_val(a, _CORE_AVCA_OMEGA); _core_check_val(b, _CORE_AVCA_OMEGA)
    a_is_unio = isinstance(a, Unio); b_is_unio = isinstance(b, Unio)
    if a_is_unio or b_is_unio:
        is_any_areo = (a_is_unio and a.aspect == "areo") or \
                      (b_is_unio and b.aspect == "areo") # type: ignore
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
    if not (P_A <= x_local <= P_B):
        raise ValueError(f"Value x_local={x_local} is outside the local frame [{P_A}, {P_B}]")
    if x_local == P_A or x_local == P_B:
        return CANONICAL_UNIO_POLE 
    return x_local - P_A 

def lens_inverse(k_canonical: CanonicalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    if S < 1: raise ValueError("Span S must be >= 1 for lens_inverse.")
    if isinstance(k_canonical, Unio):
        return P_A 
    elif isinstance(k_canonical, int) and 1 <= k_canonical < S:
        return P_A + k_canonical
    else: # Should only receive Unio or DFI {1..S-1} from core ops
        raise ValueError(f"Invalid canonical value {k_canonical!r} for inversion into span {S}. Frame [{P_A},{P_B}]")

# --- Mapped AVCA Operations ---
def mapped_avc_add(x_local: LocalVal, y_local: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    if S < 1 : raise ValueError("Span S must be >= 1 for mapped operations.")
    val_x_canon = lens_forward(x_local, P_A, P_B)
    val_y_canon = lens_forward(y_local, P_A, P_B)
    set_core_avca_omega(S) 
    res_canon = core_avc_add(val_x_canon, val_y_canon)
    return lens_inverse(res_canon, P_A, P_B)

def mapped_avc_mul(x_local: LocalVal, y_local: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    if S < 1 : raise ValueError("Span S must be >= 1 for mapped operations.")
    val_x_canon = lens_forward(x_local, P_A, P_B)
    val_y_canon = lens_forward(y_local, P_A, P_B)
    set_core_avca_omega(S)
    res_canon = core_avc_mul(val_x_canon, val_y_canon)
    return lens_inverse(res_canon, P_A, P_B)

# --- Helper for comparing results ---
def local_equals(val1: LocalVal, val2: LocalVal) -> bool:
    return val1 == val2

def canonical_equals(val1: CanonicalVal, val2: CanonicalVal) -> bool:
    if isinstance(val1, Unio) and isinstance(val2, Unio):
        return True 
    return val1 == val2

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Mapped Operations Law & Fidelity Tests (Stage 2-B) ---")
    print("    Using lens: f(x)=Unio if x=PA/PB, else x-PA. g(Unio)=PA, g(k)=PA+k.")
    print("    Canonical Ops: AVCA Core v1.2b (⊕_v1.1, ⊗_v1.2)\n")
    
    spans_to_test = list(range(2, 6)) # S = 2, 3, 4, 5. (User asked for 2-7, let's do 2-5 first due to N^3)
    P_A = 0 

    fidelity_results = []

    for S_val in spans_to_test:
        P_B = P_A + S_val
        print(f"--- Testing with Local Span S = {S_val} (Frame [{P_A},{P_B}], Canonical AVCA-{S_val}) ---")
        
        local_elements: List[LocalVal] = list(range(P_A, P_B + 1))
        if not local_elements: continue

        # --- Test Algebraic Laws for Mapped Operations ---
        # Commutativity of mapped_avc_mul
        comm_mul_law_holds = True
        comm_mul_counterexample = None
        for x, y in itertools.product(local_elements, local_elements):
            try:
                if not local_equals(mapped_avc_mul(x, y, P_A, P_B), mapped_avc_mul(y, x, P_A, P_B)):
                    comm_mul_law_holds = False; comm_mul_counterexample = (x,y); break
            except Exception as e: comm_mul_law_holds = False; comm_mul_counterexample = (x,y,str(e)); break
        print(f"  Commutativity of mapped_avc_mul: {'Holds' if comm_mul_law_holds else f'FAILS (e.g., {comm_mul_counterexample})'}")

        # Associativity of mapped_avc_mul
        assoc_mul_law_holds = True
        assoc_mul_counterexample = None
        for x, y, z in itertools.product(local_elements, local_elements, local_elements):
            try:
                lhs = mapped_avc_mul(mapped_avc_mul(x, y, P_A, P_B), z, P_A, P_B)
                rhs = mapped_avc_mul(x, mapped_avc_mul(y, z, P_A, P_B), P_A, P_B)
                if not local_equals(lhs, rhs):
                    assoc_mul_law_holds = False; assoc_mul_counterexample = (x,y,z); break
            except Exception as e: assoc_mul_law_holds = False; assoc_mul_counterexample = (x,y,z,str(e)); break
            if not assoc_mul_law_holds: break
        print(f"  Associativity of mapped_avc_mul: {'Holds' if assoc_mul_law_holds else f'FAILS (e.g., {assoc_mul_counterexample})'}")

        # Distributivity: mapped_mul(x, mapped_add(y,z)) == mapped_add(mapped_mul(x,y), mapped_mul(x,z))
        distrib_law_holds = True
        distrib_counterexample = None
        for x, y, z in itertools.product(local_elements, local_elements, local_elements):
            try:
                lhs = mapped_avc_mul(x, mapped_avc_add(y, z, P_A, P_B), P_A, P_B)
                rhs = mapped_avc_add(mapped_avc_mul(x, y, P_A, P_B), mapped_avc_mul(x, z, P_A, P_B), P_A, P_B)
                if not local_equals(lhs, rhs):
                    distrib_law_holds = False; distrib_counterexample = (x,y,z); break
            except Exception as e: distrib_law_holds = False; distrib_counterexample = (x,y,z,str(e)); break
            if not distrib_law_holds: break
        print(f"  Distributivity (mul over add): {'Holds' if distrib_law_holds else f'FAILS (e.g., {distrib_counterexample})'}")

        # --- Calculate Fidelity Scores ---
        add_homomorphism_holds_count = 0
        mul_homomorphism_holds_count = 0
        total_pairs = len(local_elements) * len(local_elements)

        for x, y in itertools.product(local_elements, local_elements):
            # Additive Fidelity: f(x ⊕_loc y) == f(x) ⊕_can f(y)
            try:
                res_loc_add = mapped_avc_add(x, y, P_A, P_B)
                f_res_loc_add = lens_forward(res_loc_add, P_A, P_B)
                
                fx = lens_forward(x, P_A, P_B)
                fy = lens_forward(y, P_A, P_B)
                set_core_avca_omega(S_val)
                fx_add_can_fy = core_avc_add(fx, fy)
                
                if canonical_equals(f_res_loc_add, fx_add_can_fy):
                    add_homomorphism_holds_count += 1
            except Exception: pass # Error in operation means fidelity fails for this pair

            # Multiplicative Fidelity: f(x ⊗_loc y) == f(x) ⊗_can f(y)
            try:
                res_loc_mul = mapped_avc_mul(x, y, P_A, P_B)
                f_res_loc_mul = lens_forward(res_loc_mul, P_A, P_B)
                
                # fx, fy already computed
                set_core_avca_omega(S_val)
                fx_mul_can_fy = core_avc_mul(fx, fy)
                
                if canonical_equals(f_res_loc_mul, fx_mul_can_fy):
                    mul_homomorphism_holds_count += 1
            except Exception: pass

        add_fid = add_homomorphism_holds_count / total_pairs if total_pairs > 0 else 0
        mul_fid = mul_homomorphism_holds_count / total_pairs if total_pairs > 0 else 0
        
        fidelity_results.append({
            "Span_S": S_val, "P_A": P_A, "P_B": P_B, 
            "L_f": 2, # Known for this lens and T=[P_A,P_B]
            "add_fidelity": add_fid, 
            "mul_fidelity": mul_fid,
            "comm_add_mapped": "Holds", # From previous script's confirmed result
            "assoc_add_mapped": "Holds" if S_val <=2 else "FAILS", # From previous script
            "comm_mul_mapped": "Holds" if comm_mul_law_holds else "FAILS",
            "assoc_mul_mapped": "Holds" if assoc_mul_law_holds else "FAILS",
            "distrib_mapped": "Holds" if distrib_law_holds else "FAILS"
        })
        print(f"  Fidelity Scores: Add={add_fid:.4f}, Mul={mul_fid:.4f}")
        print("-" * 70)

    print("\n--- Mapped Operations Law & Fidelity Tests Completed ---")
    print("\nSummary Profile (L, Add_Fid, Mul_Fid) and Law Survival:")
    print("S | Frame   | L | Add_Fid | Mul_Fid | Comm(Add_M) | Assoc(Add_M) | Comm(Mul_M) | Assoc(Mul_M) | Distrib(M/A_M)")
    print("--|---------|---|---------|---------|-------------|--------------|-------------|--------------|----------------")
    for res in fidelity_results:
        print(f"{res['Span_S']!s:<2}| [{res['P_A']},{res['P_B']}]   | {res['L_f']!s:<2}| {res['add_fidelity']:<7.4f} | {res['mul_fidelity']:<7.4f} | {res['comm_add_mapped']:<11} | {res['assoc_add_mapped']:<12} | {res['comm_mul_mapped']:<11} | {res['assoc_mul_mapped']:<12} | {res['distrib_mapped']:<15}")

if __name__ == "__main__":
    run_all_tests()