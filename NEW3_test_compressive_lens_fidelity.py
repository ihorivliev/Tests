# test_compressive_lens_fidelity.py
# Purpose: Stage 2-B - Test a compressive lens (scale k=2).
# Calculate Loss L, Add/Mul Fidelities, and check algebraic law survival
# for mapped operations using this compressive lens for spans S=2-7.

import itertools
import math
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- Unio Class Definition ---
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

LocalVal = int 
CanonicalVal = Union[int, Unio]
_CORE_AVCA_OMEGA: int = 0

# --- Core AVCA Domain Enforcement & Operations (v1.2b logic) ---
def _core_check_val(x: CanonicalVal, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"CoreAVCA Omega parameter must be an integer >= 1. Got: {current_omega}")
    if isinstance(x, Unio): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid CoreAVCA Value: {x!r}. Expected int (for DFI) or Unio instance. Got type: {type(x)}.")
    if current_omega == 1: # Canonical DFI is empty if Omega_eff=1
        if isinstance(x, int):
            raise ValueError(f"Invalid CoreAVCA DFI Value for Omega=1: {x}. DFI is empty.")
    elif not (1 <= x < current_omega): 
            raise ValueError(f"Invalid CoreAVCA DFI Value: {x}. For Omega={current_omega}, DFI must be in range [1, {current_omega - 1}].")

def core_avc_add(a: CanonicalVal, b: CanonicalVal) -> CanonicalVal: # ⊕_v1.1
    global _CORE_AVCA_OMEGA
    if _CORE_AVCA_OMEGA == 0: raise ValueError("CoreAVCA Omega not set for add.")
    _core_check_val(a, _CORE_AVCA_OMEGA); _core_check_val(b, _CORE_AVCA_OMEGA)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    standard_sum = a + b # type: ignore 
    return standard_sum if standard_sum < _CORE_AVCA_OMEGA else CORE_AREO_UNIO

def core_avc_mul(a: CanonicalVal, b: CanonicalVal) -> CanonicalVal: # ⊗_v1.2
    global _CORE_AVCA_OMEGA
    if _CORE_AVCA_OMEGA == 0: raise ValueError("CoreAVCA Omega not set for mul.")
    _core_check_val(a, _CORE_AVCA_OMEGA); _core_check_val(b, _CORE_AVCA_OMEGA)
    a_is_unio = isinstance(a, Unio); b_is_unio = isinstance(b, Unio)
    if a_is_unio or b_is_unio:
        a_is_areo = a_is_unio and a.aspect == "areo" # type: ignore
        b_is_areo = b_is_unio and b.aspect == "areo" # type: ignore
        is_any_areo = a_is_areo or b_is_areo
        return CORE_AREO_UNIO if is_any_areo else CORE_ZERO_UNIO
    else: 
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < _CORE_AVCA_OMEGA else CORE_AREO_UNIO

def set_core_avca_omega(omega_value: int):
    global _CORE_AVCA_OMEGA
    if not isinstance(omega_value, int) or omega_value < 1:
        omega_value = 1 # Default to Omega=1 if span calculation leads to <1
    _CORE_AVCA_OMEGA = omega_value

# --- Compressive Lens Functions (k_compress=2) ---
K_COMPRESS = 2

def lens_forward_compressive(x_local: LocalVal, P_A: int, P_B: int) -> CanonicalVal:
    S = P_B - P_A
    Omega_eff = math.ceil(S / K_COMPRESS)
    if Omega_eff < 1: Omega_eff = 1 # Canonical Omega must be at least 1

    if not (P_A <= x_local <= P_B):
        raise ValueError(f"Value x_local={x_local} is outside the local frame [{P_A}, {P_B}]")
    
    if x_local == P_A or x_local == P_B:
        return CANONICAL_UNIO_POLE
    
    val_intermediate = x_local - P_A # Local DFI mapped to {1, ..., S-1}
    val_scaled = math.floor((val_intermediate - 1) / K_COMPRESS) + 1
    
    if Omega_eff == 1: # Canonical DFI is empty
        return CANONICAL_UNIO_POLE
    if 1 <= val_scaled < Omega_eff:
        return int(val_scaled)
    else: # Capped: values that scale outside canonical DFI map to Unio
        return CANONICAL_UNIO_POLE

def lens_inverse_compressive(k_canonical: CanonicalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    Omega_eff = math.ceil(S / K_COMPRESS)
    if Omega_eff < 1: Omega_eff = 1

    if isinstance(k_canonical, Unio):
        return P_A
    elif isinstance(k_canonical, int):
        if Omega_eff == 1 : # Canonical DFI was empty, so k_canonical should not be an int from core_op
             # This case implies k_canonical might be an unexpected integer from a flawed core_op
             # or bad _core_check_val. If it must be mapped, map to a pole.
            return P_A
        if 1 <= k_canonical < Omega_eff: # Valid canonical DFI
            # Map to the first corresponding local DFI value
            # x_local - P_A = (k_canonical - 1) * K_COMPRESS + 1
            # x_local = P_A + (k_canonical - 1) * K_COMPRESS + 1
            # Ensure it doesn't exceed P_B - 1 (max local DFI) due to rounding/edge cases
            inv_val = P_A + (k_canonical - 1) * K_COMPRESS + 1
            return min(inv_val, P_B -1) if P_B -1 >= P_A else P_A # ensure it's within local DFI bounds or P_A
        else:
            # If k_canonical is an int but outside valid canonical DFI range (e.g. 0, or >= Omega_eff)
            # This shouldn't happen if core_avc_ops are correct for AVCA-Omega_eff
            return P_A # Default map to origin pole
    else:
        raise TypeError(f"Invalid type for k_canonical: {type(k_canonical)}")

# --- Mapped AVCA Operations using Compressive Lens ---
def mapped_avc_add_comp(x_local: LocalVal, y_local: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    Omega_eff = math.ceil(S / K_COMPRESS)
    if Omega_eff < 1: Omega_eff = 1
    
    val_x_canon = lens_forward_compressive(x_local, P_A, P_B)
    val_y_canon = lens_forward_compressive(y_local, P_A, P_B)
    set_core_avca_omega(int(Omega_eff))
    res_canon = core_avc_add(val_x_canon, val_y_canon)
    return lens_inverse_compressive(res_canon, P_A, P_B)

def mapped_avc_mul_comp(x_local: LocalVal, y_local: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    Omega_eff = math.ceil(S / K_COMPRESS)
    if Omega_eff < 1: Omega_eff = 1

    val_x_canon = lens_forward_compressive(x_local, P_A, P_B)
    val_y_canon = lens_forward_compressive(y_local, P_A, P_B)
    set_core_avca_omega(int(Omega_eff))
    res_canon = core_avc_mul(val_x_canon, val_y_canon)
    return lens_inverse_compressive(res_canon, P_A, P_B)

# --- Loss Metric L(f) for Compressive Lens ---
def calculate_L_f_compressive(test_set_T: List[int], P_A: int, P_B: int) -> int:
    loss_count = 0
    mapped_values = {val_t: lens_forward_compressive(val_t, P_A, P_B) for val_t in test_set_T}
    for x, y in itertools.product(test_set_T, test_set_T):
        if x == y: continue
        fx = mapped_values[x]
        fy = mapped_values[y]
        if canonical_equals(fx, fy): 
            loss_count += 1
    return loss_count

# --- Helper for comparing results & Status String ---
def local_equals(val1: LocalVal, val2: LocalVal) -> bool: return val1 == val2
def canonical_equals(val1: CanonicalVal, val2: CanonicalVal) -> bool:
    if isinstance(val1, Unio) and isinstance(val2, Unio): return True 
    return val1 == val2

def status_to_str(status_bool_or_str, counterexample_str=""):
    if isinstance(status_bool_or_str, str): return status_bool_or_str
    if status_bool_or_str: return "Holds"
    return f"FAILS ({counterexample_str})" if counterexample_str else "FAILS"

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Compressive Lens Law & Fidelity Tests (Stage 2-B) ---")
    print(f"    Using Compressive Lens (k={K_COMPRESS}): f_cmp(x)=U if x=PA/PB, else floor((x-PA-1)/{K_COMPRESS})+1 then capped to AVCA-Ω_eff.")
    print(f"    Ω_eff = ceil(S/{K_COMPRESS}). g_cmp(U)=PA, g_cmp(k_c)=PA+((k_c-1)*{K_COMPRESS})+1 (approx inverse).")
    print("    Canonical Ops: AVCA Core v1.2b (⊕_v1.1, ⊗_v1.2)\n")
    
    spans_to_test = list(range(2, 8)) # S = 2 through 7
    P_A = 0 
    fidelity_results = []

    # Mapped Add laws from previous script's findings (using affine lens)
    # These are NOT for the compressive lens, just for table comparison.
    affine_mapped_add_results = {
        2: {"comm": "Holds", "assoc": "Holds"}, 3: {"comm": "Holds", "assoc": "FAILS"},
        4: {"comm": "Holds", "assoc": "FAILS"}, 5: {"comm": "Holds", "assoc": "FAILS"},
        6: {"comm": "Holds", "assoc": "FAILS"}, 7: {"comm": "Holds", "assoc": "FAILS"},
    }

    for S_val in spans_to_test:
        P_B = P_A + S_val
        Omega_eff = math.ceil(S_val / K_COMPRESS)
        if Omega_eff < 1: Omega_eff = 1
        print(f"--- Testing Local Span S = {S_val} (Frame [{P_A},{P_B}], Canonical AVCA-{int(Omega_eff)}) ---")
        
        local_elements: List[LocalVal] = list(range(P_A, P_B + 1))
        if not local_elements: continue

        loss_l = calculate_L_f_compressive(local_elements, P_A, P_B)
        print(f"  Loss L(f_cmp): {loss_l}")

        # Commutativity of mapped_avc_mul_comp
        comm_mul_law_holds = True; comm_mul_cex_s = ""
        for x,y in itertools.product(local_elements,repeat=2):
            try:
                if not local_equals(mapped_avc_mul_comp(x,y,P_A,P_B), mapped_avc_mul_comp(y,x,P_A,P_B)):
                    comm_mul_law_holds=False; comm_mul_cex_s=f"x={x},y={y}"; break
            except Exception as e: comm_mul_law_holds=False; comm_mul_cex_s=f"x={x},y={y} Exc:{e}"; break
        print(f"  Commutativity of mapped_avc_mul_comp: {status_to_str(comm_mul_law_holds, comm_mul_cex_s)}")

        # Associativity of mapped_avc_mul_comp
        assoc_mul_law_holds: Any = True; assoc_mul_cex_s = ""
        if S_val <= 5: # Limit N^3 for speed
            for x,y,z in itertools.product(local_elements,repeat=3):
                try:
                    lhs = mapped_avc_mul_comp(mapped_avc_mul_comp(x,y,P_A,P_B),z,P_A,P_B)
                    rhs = mapped_avc_mul_comp(x,mapped_avc_mul_comp(y,z,P_A,P_B),P_A,P_B)
                    if not local_equals(lhs,rhs):
                        assoc_mul_law_holds=False; assoc_mul_cex_s=f"x={x},y={y},z={z}"; break
                except Exception as e: assoc_mul_law_holds=False; assoc_mul_cex_s=f"x={x},y={y},z={z} Exc:{e}"; break
                if not assoc_mul_law_holds: break
        else: assoc_mul_law_holds = "SKIP S>5"
        print(f"  Associativity of mapped_avc_mul_comp: {status_to_str(assoc_mul_law_holds, assoc_mul_cex_s)}")

        # Distributivity: mapped_mul_comp(x, mapped_add_comp(y,z)) == mapped_add_comp(mapped_mul_comp(x,y), mapped_mul_comp(x,z))
        distrib_law_holds: Any = True; distrib_cex_s = ""
        if S_val <= 5: # Limit N^3 for speed
            for x,y,z in itertools.product(local_elements,repeat=3):
                try:
                    lhs = mapped_avc_mul_comp(x, mapped_avc_add_comp(y,z,P_A,P_B),P_A,P_B)
                    rhs = mapped_avc_add_comp(mapped_avc_mul_comp(x,y,P_A,P_B), mapped_avc_mul_comp(x,z,P_A,P_B),P_A,P_B)
                    if not local_equals(lhs,rhs):
                        distrib_law_holds=False; distrib_cex_s=f"x={x},y={y},z={z}"; break
                except Exception as e: distrib_law_holds=False; distrib_cex_s=f"x={x},y={y},z={z} Exc:{e}"; break
                if not distrib_law_holds: break
        else: distrib_law_holds = "SKIP S>5"
        print(f"  Distributivity (comp_mul over comp_add): {status_to_str(distrib_law_holds, distrib_cex_s)}")

        # Fidelity Scores
        add_hom_count = 0; mul_hom_count = 0
        total_pairs = len(local_elements)**2
        for x,y in itertools.product(local_elements,repeat=2):
            try:
                f_res_loc_add = lens_forward_compressive(mapped_avc_add_comp(x,y,P_A,P_B), P_A,P_B)
                fx, fy = lens_forward_compressive(x,P_A,P_B), lens_forward_compressive(y,P_A,P_B)
                set_core_avca_omega(int(Omega_eff))
                fx_add_can_fy = core_avc_add(fx,fy)
                if canonical_equals(f_res_loc_add, fx_add_can_fy): add_hom_count +=1
            except Exception: pass
            try:
                f_res_loc_mul = lens_forward_compressive(mapped_avc_mul_comp(x,y,P_A,P_B), P_A,P_B)
                # fx, fy are same as for add
                set_core_avca_omega(int(Omega_eff))
                fx_mul_can_fy = core_avc_mul(fx,fy)
                if canonical_equals(f_res_loc_mul, fx_mul_can_fy): mul_hom_count +=1
            except Exception: pass
        
        add_fid = add_hom_count / total_pairs if total_pairs > 0 else 0
        mul_fid = mul_hom_count / total_pairs if total_pairs > 0 else 0
        print(f"  Fidelity Scores (Compressive): Add={add_fid:.4f}, Mul={mul_fid:.4f}")

        fidelity_results.append({
            "Span_S": S_val, "P_A": P_A, "P_B": P_B, "L_f": loss_l, 
            "add_fidelity": add_fid, "mul_fidelity": mul_fid,
            "comm_add_mapped": affine_mapped_add_results.get(S_val,{}).get("comm","N/A"), # This is for affine
            "assoc_add_mapped": affine_mapped_add_results.get(S_val,{}).get("assoc","N/A"),# This is for affine
            "comm_mul_mapped": status_to_str(comm_mul_law_holds),
            "assoc_mul_mapped": status_to_str(assoc_mul_law_holds),
            "distrib_mapped": status_to_str(distrib_law_holds)
        })
        print("-" * 70)

    print("\n--- Compressive Lens Law & Fidelity Tests Completed ---")
    print("\nSummary Profile (L, Add_Fid_Comp, Mul_Fid_Comp) and Law Survival (for Compressive Lens Mapped Ops):")
    header = "S | Frame   | L_cmp| Add_Fid_C | Mul_Fid_C | Comm(Add_Affine) | Assoc(Add_Affine) | Comm(Mul_C) | Assoc(Mul_C) | Distrib(M_C/A_C)"
    print(header)
    print("-" * len(header))
    for res in fidelity_results:
        print(f"{res['Span_S']!s:<2}| [{res['P_A']},{res['P_B']}]   | {res['L_f']!s:<6}| {res['add_fidelity']:<9.4f} | {res['mul_fidelity']:<9.4f} | {res['comm_add_mapped']:<16} | {res['assoc_add_mapped']:<17} | {res['comm_mul_mapped']:<11} | {res['assoc_mul_mapped']:<12} | {res['distrib_mapped']:<17}")

if __name__ == "__main__":
    run_all_tests()