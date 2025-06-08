# test_compressive_lens_direct_comparison.py
# Purpose: Stage 2-B - Test a compressive lens (k=2).
# 1. Calculate Loss L(f_cmp).
# 2. Test algebraic laws for mapped operations (defined via round-trip g(f()op f())).
# 3. Calculate "direct comparison" fidelities (non-homomorphic test):
#    f_cmp(op_LocalSpanS(x,y)) vs. op_OmegaEff(f_cmp(x), f_cmp(y))

import itertools
import math
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- Unio Class Definition ---
class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: Literal["zero", "areo"] = "zero"):
        self.aspect = aspect
    def __eq__(self, other: object) -> bool: return isinstance(other, Unio)
    def __hash__(self) -> int: return hash(type(self))
    def __repr__(self) -> str: return f"Unio('{self.aspect}')"

CANONICAL_UNIO_POLE = Unio("zero") 
CORE_ZERO_UNIO = Unio("zero")
CORE_AREO_UNIO = Unio("areo")

LocalVal = int 
CanonicalVal = Union[int, Unio]
_CORE_AVCA_OMEGA: int = 0 # Used for canonical operations at Omega_eff or Span S

# --- Core AVCA Domain Enforcement & Operations (v1.2b logic) ---
def _core_check_val(x: CanonicalVal, current_omega: int):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"CoreAVCA Omega ({current_omega}) must be an integer >= 1.")
    if isinstance(x, Unio): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid CoreAVCA Value: {x!r}. Expected int or Unio. Got {type(x)} for Omega={current_omega}.")
    if current_omega == 1:
        if isinstance(x, int):
            raise ValueError(f"Invalid CoreAVCA DFI Value for Omega=1: {x}. DFI is empty.")
    elif not (1 <= x < current_omega): 
            raise ValueError(f"Invalid CoreAVCA DFI Value: {x}. For Omega={current_omega}, DFI must be in [1, {current_omega-1}]")

def set_core_avca_omega(omega_value: int):
    global _CORE_AVCA_OMEGA
    if not isinstance(omega_value, int) or omega_value < 1:
        # This case should ideally be handled by ensuring Omega_eff is always >=1
        # For AVCA-1, DFI is empty. Operations still defined (e.g. U+U=U).
        raise ValueError("CoreAVCA Omega must be an integer >= 1.")
    _CORE_AVCA_OMEGA = omega_value

def core_avc_add(a: CanonicalVal, b: CanonicalVal, omega_for_op: int) -> CanonicalVal: # ⊕_v1.1
    set_core_avca_omega(omega_for_op)
    _core_check_val(a, _CORE_AVCA_OMEGA); _core_check_val(b, _CORE_AVCA_OMEGA)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    standard_sum = a + b # type: ignore 
    return standard_sum if standard_sum < _CORE_AVCA_OMEGA else CORE_AREO_UNIO

def core_avc_mul(a: CanonicalVal, b: CanonicalVal, omega_for_op: int) -> CanonicalVal: # ⊗_v1.2
    set_core_avca_omega(omega_for_op)
    _core_check_val(a, _CORE_AVCA_OMEGA); _core_check_val(b, _CORE_AVCA_OMEGA)
    a_is_unio = isinstance(a, Unio); b_is_unio = isinstance(b, Unio)
    if a_is_unio or b_is_unio:
        a_is_areo = a_is_unio and a.aspect == "areo" # type: ignore
        b_is_areo = b_is_unio and b.aspect == "areo" # type: ignore
        return CORE_AREO_UNIO if (a_is_areo or b_is_areo) else CORE_ZERO_UNIO
    else: 
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < _CORE_AVCA_OMEGA else CORE_AREO_UNIO

# --- Compressive Lens Functions (k_compress=2) ---
K_COMPRESS = 2

def get_omega_eff(S: int, k_compress: int) -> int:
    if S < 1: return 1 # Or raise error, span must be positive
    omega_eff = math.ceil(S / k_compress)
    return int(max(1, omega_eff)) # Ensure Omega_eff is at least 1

def lens_forward_compressive(x_local: LocalVal, P_A: int, P_B: int) -> CanonicalVal:
    S = P_B - P_A
    Omega_eff = get_omega_eff(S, K_COMPRESS)

    if not (P_A <= x_local <= P_B):
        raise ValueError(f"Value x_local={x_local} not in local frame [{P_A}, {P_B}]")
    if x_local == P_A or x_local == P_B:
        return CANONICAL_UNIO_POLE
    
    val_intermediate = x_local - P_A 
    val_scaled = math.floor((val_intermediate - 1) / K_COMPRESS) + 1
    
    if Omega_eff == 1: # Canonical DFI is empty for AVCA-1
        return CANONICAL_UNIO_POLE
    if 1 <= val_scaled < Omega_eff:
        return int(val_scaled)
    else: 
        return CANONICAL_UNIO_POLE

def lens_inverse_compressive(k_canonical: CanonicalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    Omega_eff = get_omega_eff(S, K_COMPRESS)

    if isinstance(k_canonical, Unio):
        return P_A 
    elif isinstance(k_canonical, int):
        if Omega_eff == 1: # Canonical DFI was empty. Any int k_canonical is unexpected from core_op.
            return P_A 
        if 1 <= k_canonical < Omega_eff: # Valid canonical DFI for AVCA-Omega_eff
            inv_val = P_A + (k_canonical - 1) * K_COMPRESS + 1
            # Cap at P_B-1 if S-1 (max local DFI index) is non-empty
            max_local_dfi = P_B - 1
            if S < 2 : max_local_dfi = P_A # No DFI if S=1 or S=0 (empty range P_A+1 to P_B-1)
            return min(inv_val, max_local_dfi) if P_A <= max_local_dfi else P_A
        else: # k_canonical is an int but out of expected DFI range for Omega_eff
            return P_A 
    else:
        raise TypeError(f"Invalid type for k_canonical: {type(k_canonical)}")

# --- Mapped AVCA Operations (Round-Trip for Law Testing) ---
def mapped_avc_add_comp(x: LocalVal, y: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    Omega_eff = get_omega_eff(S, K_COMPRESS)
    fx = lens_forward_compressive(x, P_A, P_B)
    fy = lens_forward_compressive(y, P_A, P_B)
    res_canon = core_avc_add(fx, fy, Omega_eff)
    return lens_inverse_compressive(res_canon, P_A, P_B)

def mapped_avc_mul_comp(x: LocalVal, y: LocalVal, P_A: int, P_B: int) -> LocalVal:
    S = P_B - P_A
    Omega_eff = get_omega_eff(S, K_COMPRESS)
    fx = lens_forward_compressive(x, P_A, P_B)
    fy = lens_forward_compressive(y, P_A, P_B)
    res_canon = core_avc_mul(fx, fy, Omega_eff)
    return lens_inverse_compressive(res_canon, P_A, P_B)

# --- Loss Metric L(f_cmp) ---
def calculate_L_f_comp(test_set_T: List[int], P_A: int, P_B: int) -> int:
    loss_count = 0
    mapped_values = {val_t: lens_forward_compressive(val_t, P_A, P_B) for val_t in test_set_T}
    for x, y in itertools.product(test_set_T, test_set_T):
        if x == y: continue
        if canonical_equals(mapped_values[x], mapped_values[y]): loss_count += 1
    return loss_count

def local_equals(v1:LocalVal, v2:LocalVal) -> bool: return v1 == v2
def canonical_equals(v1:CanonicalVal, v2:CanonicalVal) -> bool:
    return (isinstance(v1,Unio) and isinstance(v2,Unio)) or v1 == v2

def status_to_str(val: Any, cex_str: str = "") -> str:
    if isinstance(val, str): return val
    return "Holds" if val else (f"FAILS ({cex_str})" if cex_str else "FAILS")

# --- Test Runner ---
def run_all_tests():
    print("--- Starting Compressive Lens (k=2) Direct Comparison Fidelity & Law Tests (Stage 2-B) ---")
    print("    f_cmp(op_S(x,y)) vs. op_Ωeff(f_cmp(x), f_cmp(y))\n")
    
    spans_to_test = list(range(2, 8)) # S = 2 through 7
    P_A = 0 
    results_summary = []

    affine_mapped_add_results = { # For table comparison (Assoc(Add_M) from prior script)
        2: {"assoc": "Holds"}, 3: {"assoc": "FAILS"}, 4: {"assoc": "FAILS"},
        5: {"assoc": "FAILS"}, 6: {"assoc": "FAILS"}, 7: {"assoc": "FAILS"},
    }

    for S_val in spans_to_test:
        P_B = P_A + S_val
        Omega_eff = get_omega_eff(S_val, K_COMPRESS)
        print(f"--- Testing Span S={S_val} (Frame [{P_A},{P_B}], Canonical AVCA-{Omega_eff}) ---")
        
        local_elements: List[LocalVal] = list(range(P_A, P_B + 1))
        if not local_elements: continue

        loss_l = calculate_L_f_comp(local_elements, P_A, P_B)
        print(f"  Loss L(f_cmp): {loss_l}")

        # Laws for Mapped_Op_Compressive (round-trip definition)
        comm_mul_c = True; comm_mul_cex_s = ""
        for x,y in itertools.product(local_elements,repeat=2):
            try:
                if not local_equals(mapped_avc_mul_comp(x,y,P_A,P_B), mapped_avc_mul_comp(y,x,P_A,P_B)):
                    comm_mul_c=False; comm_mul_cex_s=f"x={x},y={y}"; break
            except Exception as e: comm_mul_c=False; comm_mul_cex_s=f"x={x},y={y} Exc:{e}"; break
        print(f"  Commutativity of mapped_avc_mul_comp: {status_to_str(comm_mul_c, comm_mul_cex_s)}")

        assoc_mul_c: Any = True; assoc_mul_cex_s = ""
        if S_val <= 5:
            for x,y,z in itertools.product(local_elements,repeat=3):
                try:
                    lhs = mapped_avc_mul_comp(mapped_avc_mul_comp(x,y,P_A,P_B),z,P_A,P_B)
                    rhs = mapped_avc_mul_comp(x,mapped_avc_mul_comp(y,z,P_A,P_B),P_A,P_B)
                    if not local_equals(lhs,rhs):
                        assoc_mul_c=False; assoc_mul_cex_s=f"x={x},y={y},z={z}"; break
                except Exception as e: assoc_mul_c=False; assoc_mul_cex_s=f"x={x},y={y},z={z} Exc:{e}"; break
                if not isinstance(assoc_mul_c, str) and not assoc_mul_c: break
        else: assoc_mul_c = "SKIP S>5"
        print(f"  Associativity of mapped_avc_mul_comp: {status_to_str(assoc_mul_c, assoc_mul_cex_s)}")
        
        distrib_c: Any = True; distrib_cex_s = ""
        if S_val <= 5:
            for x,y,z in itertools.product(local_elements,repeat=3):
                try:
                    lhs = mapped_avc_mul_comp(x, mapped_avc_add_comp(y,z,P_A,P_B),P_A,P_B)
                    rhs = mapped_avc_add_comp(mapped_avc_mul_comp(x,y,P_A,P_B), mapped_avc_mul_comp(x,z,P_A,P_B),P_A,P_B)
                    if not local_equals(lhs,rhs):
                        distrib_c=False; distrib_cex_s=f"x={x},y={y},z={z} -> L:{lhs},R:{rhs}"; break
                except Exception as e: distrib_c=False; distrib_cex_s=f"x={x},y={y},z={z} Exc:{e}"; break
                if not isinstance(distrib_c, str) and not distrib_c: break
        else: distrib_c = "SKIP S>5"
        print(f"  Distributivity (comp_mul over comp_add): {status_to_str(distrib_c, distrib_cex_s)}")

        # Direct Comparison Fidelities
        add_fid_matches = 0; mul_fid_matches = 0
        total_pairs = len(local_elements)**2
        for x,y in itertools.product(local_elements,repeat=2):
            # Additive
            try:
                res_local_raw_add = core_avc_add(x,y,S_val)
                mapped_lhs_add = lens_forward_compressive(res_local_raw_add, P_A,P_B)
                fx, fy = lens_forward_compressive(x,P_A,P_B), lens_forward_compressive(y,P_A,P_B)
                mapped_rhs_add = core_avc_add(fx,fy,Omega_eff)
                if canonical_equals(mapped_lhs_add, mapped_rhs_add): add_fid_matches+=1
            except Exception: pass
            # Multiplicative
            try:
                res_local_raw_mul = core_avc_mul(x,y,S_val)
                mapped_lhs_mul = lens_forward_compressive(res_local_raw_mul, P_A,P_B)
                fx, fy = lens_forward_compressive(x,P_A,P_B), lens_forward_compressive(y,P_A,P_B)
                mapped_rhs_mul = core_avc_mul(fx,fy,Omega_eff)
                if canonical_equals(mapped_lhs_mul, mapped_rhs_mul): mul_fid_matches+=1
            except Exception: pass
        
        add_fid = add_fid_matches/total_pairs if total_pairs>0 else 0
        mul_fid = mul_fid_matches/total_pairs if total_pairs>0 else 0
        print(f"  Direct Comparison Fidelities: Add={add_fid:.4f} ({add_fid_matches}/{total_pairs}), Mul={mul_fid:.4f} ({mul_fid_matches}/{total_pairs})")

        results_summary.append({
            "S": S_val, "Frame": f"[{P_A},{P_B}]", "L_cmp": loss_l, 
            "Add_Fid_C": add_fid, "Mul_Fid_C": mul_fid,
            "Comm(Add_Aff)": affine_mapped_add_results.get(S_val,{}).get("comm","N/A"),
            "Assoc(Add_Aff)": affine_mapped_add_results.get(S_val,{}).get("assoc","N/A"),
            "Comm(Mul_C)": status_to_str(comm_mul_c),
            "Assoc(Mul_C)": status_to_str(assoc_mul_c),
            "Distrib(M_C/A_C)": status_to_str(distrib_c)
        })
        print("-" * 70)

    print("\n--- Compressive Lens Direct Comparison Fidelity & Law Tests Completed ---")
    print("\nSummary Profile (L_cmp, Add_Fid_DirectComp, Mul_Fid_DirectComp) and Law Survival (for Compressive Lens Mapped Ops via round-trip):")
    header = "S | Frame   | L_cmp| Add_Fid_DC | Mul_Fid_DC | Comm(Add_Aff) | Assoc(Add_Aff) | Comm(Mul_C) | Assoc(Mul_C) | Distrib(M_C/A_C)"
    print(header)
    print("-" * len(header))
    for res in results_summary:
        print(f"{res['S']!s:<2}| {res['Frame']:<8}| {res['L_cmp']!s:<6}| {res['Add_Fid_C']:<10.4f} | {res['Mul_Fid_C']:<10.4f} | {res['Comm(Add_Aff)']:<15} | {res['Assoc(Add_Aff)']:<16} | {res['Comm(Mul_C)']:<11} | {res['Assoc(Mul_C)']:<12} | {res['Distrib(M_C/A_C)']:<17}")

if __name__ == "__main__":
    run_all_tests()