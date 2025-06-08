# Debug_Monotonicity_For_Known_PO_Omega3_v2.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, Function, GE, LT)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable, Literal, Union, Set

# --- S_ord (Semantic Space for Ω=3) Definitions ---
DFI1s, DFI2s, ZUs, AUs = Int(0), Int(1), Int(2), Int(3) 
SMT_S_ORD_ELEMENTS: List[FNode] = [DFI1s, DFI2s, ZUs, AUs] 

S_ORD_ELEMENT_MAP: Dict[int, str] = {
    DFI1s.constant_value(): "DFI1s", 
    DFI2s.constant_value(): "DFI2s", 
    ZUs.constant_value(): "ZUs", 
    AUs.constant_value(): "AUs"
}
S_ORD_PY_KEYS: List[int] = sorted(S_ORD_ELEMENT_MAP.keys()) # Defined globally

# --- AVCA S_Ω (Algebraic Space for Ω=3) Definitions ---
AVCA_U_ALG = Int(0)
AVCA_DFI1_ALG = Int(1)
AVCA_DFI2_ALG = Int(2)

# --- Semantic Aspect Definitions ---
SEM_ZERO_ASPECT = Int(0) 
SEM_AREO_ASPECT = Int(1) 
SEM_DFI_ASPECT  = Int(2) 

# --- Quotient Map π and its Inverse π_inv (Copied from Find_SL_Common_Monotonic_PO_Omega3_v2.py) ---
def pi_algebraic(s_ord_element_smt: FNode) -> FNode:
    return Ite(Equals(s_ord_element_smt, DFI1s), AVCA_DFI1_ALG,
           Ite(Equals(s_ord_element_smt, DFI2s), AVCA_DFI2_ALG, AVCA_U_ALG)) 

def pi_aspect_inherent(s_ord_element_smt: FNode) -> FNode:
    return Ite(Equals(s_ord_element_smt, ZUs), SEM_ZERO_ASPECT,
           Ite(Equals(s_ord_element_smt, AUs), SEM_AREO_ASPECT, SEM_DFI_ASPECT))

def pi_inv_s_ord(avca_algebraic_result: FNode, avca_semantic_aspect: FNode) -> FNode:
    is_alg_U = Equals(avca_algebraic_result, AVCA_U_ALG)
    is_alg_DFI1 = Equals(avca_algebraic_result, AVCA_DFI1_ALG)
    is_alg_DFI2 = Equals(avca_algebraic_result, AVCA_DFI2_ALG)
    return Ite(is_alg_U,
               Ite(Equals(avca_semantic_aspect, SEM_ZERO_ASPECT), ZUs, AUs), 
           Ite(is_alg_DFI1, DFI1s,
           Ite(is_alg_DFI2, DFI2s, AUs)))

def avca_add_bc_omega3_algebraic(a: FNode, b: FNode, omega: int = 3) -> FNode:
    is_a_U=Equals(a,AVCA_U_ALG); is_b_U=Equals(b,AVCA_U_ALG)
    s=Plus(a,b); return Ite(is_a_U,b,Ite(is_b_U,a,Ite(LT(s,Int(omega)),s,AVCA_U_ALG)))

def avca_mul_bc_omega3_algebraic(a: FNode, b: FNode, omega: int = 3) -> FNode:
    is_a_U=Equals(a,AVCA_U_ALG); is_b_U=Equals(b,AVCA_U_ALG)
    c1=Or(is_a_U,is_b_U);r1=AVCA_U_ALG
    c2=And(Equals(a,AVCA_DFI1_ALG),Equals(b,AVCA_DFI1_ALG));r2=AVCA_DFI1_ALG
    c3=Or(And(Equals(a,AVCA_DFI1_ALG),Equals(b,AVCA_DFI2_ALG)), \
          And(Equals(a,AVCA_DFI2_ALG),Equals(b,AVCA_DFI1_ALG)));r3=AVCA_DFI2_ALG
    r4=AVCA_U_ALG
    return Ite(c1,r1,Ite(c2,r2,Ite(c3,r3,r4)))

def determine_avca_effective_aspects(op_char, s_ord_in1, s_ord_in2, omega=3) -> Tuple[FNode, FNode]:
    pi_s1_alg=pi_algebraic(s_ord_in1); pi_s2_alg=pi_algebraic(s_ord_in2)
    asp_s1_inh=pi_aspect_inherent(s_ord_in1); asp_s2_inh=pi_aspect_inherent(s_ord_in2)
    eff_s1=Ite(Equals(asp_s1_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s1_inh)
    eff_s2=Ite(Equals(asp_s2_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s2_inh)
    is_pi_s1_dfi=Not(Equals(pi_s1_alg,AVCA_U_ALG));is_pi_s2_dfi=Not(Equals(pi_s2_alg,AVCA_U_ALG))
    is_dfi_dfi_interaction=And(is_pi_s1_dfi,is_pi_s2_dfi)
    causes_sat=FALSE()
    if op_char=="add": causes_sat=GE(Plus(pi_s1_alg,pi_s2_alg),Int(omega))
    elif op_char=="mul": causes_sat=GE(Times(pi_s1_alg,pi_s2_alg),Int(omega))
    eff_s1=Ite(And(is_dfi_dfi_interaction,causes_sat),SEM_AREO_ASPECT,eff_s1)
    eff_s2=Ite(And(is_dfi_dfi_interaction,causes_sat),SEM_AREO_ASPECT,eff_s2)
    return eff_s1,eff_s2

def get_avca_result_aspect(alg_res_avca: FNode, eff_asp_a_avca: FNode, eff_asp_b_avca: FNode) -> FNode:
    is_res_U=Equals(alg_res_avca,AVCA_U_ALG)
    res_areo_if_U=Or(Equals(eff_asp_a_avca,SEM_AREO_ASPECT),Equals(eff_asp_b_avca,SEM_AREO_ASPECT))
    return Ite(is_res_U,Ite(res_areo_if_U,SEM_AREO_ASPECT,SEM_ZERO_ASPECT),SEM_DFI_ASPECT)

def mapped_avca_add_s_ord(s_ord_a: FNode, s_ord_b: FNode) -> FNode:
    pi_a_alg = pi_algebraic(s_ord_a); pi_b_alg = pi_algebraic(s_ord_b)
    avca_alg_res = avca_add_bc_omega3_algebraic(pi_a_alg, pi_b_alg)
    eff_asp_a, eff_asp_b = determine_avca_effective_aspects("add", s_ord_a, s_ord_b)
    avca_sem_asp = get_avca_result_aspect(avca_alg_res, eff_asp_a, eff_asp_b)
    return pi_inv_s_ord(avca_alg_res, avca_sem_asp)

def mapped_avca_mul_s_ord(s_ord_a: FNode, s_ord_b: FNode) -> FNode:
    pi_a_alg = pi_algebraic(s_ord_a); pi_b_alg = pi_algebraic(s_ord_b)
    avca_alg_res = avca_mul_bc_omega3_algebraic(pi_a_alg, pi_b_alg)
    eff_asp_a, eff_asp_b = determine_avca_effective_aspects("mul", s_ord_a, s_ord_b)
    avca_sem_asp = get_avca_result_aspect(avca_alg_res, eff_asp_a, eff_asp_b)
    return pi_inv_s_ord(avca_alg_res, avca_sem_asp)

def run_B1_debug_monotonicity_for_known_po(
    po_name: str,
    known_po_true_relations_int: List[Tuple[int,int]] 
):
    print(f"\n====== SCRIPT: Debug_Monotonicity_For_Known_PO_Omega3 (PO: {po_name}) ======")
    print(f"Purpose: Test if a KNOWN PO on S_ord (Ω=3) is common-monotonic for mapped AVCA ⊕ and ⊗")
    print(f"         using the mapping logic from Find_SL_Common_Monotonic_PO_Omega3_v2.py.")
    # Corrected: Using S_ORD_ELEMENT_MAP which is global
    print(f"Input True Non-Reflexive Relations (x_val <= y_val): {[(S_ORD_ELEMENT_MAP[x], S_ORD_ELEMENT_MAP[y]) for x,y in known_po_true_relations_int]}")
    print("Expected: SAT if this PO is indeed common monotonic with current mapped ops.\n")

    le_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    # Using a more unique name for the 'le' function to avoid SMT symbol clashes if run in series
    le_smt_func_name = f"le_{po_name.replace(' ','_').replace('≤','le').replace(',','').replace('(','').replace(')','')}"
    le = Symbol(le_smt_func_name, le_func_type) 

    assertions = []
    
    print("--- Defining the specific PO via 'le' function axioms ---")
    # Define 'le' function based on known_po_true_relations_int plus reflexivity
    all_true_relations_for_le_py_keys: Set[Tuple[int,int]] = set()
    for x_py_key in S_ORD_PY_KEYS: # S_ORD_PY_KEYS is now correctly global
        all_true_relations_for_le_py_keys.add((x_py_key, x_py_key)) # Add reflexive
    for lesser_py, greater_py in known_po_true_relations_int: # Add given non-reflexive
        all_true_relations_for_le_py_keys.add((lesser_py, greater_py))

    for x_smt_po_def in SMT_S_ORD_ELEMENTS:
        for y_smt_po_def in SMT_S_ORD_ELEMENTS:
            if (x_smt_po_def.constant_value(), y_smt_po_def.constant_value()) in all_true_relations_for_le_py_keys:
                assertions.append(le(x_smt_po_def, y_smt_po_def))
            else:
                assertions.append(Not(le(x_smt_po_def, y_smt_po_def)))
    
    print("--- Asserting PO Axioms for the defined 'le' relation (for consistency check of input PO) ---")
    for x_refl in SMT_S_ORD_ELEMENTS: assertions.append(le(x_refl, x_refl)) # Should be entailed if PO is well-defined
    for x_anti in SMT_S_ORD_ELEMENTS:
        for y_anti in SMT_S_ORD_ELEMENTS:
            # No need for x_anti.constant_value() != y_anti.constant_value() if asserting general antisymmetry
            assertions.append(Implies(And(le(x_anti,y_anti), le(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in SMT_S_ORD_ELEMENTS:
        for y_trans in SMT_S_ORD_ELEMENTS:
            for z_trans in SMT_S_ORD_ELEMENTS:
                assertions.append(Implies(And(le(x_trans,y_trans), le(y_trans,z_trans)), le(x_trans,z_trans)))

    print("\n--- Asserting Monotonicity for mapped AVCA ⊕ and ⊗ with this PO ---")
    monotonicity_conjuncts: List[FNode] = []
    for x1 in SMT_S_ORD_ELEMENTS:
        for y1 in SMT_S_ORD_ELEMENTS:
            premise = le(x1, y1)
            for a_mono in SMT_S_ORD_ELEMENTS:
                # For mapped AVCA Add
                add_res_x1_a = mapped_avca_add_s_ord(x1, a_mono)
                add_res_y1_a = mapped_avca_add_s_ord(y1, a_mono)
                monotonicity_conjuncts.append(Implies(premise, le(add_res_x1_a, add_res_y1_a)))
                
                add_res_a_x1 = mapped_avca_add_s_ord(a_mono, x1)
                add_res_a_y1 = mapped_avca_add_s_ord(a_mono, y1)
                monotonicity_conjuncts.append(Implies(premise, le(add_res_a_x1, add_res_a_y1)))

                # For mapped AVCA Mul
                mul_res_x1_a = mapped_avca_mul_s_ord(x1, a_mono)
                mul_res_y1_a = mapped_avca_mul_s_ord(y1, a_mono)
                monotonicity_conjuncts.append(Implies(premise, le(mul_res_x1_a, mul_res_y1_a)))

                mul_res_a_x1 = mapped_avca_mul_s_ord(a_mono, x1)
                mul_res_a_y1 = mapped_avca_mul_s_ord(a_mono, y1)
                monotonicity_conjuncts.append(Implies(premise, le(mul_res_a_x1, mul_res_a_y1)))
    
    assertions.append(And(monotonicity_conjuncts))

    print("\n--- Solving with SMT (Z3) to check if PO is common monotonic ---")
    with Solver(name="z3", logic="QF_UFLIA") as s: 
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Debug Monotonicity (PO: {po_name}): {'SAT' if result else 'UNSAT'}")

        if result:
            print(f"  INTERPRETATION: SAT means the provided PO '{po_name}' IS common monotonic")
            print("                  for the mapped AVCA ⊕ and ⊗ operations as defined in this script.")
            print("                  This implies the 'Find_SL_Common_Monotonic_PO_Omega3_v2.py' script")
            print(f"                  should ideally be able to find this PO (or one with more edges).")
            print("                  If the Finder script got UNSAT for a min_extra_edges count consistent")
            print("                  with this PO, there might be a subtle difference in constraints or search.")

        else: 
            print(f"  INTERPRETATION: UNSAT means the provided PO '{po_name}' IS NOT common monotonic")
            print("                  for the mapped AVCA ⊕ and ⊗ operations as defined in this script.")
            print("                  This could explain why 'Find_SL_Common_Monotonic_PO_Omega3_v2.py' yielded UNSAT,")
            print("                  if its mapped ops/monotonicity logic matches this script and is correct,")
            print("                  and the PO from Chapter X was based on different/simpler mapped ops.")

    print(f"\n====== Debug_Monotonicity_For_Known_PO_Omega3 (PO: {po_name}) Finished ======")

if __name__ == "__main__":
    # From AVCA Core DraftV4 Chapter X (H-O1 section), for Ω=3, test_ops=["add", "mul"], min_extra_edges=2
    # Report: "a common monotonic order: DFI1sem ≤ AUsem and ZUs_em ≤ AUsem (with DFI2sem isolated)."
    # S_ord: DFI1s=0, DFI2s=1, ZUs=2, AUs=3
    # This PO's true non-reflexive relations: (0,3) [DFI1s≤AUs], (2,3) [ZUs≤AUs]. DFI2s is only <= itself.
    
    ch_x_po_name = "ChapterX_min_edges_2_PO_DFI2iso"
    # Input to script is only the *non-reflexive* true relations. Reflexivity is added by the script.
    ch_x_po_non_reflexive_true_relations = [ 
        (0,3), # DFI1s <= AUs
        (2,3)  # ZUs <= AUs
    ]
    run_B1_debug_monotonicity_for_known_po(
        po_name=ch_x_po_name,
        known_po_true_relations_int = ch_x_po_non_reflexive_true_relations
    )
    
    print("\n" + "="*70 + "\n")

    # For comparison, the PO that FAILED the lattice check in user's prior output
    # Hasse: DFI1s -> DFI2s -> AUs and ZUs -> AUs.
    # Non-reflexive true relations: (0,1), (1,3), (2,3), (0,3) [DFI1s≤AUs by transitivity or explicit]
    failed_lattice_po_name = "AuditorFailedLatticeTestPO_DFI1-DFI2-AU_ZU-AU"
    failed_lattice_po_non_reflexive_true_relations = [
        (0,1), # DFI1s <= DFI2s
        (1,3), # DFI2s <= AUs
        (2,3), # ZUs <= AUs
        (0,3)  # DFI1s <= AUs
    ]
    run_B1_debug_monotonicity_for_known_po(
        po_name=failed_lattice_po_name,
        known_po_true_relations_int=failed_lattice_po_non_reflexive_true_relations
    )