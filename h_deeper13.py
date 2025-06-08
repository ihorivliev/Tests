# Find_SL_Common_Monotonic_PO_Omega3_v2.py
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
    DFI1s.constant_value(): "DFI1s", DFI2s.constant_value(): "DFI2s", 
    ZUs.constant_value(): "ZUs", AUs.constant_value(): "AUs"
}
S_ORD_PY_KEYS: List[int] = sorted(S_ORD_ELEMENT_MAP.keys())

# --- AVCA S_Ω (Algebraic Space for Ω=3) Definitions ---
AVCA_U_ALG = Int(0)
AVCA_DFI1_ALG = Int(1)
AVCA_DFI2_ALG = Int(2)
# AVCA_S_OMEGA_PY_KEYS = [0,1,2] # Not directly used but good for clarity

# --- Semantic Aspect Definitions ---
SEM_ZERO_ASPECT = Int(0) 
SEM_AREO_ASPECT = Int(1) 
SEM_DFI_ASPECT  = Int(2) 

# --- Quotient Map π and its Inverse π_inv ---
def pi_algebraic(s_ord_element_smt: FNode) -> FNode:
    return Ite(Equals(s_ord_element_smt, DFI1s), AVCA_DFI1_ALG,
           Ite(Equals(s_ord_element_smt, DFI2s), AVCA_DFI2_ALG, AVCA_U_ALG)) 

def pi_aspect_inherent(s_ord_element_smt: FNode) -> FNode:
    return Ite(Equals(s_ord_element_smt, ZUs), SEM_ZERO_ASPECT,
           Ite(Equals(s_ord_element_smt, AUs), SEM_AREO_ASPECT, SEM_DFI_ASPECT))

def pi_inv_s_ord(avca_algebraic_result: FNode, avca_semantic_aspect: FNode) -> FNode:
    """Maps an AVCA algebraic result + its semantic aspect back to an S_ord element."""
    is_alg_U = Equals(avca_algebraic_result, AVCA_U_ALG)
    is_alg_DFI1 = Equals(avca_algebraic_result, AVCA_DFI1_ALG)
    is_alg_DFI2 = Equals(avca_algebraic_result, AVCA_DFI2_ALG)

    return Ite(is_alg_U,
               Ite(Equals(avca_semantic_aspect, SEM_ZERO_ASPECT), ZUs, AUs), 
           Ite(is_alg_DFI1, DFI1s,
           Ite(is_alg_DFI2, DFI2s,
               AUs))) # Corrected: AU_s to AUs (Fallback/Error case)

# --- AVCA Operations (Algebraic & Aspect Determination Logic from B3 script) ---
def avca_add_bc_omega3_algebraic(a: FNode, b: FNode, omega: int = 3) -> FNode:
    is_a_U=Equals(a,AVCA_U_ALG); is_b_U=Equals(b,AVCA_U_ALG)
    # Ensure DFI inputs are used for sum if not U.
    # If a or b is U (0), Plus(a,b) still works if they are SMT Ints.
    s=Plus(a,b); 
    return Ite(is_a_U,b,Ite(is_b_U,a,Ite(LT(s,Int(omega)),s,AVCA_U_ALG)))

def avca_mul_bc_omega3_algebraic(a: FNode, b: FNode, omega: int = 3) -> FNode:
    is_a_U=Equals(a,AVCA_U_ALG); is_b_U=Equals(b,AVCA_U_ALG)
    # Explicit cases for Omega=3 multiplication
    cond1 = Or(is_a_U, is_b_U) # U is annihilator
    res1 = AVCA_U_ALG
    
    # DFI1_alg = 1, DFI2_alg = 2, U_alg = 0
    cond2 = And(Equals(a, AVCA_DFI1_ALG), Equals(b, AVCA_DFI1_ALG)) # 1*1
    res2 = AVCA_DFI1_ALG
    
    cond3_term1 = And(Equals(a, AVCA_DFI1_ALG), Equals(b, AVCA_DFI2_ALG)) # 1*2
    cond3_term2 = And(Equals(a, AVCA_DFI2_ALG), Equals(b, AVCA_DFI1_ALG)) # 2*1
    cond3 = Or(cond3_term1, cond3_term2)
    res3 = AVCA_DFI2_ALG
    
    # Default case is 2*2 = 4 -> U (0 for Omega=3)
    # Or any other DFI product not covered above (none for Omega=3 DFI={1,2})
    res_default_dfi_mul = AVCA_U_ALG 
    
    return Ite(cond1, res1, Ite(cond2, res2, Ite(cond3, res3, res_default_dfi_mul)))


def determine_avca_effective_aspects(op_char, s_ord_in1, s_ord_in2, omega=3) -> Tuple[FNode, FNode]:
    pi_s1_alg=pi_algebraic(s_ord_in1); pi_s2_alg=pi_algebraic(s_ord_in2)
    asp_s1_inh=pi_aspect_inherent(s_ord_in1); asp_s2_inh=pi_aspect_inherent(s_ord_in2)
    
    eff_s1=Ite(Equals(asp_s1_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s1_inh)
    eff_s2=Ite(Equals(asp_s2_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s2_inh)
    
    is_pi_s1_dfi=Not(Equals(pi_s1_alg,AVCA_U_ALG));is_pi_s2_dfi=Not(Equals(pi_s2_alg,AVCA_U_ALG))
    is_dfi_dfi_interaction=And(is_pi_s1_dfi,is_pi_s2_dfi)
    
    dfi_dfi_op_causes_saturation=FALSE()
    if op_char=="add":
        # Check DFI values for sum. pi_s1_alg, pi_s2_alg are AVCA algebraic values {0,1,2}
        # This check is only meaningful if both are DFIs.
        # The Plus works on SMT Ints.
        classical_sum_avca = Plus(pi_s1_alg,pi_s2_alg)
        dfi_dfi_op_causes_saturation=GE(classical_sum_avca,Int(omega))
    elif op_char=="mul":
        # This assumes pi_s1_alg, pi_s2_alg are DFI values (1 or 2) if is_dfi_dfi_interaction is true
        classical_prod_avca = Times(pi_s1_alg, pi_s2_alg)
        dfi_dfi_op_causes_saturation=GE(classical_prod_avca,Int(omega))
        
    eff_s1=Ite(And(is_dfi_dfi_interaction,dfi_dfi_op_causes_saturation),SEM_AREO_ASPECT,eff_s1)
    eff_s2=Ite(And(is_dfi_dfi_interaction,dfi_dfi_op_causes_saturation),SEM_AREO_ASPECT,eff_s2)
    return eff_s1,eff_s2

def get_avca_result_aspect(alg_res_avca: FNode, eff_asp_a_avca: FNode, eff_asp_b_avca: FNode) -> FNode:
    is_res_U=Equals(alg_res_avca,AVCA_U_ALG)
    res_areo_if_U=Or(Equals(eff_asp_a_avca,SEM_AREO_ASPECT),Equals(eff_asp_b_avca,SEM_AREO_ASPECT))
    return Ite(is_res_U,Ite(res_areo_if_U,SEM_AREO_ASPECT,SEM_ZERO_ASPECT),SEM_DFI_ASPECT)

# --- Mapped AVCA Operations on S_ord ---
def mapped_avca_add_s_ord(s_ord_a: FNode, s_ord_b: FNode) -> FNode:
    pi_a_alg = pi_algebraic(s_ord_a)
    pi_b_alg = pi_algebraic(s_ord_b)
    avca_alg_res = avca_add_bc_omega3_algebraic(pi_a_alg, pi_b_alg)
    eff_asp_a, eff_asp_b = determine_avca_effective_aspects("add", s_ord_a, s_ord_b)
    avca_sem_asp = get_avca_result_aspect(avca_alg_res, eff_asp_a, eff_asp_b)
    return pi_inv_s_ord(avca_alg_res, avca_sem_asp)

def mapped_avca_mul_s_ord(s_ord_a: FNode, s_ord_b: FNode) -> FNode:
    pi_a_alg = pi_algebraic(s_ord_a)
    pi_b_alg = pi_algebraic(s_ord_b)
    avca_alg_res = avca_mul_bc_omega3_algebraic(pi_a_alg, pi_b_alg)
    eff_asp_a, eff_asp_b = determine_avca_effective_aspects("mul", s_ord_a, s_ord_b)
    avca_sem_asp = get_avca_result_aspect(avca_alg_res, eff_asp_a, eff_asp_b)
    return pi_inv_s_ord(avca_alg_res, avca_sem_asp)

def run_B1_find_common_monotonic_po(min_extra_edges: int):
    print(f"\n====== SCRIPT: Find_SL_Common_Monotonic_PO_Omega3 (min_extra_edges={min_extra_edges}) ======")
    print(f"Purpose: Find a PO on S_ord (Ω=3) that is common-monotonic for mapped AVCA ⊕ and ⊗,")
    print(f"         and has at least {min_extra_edges} non-reflexive true relations.")
    print("Expected: SAT if such a PO exists, providing the 'le' relations.\n")

    le_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le = Symbol("le_s_ord_finder", le_func_type)

    assertions = []
    
    print("--- Asserting PO Axioms for 'le' function ---")
    for x_refl in SMT_S_ORD_ELEMENTS: assertions.append(le(x_refl, x_refl))
    for x_anti in SMT_S_ORD_ELEMENTS:
        for y_anti in SMT_S_ORD_ELEMENTS:
            if x_anti.constant_value() != y_anti.constant_value():
                assertions.append(Implies(And(le(x_anti,y_anti), le(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in SMT_S_ORD_ELEMENTS:
        for y_trans in SMT_S_ORD_ELEMENTS:
            for z_trans in SMT_S_ORD_ELEMENTS:
                assertions.append(Implies(And(le(x_trans,y_trans), le(y_trans,z_trans)), le(x_trans,z_trans)))

    print("\n--- Asserting Monotonicity for mapped AVCA ⊕ and ⊗ ---")
    # Monotonicity: le(x1,y1) => le(op(x1,a), op(y1,a)) AND le(op(a,x1), op(a,y1))
    for x1 in SMT_S_ORD_ELEMENTS:
        for y1 in SMT_S_ORD_ELEMENTS:
            premise = le(x1, y1)
            for a_mono in SMT_S_ORD_ELEMENTS:
                add_res_x1_a = mapped_avca_add_s_ord(x1, a_mono)
                add_res_y1_a = mapped_avca_add_s_ord(y1, a_mono)
                assertions.append(Implies(premise, le(add_res_x1_a, add_res_y1_a)))
                
                add_res_a_x1 = mapped_avca_add_s_ord(a_mono, x1)
                add_res_a_y1 = mapped_avca_add_s_ord(a_mono, y1)
                assertions.append(Implies(premise, le(add_res_a_x1, add_res_a_y1)))

                mul_res_x1_a = mapped_avca_mul_s_ord(x1, a_mono)
                mul_res_y1_a = mapped_avca_mul_s_ord(y1, a_mono)
                assertions.append(Implies(premise, le(mul_res_x1_a, mul_res_y1_a)))

                mul_res_a_x1 = mapped_avca_mul_s_ord(a_mono, x1)
                mul_res_a_y1 = mapped_avca_mul_s_ord(a_mono, y1)
                assertions.append(Implies(premise, le(mul_res_a_x1, mul_res_a_y1)))

    print(f"\n--- Asserting at least {min_extra_edges} non-reflexive true 'le' relations ---")
    non_reflexive_le_conditions: List[FNode] = []
    for x_nr_idx, x_nr in enumerate(SMT_S_ORD_ELEMENTS):
        for y_nr in SMT_S_ORD_ELEMENTS[x_nr_idx+1:]: # Ensures x_nr != y_nr and avoids duplicate pairs (x,y), (y,x)
            non_reflexive_le_conditions.append(le(x_nr, y_nr))
            non_reflexive_le_conditions.append(le(y_nr, x_nr)) 
            # We want to count true relations, not just pairs.
            # A simpler way: count ITE(le(x,y),1,0) for all x!=y pairs.
            
    # Corrected way to count non-reflexive true relations
    all_possible_non_reflexive_le_relations: List[FNode] = []
    for x_count_smt in SMT_S_ORD_ELEMENTS:
        for y_count_smt in SMT_S_ORD_ELEMENTS:
            if x_count_smt.constant_value() != y_count_smt.constant_value():
                all_possible_non_reflexive_le_relations.append(le(x_count_smt, y_count_smt))

    if not all_possible_non_reflexive_le_relations and min_extra_edges > 0:
        print(f"Warning: No non-reflexive pairs exist to count for min_extra_edges={min_extra_edges}.") # Should not happen for size 4 set
        assertions.append(FALSE()) 
    elif all_possible_non_reflexive_le_relations:
        terms_for_sum_edges = [Ite(cond, Int(1), Int(0)) for cond in all_possible_non_reflexive_le_relations]
        sum_of_true_relations = Plus(terms_for_sum_edges) if len(terms_for_sum_edges) > 1 else (terms_for_sum_edges[0] if terms_for_sum_edges else Int(0))
        assertions.append(GE(sum_of_true_relations, Int(min_extra_edges)))
    elif min_extra_edges > 0 : # No relations, but min_extra_edges > 0
         assertions.append(FALSE())


    print("\n--- Solving with SMT (Z3) to find a common monotonic PO ---")
    with Solver(name="z3", logic="QF_UFLIA") as s: 
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for B1 (Find Common Monotonic PO, min_extra_edges={min_extra_edges}): {'SAT' if result else 'UNSAT'}")

        if result:
            print(f"  INTERPRETATION: SAT means a common monotonic PO with at least {min_extra_edges} non-reflexive true relations was found.")
            model = s.get_model()
            print("  Candidate PO True Relations (x_val <= y_val):")
            found_relations_tuples: List[Tuple[int,int]] = []
            output_lines = []
            for x_model_smt_outer in SMT_S_ORD_ELEMENTS:
                x_model_py_outer = x_model_smt_outer.constant_value()
                for y_model_smt_outer in SMT_S_ORD_ELEMENTS:
                    y_model_py_outer = y_model_smt_outer.constant_value()
                    if model.get_value(le(x_model_smt_outer, y_model_smt_outer)) == TRUE():
                        output_lines.append(f"  {S_ORD_ELEMENT_MAP[x_model_py_outer]:<5} <= {S_ORD_ELEMENT_MAP[y_model_py_outer]:<5}")
                        found_relations_tuples.append((x_model_py_outer, y_model_py_outer))
            
            for line in sorted(list(set(output_lines))): # Print unique relations
                print(line)
            print("\n  This PO can now be fed into Test_C2_SL_DistributiveLattice_Checker.py (Task B2).")
            print(f"  PO Relations for B2 script: candidate_po_true_relations = {sorted(list(set(found_relations_tuples)))}") # Ensure unique pairs for input
        else: 
            print(f"  INTERPRETATION: UNSAT means NO common monotonic PO could be found satisfying all conditions,")
            print(f"                  including having at least {min_extra_edges} non-reflexive true relations.")

    print(f"\n====== Find_SL_Common_Monotonic_PO_Omega3 (min_extra_edges={min_extra_edges}) Finished ======")

if __name__ == "__main__":
    # run_B1_find_common_monotonic_po(min_extra_edges=1) 
    # print("\n" + "="*70 + "\n")
    run_B1_find_common_monotonic_po(min_extra_edges=2) 
    print("\n" + "="*70 + "\n")
    run_B1_find_common_monotonic_po(min_extra_edges=3)
    # print("\n" + "="*70 + "\n")
    # run_B1_find_common_monotonic_po(min_extra_edges=4)
    # print("\n" + "="*70 + "\n")
    # run_B1_find_common_monotonic_po(min_extra_edges=5)
    # print("\n" + "="*70 + "\n")
    # run_B1_find_common_monotonic_po(min_extra_edges=6)