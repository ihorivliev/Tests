# Find_All_SL_Common_Monotonic_POs_Omega3.py
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
    is_alg_U = Equals(avca_algebraic_result, AVCA_U_ALG)
    is_alg_DFI1 = Equals(avca_algebraic_result, AVCA_DFI1_ALG)
    is_alg_DFI2 = Equals(avca_algebraic_result, AVCA_DFI2_ALG)
    return Ite(is_alg_U,
               Ite(Equals(avca_semantic_aspect, SEM_ZERO_ASPECT), ZUs, AUs), 
           Ite(is_alg_DFI1, DFI1s,
           Ite(is_alg_DFI2, DFI2s, AUs)))

# --- AVCA Operations (Algebraic & Aspect Determination Logic) ---
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
    pi_a_alg=pi_algebraic(s_ord_a); pi_b_alg=pi_algebraic(s_ord_b)
    avca_alg_res=avca_add_bc_omega3_algebraic(pi_a_alg,pi_b_alg)
    eff_asp_a,eff_asp_b=determine_avca_effective_aspects("add",s_ord_a,s_ord_b)
    avca_sem_asp=get_avca_result_aspect(avca_alg_res,eff_asp_a,eff_asp_b)
    return pi_inv_s_ord(avca_alg_res,avca_sem_asp)

def mapped_avca_mul_s_ord(s_ord_a: FNode, s_ord_b: FNode) -> FNode:
    pi_a_alg=pi_algebraic(s_ord_a); pi_b_alg=pi_algebraic(s_ord_b)
    avca_alg_res=avca_mul_bc_omega3_algebraic(pi_a_alg,pi_b_alg)
    eff_asp_a,eff_asp_b=determine_avca_effective_aspects("mul",s_ord_a,s_ord_b)
    avca_sem_asp=get_avca_result_aspect(avca_alg_res,eff_asp_a,eff_asp_b)
    return pi_inv_s_ord(avca_alg_res,avca_sem_asp)

def run_B1_find_all_common_monotonic_pos(min_extra_edges: int, max_models_to_find: int = 1000000000):
    print(f"\n====== SCRIPT: Find_All_SL_Common_Monotonic_POs_Omega3 (min_extra_edges={min_extra_edges}) ======")
    print(f"Purpose: Find ALL distinct POs on S_ord (Ω=3) common-monotonic for mapped AVCA ⊕ and ⊗,")
    print(f"         with at least {min_extra_edges} non-reflexive true relations (up to {max_models_to_find} models).")
    print("Expected: SAT if such POs exist, providing the 'le' relations for each.\n")

    le_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le = Symbol("le_s_ord_finder_all", le_func_type)

    base_assertions = []
    
    # --- Assert PO Axioms for 'le' function ---
    for x_refl in SMT_S_ORD_ELEMENTS: base_assertions.append(le(x_refl, x_refl)) # Reflexivity
    for x_anti in SMT_S_ORD_ELEMENTS: # Antisymmetry
        for y_anti in SMT_S_ORD_ELEMENTS:
            if x_anti.constant_value() != y_anti.constant_value():
                base_assertions.append(Implies(And(le(x_anti,y_anti), le(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in SMT_S_ORD_ELEMENTS: # Transitivity
        for y_trans in SMT_S_ORD_ELEMENTS:
            for z_trans in SMT_S_ORD_ELEMENTS:
                base_assertions.append(Implies(And(le(x_trans,y_trans), le(y_trans,z_trans)), le(x_trans,z_trans)))

    # --- Assert Monotonicity for mapped AVCA ⊕ and ⊗ ---
    monotonicity_conjuncts: List[FNode] = []
    for x1 in SMT_S_ORD_ELEMENTS:
        for y1 in SMT_S_ORD_ELEMENTS:
            premise = le(x1, y1)
            for a_mono in SMT_S_ORD_ELEMENTS:
                add_res_x1_a = mapped_avca_add_s_ord(x1, a_mono); add_res_y1_a = mapped_avca_add_s_ord(y1, a_mono)
                monotonicity_conjuncts.append(Implies(premise, le(add_res_x1_a, add_res_y1_a)))
                add_res_a_x1 = mapped_avca_add_s_ord(a_mono, x1); add_res_a_y1 = mapped_avca_add_s_ord(a_mono, y1)
                monotonicity_conjuncts.append(Implies(premise, le(add_res_a_x1, add_res_a_y1)))
                mul_res_x1_a = mapped_avca_mul_s_ord(x1, a_mono); mul_res_y1_a = mapped_avca_mul_s_ord(y1, a_mono)
                monotonicity_conjuncts.append(Implies(premise, le(mul_res_x1_a, mul_res_y1_a)))
                mul_res_a_x1 = mapped_avca_mul_s_ord(a_mono, x1); mul_res_a_y1 = mapped_avca_mul_s_ord(a_mono, y1)
                monotonicity_conjuncts.append(Implies(premise, le(mul_res_a_x1, mul_res_a_y1)))
    base_assertions.append(And(monotonicity_conjuncts))

    # --- Assert at least `min_extra_edges` non-reflexive true 'le' relations ---
    all_possible_non_reflexive_le_relations: List[FNode] = []
    for x_count_smt in SMT_S_ORD_ELEMENTS:
        for y_count_smt in SMT_S_ORD_ELEMENTS:
            if x_count_smt.constant_value() != y_count_smt.constant_value():
                all_possible_non_reflexive_le_relations.append(le(x_count_smt, y_count_smt))

    if not all_possible_non_reflexive_le_relations and min_extra_edges > 0:
        base_assertions.append(FALSE()) 
    elif all_possible_non_reflexive_le_relations:
        terms_for_sum_edges = [Ite(cond, Int(1), Int(0)) for cond in all_possible_non_reflexive_le_relations]
        sum_of_true_relations = Plus(terms_for_sum_edges) if len(terms_for_sum_edges)>1 else (terms_for_sum_edges[0] if terms_for_sum_edges else Int(0))
        base_assertions.append(GE(sum_of_true_relations, Int(min_extra_edges)))
    elif min_extra_edges > 0 : 
         base_assertions.append(FALSE())

    print(f"\n--- Solving with SMT (Z3) to find common monotonic POs (min_extra_edges={min_extra_edges}) ---")
    
    found_models_count = 0
    with Solver(name="z3", logic="QF_UFLIA") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        
        while found_models_count < max_models_to_find and s.solve():
            found_models_count += 1
            print(f"\n--- Model {found_models_count} (min_extra_edges={min_extra_edges}) ---")
            model = s.get_model()
            print("  Candidate PO True Relations (x_val <= y_val):")
            
            current_model_true_relations_tuples: List[Tuple[int,int]] = []
            output_lines = []
            num_extra_edges_in_model = 0

            for x_model_smt in SMT_S_ORD_ELEMENTS:
                x_model_py = x_model_smt.constant_value()
                for y_model_smt in SMT_S_ORD_ELEMENTS:
                    y_model_py = y_model_smt.constant_value()
                    if model.get_value(le(x_model_smt, y_model_smt)) == TRUE():
                        output_lines.append(f"  {S_ORD_ELEMENT_MAP[x_model_py]:<5} <= {S_ORD_ELEMENT_MAP[y_model_py]:<5}")
                        current_model_true_relations_tuples.append((x_model_py, y_model_py))
                        if x_model_py != y_model_py:
                            num_extra_edges_in_model +=1
            
            for line in sorted(list(set(output_lines))):
                print(line)
            print(f"  Number of non-reflexive true relations in this model: {num_extra_edges_in_model}")
            print(f"  PO Relations for B2 script: candidate_po_true_relations = {sorted(list(set(current_model_true_relations_tuples)))}")

            # Add blocking clause to find a different model for 'le'
            # This requires getting the function interpretation for 'le'
            # A simpler way to block this specific PO model is to find one relation that defines it
            # and negate it, or negate the conjunction of all its true/false values.
            # For function 'le', we need to block its interpretation.
            blocking_clause_terms = []
            for x_block_smt in SMT_S_ORD_ELEMENTS:
                for y_block_smt in SMT_S_ORD_ELEMENTS:
                    val = model.get_value(le(x_block_smt, y_block_smt))
                    if val == TRUE():
                        blocking_clause_terms.append(Not(le(x_block_smt, y_block_smt)))
                    else:
                        blocking_clause_terms.append(le(x_block_smt, y_block_smt))
            if blocking_clause_terms:
                 s.add_assertion(Or(blocking_clause_terms))
            else: # Should not happen
                break 
        
        if found_models_count == 0:
            print(f"\nSMT Result for B1 (Find Common Monotonic POs, min_extra_edges={min_extra_edges}): UNSAT")
            print(f"  INTERPRETATION: UNSAT means NO common monotonic PO could be found satisfying all conditions,")
            print(f"                  including having at least {min_extra_edges} non-reflexive true relations.")
            if min_extra_edges > 0:
                 print("                  This significantly challenges Conjecture C-2 if no non-trivial POs are found.")
            else: # min_extra_edges == 0
                 print("                  If min_extra_edges=0, an UNSAT is unexpected as the discrete PO should exist.")
        else:
            print(f"\nFound {found_models_count} distinct common monotonic PO(s) for min_extra_edges={min_extra_edges}.")

    print(f"\n====== Find_All_SL_Common_Monotonic_POs_Omega3 (min_extra_edges={min_extra_edges}) Finished ======")

# Suggestion for the if __name__ == "__main__": block of
# Find_All_SL_Common_Monotonic_POs_Omega3_v2.py (your h_deeper13.py with AU_s fix)

if __name__ == "__main__":
    print("Running Task B1 (enhanced): Exhaustively searching for common monotonic POs on S_ord for Ω=3.")
    print("This uses the full aspect-aware mapped AVCA operations.")
    
    print("\nSearching for POs with at least 0 non-reflexive edges (should find discrete PO & variants):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=0, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 1 non-reflexive edge (sparsest non-trivial):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=1, max_models_to_find=1000000000) # Increased max_models
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 2 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=2, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")
    
    print("Searching for POs with at least 3 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=3, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")
    
    print("Searching for POs with at least 4 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=4, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 5 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=5, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 6 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=6, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 7 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=7, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 8 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=8, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 9 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=9, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 10 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=10, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")



    print("Running Task B1 (enhanced): Exhaustively searching for common monotonic POs on S_ord for Ω=3.")
    print("This uses the full aspect-aware mapped AVCA operations.")
    
    print("\nSearching for POs with at least 11 non-reflexive edges (should find discrete PO & variants):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=11, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 12 non-reflexive edge (sparsest non-trivial):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=12, max_models_to_find=1000000000) # Increased max_models
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 13 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=13, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")
    
    print("Searching for POs with at least 14 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=14, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")
    
    print("Searching for POs with at least 15 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=15, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 16 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=16, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 17 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=17, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 18 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=18, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 19 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=19, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 20 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=20, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print("Searching for POs with at least 21 non-reflexive edges (critical test vs. Chapter X):")
    run_B1_find_all_common_monotonic_pos(min_extra_edges=21, max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

