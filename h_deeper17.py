# Find_All_SL_Common_Monotonic_POs_OmegaN.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, Function, GE, LT)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable, Literal, Union, Set

# --- Global Mappings (will be initialized by current_omega) ---
SMT_S_ORD_ELEMENTS: List[FNode] = []
S_ORD_ELEMENT_MAP: Dict[int, str] = {} # Python int key to string name
S_ORD_PY_KEYS: List[int] = []

AVCA_U_ALG_SMT: FNode # Will be Int(0)
AVCA_DFI_ALG_SMT_MAP: Dict[int, FNode] = {} # Python DFI value (1 to omega-1) to SMT Int FNode
AVCA_S_OMEGA_PY_KEYS: List[int] = []

# --- Semantic Aspect Definitions (Global) ---
SEM_ZERO_ASPECT = Int(0) 
SEM_AREO_ASPECT = Int(1) 
SEM_DFI_ASPECT  = Int(2) # Placeholder for non-Unio aspects

# --- Helper to initialize globals based on Omega ---
def initialize_omega_dependent_globals(current_omega: int):
    global SMT_S_ORD_ELEMENTS, S_ORD_ELEMENT_MAP, S_ORD_PY_KEYS
    global AVCA_U_ALG_SMT, AVCA_DFI_ALG_SMT_MAP, AVCA_S_OMEGA_PY_KEYS

    if current_omega < 1:
        raise ValueError("current_omega must be >= 1")

    SMT_S_ORD_ELEMENTS = []
    S_ORD_ELEMENT_MAP = {}
    
    # S_ord: (omega-1) DFIs_sem, ZUs, AUs  (Total omega+1 elements)
    # Mapping: DFIsem_1 -> 0, ..., DFIsem_omega-1 -> omega-2
    #          ZUs -> omega-1
    #          AUs -> omega
    for i in range(current_omega - 1): # DFIsem_1 to DFIsem_(omega-1)
        dfi_sem_val = i
        SMT_S_ORD_ELEMENTS.append(Int(dfi_sem_val))
        S_ORD_ELEMENT_MAP[dfi_sem_val] = f"DFIs{i+1}"
    
    zu_s_val = current_omega - 1
    au_s_val = current_omega
    SMT_S_ORD_ELEMENTS.append(Int(zu_s_val))
    S_ORD_ELEMENT_MAP[zu_s_val] = "ZUs"
    SMT_S_ORD_ELEMENTS.append(Int(au_s_val))
    S_ORD_ELEMENT_MAP[au_s_val] = "AUs"
    S_ORD_PY_KEYS = sorted(S_ORD_ELEMENT_MAP.keys())

    # AVCA S_Omega (Algebraic): U_alg, DFI_alg_1 ... DFI_alg_omega-1 (Total omega elements)
    # Mapping: U_alg -> 0
    #          DFI_alg_1 -> 1, ..., DFI_alg_omega-1 -> omega-1
    AVCA_U_ALG_SMT = Int(0)
    AVCA_DFI_ALG_SMT_MAP = {}
    AVCA_S_OMEGA_PY_KEYS = [0]
    if current_omega > 1:
        for i in range(1, current_omega):
            AVCA_DFI_ALG_SMT_MAP[i] = Int(i) # DFI value i maps to SMT Int(i)
            AVCA_S_OMEGA_PY_KEYS.append(i)

# --- Quotient Map π and its Inverse π_inv (Omega-Parametric) ---
def pi_algebraic(s_ord_element_smt: FNode, current_omega: int) -> FNode:
    # s_ord_element_smt is an Int representing an S_ord element
    # Maps DFIsem_i (val i-1) to DFIalg_i (val i)
    # Maps ZUs (val omega-1) and AUs (val omega) to Ualg (val 0)
    
    # Default to U_alg
    result = AVCA_U_ALG_SMT 
    # For DFIsem_j (value j = 0 to omega-2) -> DFIalg_(j+1) (value j+1)
    conditions = []
    for i in range(current_omega - 1): # DFIsem values 0 to omega-2
        dfi_sem_val = i
        dfi_alg_val = i + 1
        conditions.append(Ite(Equals(s_ord_element_smt, Int(dfi_sem_val)), 
                              AVCA_DFI_ALG_SMT_MAP.get(dfi_alg_val, AVCA_U_ALG_SMT), # Should always find
                              result)) # progressively build nested ITEs
        result = conditions[-1]
    return result

def pi_aspect_inherent(s_ord_element_smt: FNode, current_omega: int) -> FNode:
    zu_s_val = current_omega - 1
    au_s_val = current_omega
    return Ite(Equals(s_ord_element_smt, Int(zu_s_val)), SEM_ZERO_ASPECT,
           Ite(Equals(s_ord_element_smt, Int(au_s_val)), SEM_AREO_ASPECT, 
           SEM_DFI_ASPECT))

def pi_inv_s_ord(avca_algebraic_result: FNode, avca_semantic_aspect: FNode, current_omega: int) -> FNode:
    is_alg_U = Equals(avca_algebraic_result, AVCA_U_ALG_SMT)
    
    # Default for errors or non-U DFI if logic below fails (shouldn't happen)
    s_ord_dfi_fallback = Int(current_omega) # AUs as fallback if not U

    # Build ITE chain for DFIalg_i -> DFIsem_i (value i -> value i-1)
    current_dfi_map_result = s_ord_dfi_fallback
    if current_omega > 1:
        for i in range(current_omega - 1, 0, -1): # Iterate DFI alg values omega-1 down to 1
            dfi_alg_val = i
            dfi_sem_val = i - 1 # Corresponding S_ord DFIsem value
            current_dfi_map_result = Ite(Equals(avca_algebraic_result, AVCA_DFI_ALG_SMT_MAP[dfi_alg_val]),
                                         Int(dfi_sem_val),
                                         current_dfi_map_result)
                                         
    zu_s_val = current_omega - 1
    au_s_val = current_omega
    return Ite(is_alg_U,
               Ite(Equals(avca_semantic_aspect, SEM_ZERO_ASPECT), Int(zu_s_val), Int(au_s_val)), 
               current_dfi_map_result)

# --- AVCA Operations (Algebraic & Aspect Determination Logic - Omega Parametric) ---
def avca_add_bc_omegaN_algebraic(a: FNode, b: FNode, current_omega: int) -> FNode:
    is_a_U = Equals(a, AVCA_U_ALG_SMT)
    is_b_U = Equals(b, AVCA_U_ALG_SMT)
    # Assume a,b are already SMT Ints representing AVCA S_Omega values
    dfi_sum_val = Plus(a,b)
    return Ite(is_a_U, b, Ite(is_b_U, a, 
           Ite(LT(dfi_sum_val, Int(current_omega)), dfi_sum_val, AVCA_U_ALG_SMT)))

def avca_mul_bc_omegaN_algebraic(a: FNode, b: FNode, current_omega: int) -> FNode:
    is_a_U = Equals(a, AVCA_U_ALG_SMT)
    is_b_U = Equals(b, AVCA_U_ALG_SMT)
    
    # Fallback for DFI*DFI is overflow to U
    dfi_prod_result_final = AVCA_U_ALG_SMT
    
    # Build ITE chain for DFI*DFI classical products
    # This has to be done carefully for general Omega
    # For this script, let's assume omega is small enough (e.g. <=5)
    # that we can pre-calculate or hardcode some common products if needed,
    # or rely on Times() and the overflow check.
    if current_omega > 1:
        # If both a and b are DFI
        prod_val = Times(a, b)
        is_classical_prod = And(GE(prod_val, Int(1)), LT(prod_val, Int(current_omega)))
        dfi_prod_result_final = Ite(is_classical_prod, prod_val, AVCA_U_ALG_SMT)

    return Ite(Or(is_a_U, is_b_U), AVCA_U_ALG_SMT, dfi_prod_result_final)


def determine_avca_effective_aspects(op_char, s_ord_in1, s_ord_in2, current_omega) -> Tuple[FNode, FNode]:
    pi_s1_alg = pi_algebraic(s_ord_in1, current_omega)
    pi_s2_alg = pi_algebraic(s_ord_in2, current_omega)
    asp_s1_inh = pi_aspect_inherent(s_ord_in1, current_omega)
    asp_s2_inh = pi_aspect_inherent(s_ord_in2, current_omega)
    
    eff_s1 = Ite(Equals(asp_s1_inh,SEM_DFI_ASPECT), SEM_ZERO_ASPECT, asp_s1_inh)
    eff_s2 = Ite(Equals(asp_s2_inh,SEM_DFI_ASPECT), SEM_ZERO_ASPECT, asp_s2_inh)
    
    is_pi_s1_dfi = Not(Equals(pi_s1_alg, AVCA_U_ALG_SMT))
    is_pi_s2_dfi = Not(Equals(pi_s2_alg, AVCA_U_ALG_SMT))
    is_dfi_dfi_interaction = And(is_pi_s1_dfi, is_pi_s2_dfi)
    
    dfi_dfi_op_causes_saturation = FALSE()
    if op_char=="add": 
        classical_sum_avca = Plus(pi_s1_alg, pi_s2_alg)
        dfi_dfi_op_causes_saturation = GE(classical_sum_avca, Int(current_omega))
    elif op_char=="mul": 
        classical_prod_avca = Times(pi_s1_alg, pi_s2_alg) # This assumes DFI values for pi_s1/s2_alg
        # Check if product is DFI (>=1) before comparing with current_omega for overflow
        is_actual_prod_overflow = And(GE(classical_prod_avca, Int(1)), GE(classical_prod_avca, Int(current_omega)))
        # Or if prod is 0 (e.g. if 0 was allowed as DFI value, but here DFIalg > 0)
        # For current setup DFIalg*DFIalg will be >=1. So just check GE current_omega.
        dfi_dfi_op_causes_saturation = GE(classical_prod_avca, Int(current_omega))
        
    eff_s1 = Ite(And(is_dfi_dfi_interaction, dfi_dfi_op_causes_saturation), SEM_AREO_ASPECT, eff_s1)
    eff_s2 = Ite(And(is_dfi_dfi_interaction, dfi_dfi_op_causes_saturation), SEM_AREO_ASPECT, eff_s2)
    return eff_s1, eff_s2

def get_avca_result_aspect(alg_res_avca: FNode, eff_asp_a_avca: FNode, eff_asp_b_avca: FNode) -> FNode:
    is_res_U = Equals(alg_res_avca, AVCA_U_ALG_SMT)
    res_areo_if_U = Or(Equals(eff_asp_a_avca, SEM_AREO_ASPECT), Equals(eff_asp_b_avca, SEM_AREO_ASPECT))
    return Ite(is_res_U, Ite(res_areo_if_U, SEM_AREO_ASPECT, SEM_ZERO_ASPECT), SEM_DFI_ASPECT)

# --- Mapped AVCA Operations on S_ord (Omega-Parametric) ---
def mapped_avca_add_s_ord(s_ord_a: FNode, s_ord_b: FNode, current_omega: int) -> FNode:
    pi_a_alg = pi_algebraic(s_ord_a, current_omega)
    pi_b_alg = pi_algebraic(s_ord_b, current_omega)
    avca_alg_res = avca_add_bc_omegaN_algebraic(pi_a_alg, pi_b_alg, current_omega)
    eff_asp_a, eff_asp_b = determine_avca_effective_aspects("add", s_ord_a, s_ord_b, current_omega)
    avca_sem_asp = get_avca_result_aspect(avca_alg_res, eff_asp_a, eff_asp_b)
    return pi_inv_s_ord(avca_alg_res, avca_sem_asp, current_omega)

def mapped_avca_mul_s_ord(s_ord_a: FNode, s_ord_b: FNode, current_omega: int) -> FNode:
    pi_a_alg = pi_algebraic(s_ord_a, current_omega)
    pi_b_alg = pi_algebraic(s_ord_b, current_omega)
    avca_alg_res = avca_mul_bc_omegaN_algebraic(pi_a_alg, pi_b_alg, current_omega)
    eff_asp_a, eff_asp_b = determine_avca_effective_aspects("mul", s_ord_a, s_ord_b, current_omega)
    avca_sem_asp = get_avca_result_aspect(avca_alg_res, eff_asp_a, eff_asp_b)
    return pi_inv_s_ord(avca_alg_res, avca_sem_asp, current_omega)

def run_B1_find_all_common_monotonic_pos_omegaN(current_omega: int, min_extra_edges: int, max_models_to_find: int = 1000000000):
    initialize_omega_dependent_globals(current_omega) # Initialize globals for this Omega

    print(f"\n====== SCRIPT: Find_All_SL_Common_Monotonic_POs_OmegaN (Ω={current_omega}, min_extra_edges={min_extra_edges}) ======")
    print(f"Purpose: Find ALL distinct POs on S_ord (size {current_omega+1}) common-monotonic for mapped AVCA ⊕ and ⊗,")
    print(f"         with at least {min_extra_edges} non-reflexive true relations (up to {max_models_to_find} models).")
    print("Expected: SAT if such POs exist, providing the 'le' relations for each.\n")

    le_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    # Use current_omega in symbol name for uniqueness if looping outside
    le = Symbol(f"le_s_ord_finder_O{current_omega}", le_func_type) 

    base_assertions = []
    
    print("--- Asserting PO Axioms for 'le' function ---")
    for x_refl in SMT_S_ORD_ELEMENTS: base_assertions.append(le(x_refl, x_refl))
    for x_anti in SMT_S_ORD_ELEMENTS:
        for y_anti in SMT_S_ORD_ELEMENTS:
            if x_anti.constant_value() != y_anti.constant_value(): # Optimization
                base_assertions.append(Implies(And(le(x_anti,y_anti), le(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in SMT_S_ORD_ELEMENTS:
        for y_trans in SMT_S_ORD_ELEMENTS:
            for z_trans in SMT_S_ORD_ELEMENTS:
                base_assertions.append(Implies(And(le(x_trans,y_trans), le(y_trans,z_trans)), le(x_trans,z_trans)))

    print("\n--- Asserting Monotonicity for mapped AVCA ⊕ and ⊗ ---")
    monotonicity_conjuncts: List[FNode] = []
    for x1 in SMT_S_ORD_ELEMENTS:
        for y1 in SMT_S_ORD_ELEMENTS:
            premise = le(x1, y1)
            for a_mono in SMT_S_ORD_ELEMENTS:
                add_res_x1_a = mapped_avca_add_s_ord(x1, a_mono, current_omega)
                add_res_y1_a = mapped_avca_add_s_ord(y1, a_mono, current_omega)
                monotonicity_conjuncts.append(Implies(premise, le(add_res_x1_a, add_res_y1_a)))
                add_res_a_x1 = mapped_avca_add_s_ord(a_mono, x1, current_omega)
                add_res_a_y1 = mapped_avca_add_s_ord(a_mono, y1, current_omega)
                monotonicity_conjuncts.append(Implies(premise, le(add_res_a_x1, add_res_a_y1)))

                mul_res_x1_a = mapped_avca_mul_s_ord(x1, a_mono, current_omega)
                mul_res_y1_a = mapped_avca_mul_s_ord(y1, a_mono, current_omega)
                monotonicity_conjuncts.append(Implies(premise, le(mul_res_x1_a, mul_res_y1_a)))
                mul_res_a_x1 = mapped_avca_mul_s_ord(a_mono, x1, current_omega)
                mul_res_a_y1 = mapped_avca_mul_s_ord(a_mono, y1, current_omega)
                monotonicity_conjuncts.append(Implies(premise, le(mul_res_a_x1, mul_res_a_y1)))
    if monotonicity_conjuncts: # Only add if S_ord has elements
        base_assertions.append(And(monotonicity_conjuncts))

    print(f"\n--- Asserting at least {min_extra_edges} non-reflexive true 'le' relations ---")
    all_possible_non_reflexive_le_relations: List[FNode] = []
    if len(SMT_S_ORD_ELEMENTS) > 1:
        for x_count_smt in SMT_S_ORD_ELEMENTS:
            for y_count_smt in SMT_S_ORD_ELEMENTS:
                if x_count_smt.constant_value() != y_count_smt.constant_value():
                    all_possible_non_reflexive_le_relations.append(le(x_count_smt, y_count_smt))

    if not all_possible_non_reflexive_le_relations and min_extra_edges > 0:
        print(f"Warning: No non-reflexive pairs exist for S_ord size {len(SMT_S_ORD_ELEMENTS)} to count for min_extra_edges={min_extra_edges}.")
        base_assertions.append(FALSE()) 
    elif all_possible_non_reflexive_le_relations: # If there are pairs to count from
        terms_for_sum_edges = [Ite(cond, Int(1), Int(0)) for cond in all_possible_non_reflexive_le_relations]
        sum_of_true_relations = Plus(terms_for_sum_edges) if len(terms_for_sum_edges) > 1 else (terms_for_sum_edges[0] if terms_for_sum_edges else Int(0))
        base_assertions.append(GE(sum_of_true_relations, Int(min_extra_edges)))
    elif min_extra_edges > 0 : # No relations (e.g. S_ord size 1), but min_extra_edges > 0
         base_assertions.append(FALSE())
    # If min_extra_edges is 0, and no non-reflexive pairs, this is fine.

    print(f"\n--- Solving with SMT (Z3) to find common monotonic POs (Ω={current_omega}, min_extra_edges={min_extra_edges}) ---")
    
    found_models_count = 0
    all_found_po_tuples: List[List[Tuple[int,int]]] = []

    with Solver(name="z3", logic="QF_UFLIA") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        
        while found_models_count < max_models_to_find and s.solve():
            found_models_count += 1
            print(f"\n--- Model {found_models_count} (Ω={current_omega}, min_extra_edges={min_extra_edges}) ---")
            model = s.get_model()
            print("  Candidate PO True Relations (x_val <= y_val):")
            
            current_model_true_relations_tuples: List[Tuple[int,int]] = []
            output_lines: List[str] = []
            num_extra_edges_in_model = 0

            for x_model_smt_outer in SMT_S_ORD_ELEMENTS:
                x_model_py_outer = x_model_smt_outer.constant_value()
                for y_model_smt_outer in SMT_S_ORD_ELEMENTS:
                    y_model_py_outer = y_model_smt_outer.constant_value()
                    if model.get_value(le(x_model_smt_outer, y_model_smt_outer)) == TRUE():
                        output_lines.append(f"  {S_ORD_ELEMENT_MAP[x_model_py_outer]:<7} <= {S_ORD_ELEMENT_MAP[y_model_py_outer]:<7}")
                        current_model_true_relations_tuples.append((x_model_py_outer, y_model_py_outer))
                        if x_model_py_outer != y_model_py_outer:
                            num_extra_edges_in_model +=1
            
            for line in sorted(list(set(output_lines))): print(line)
            print(f"  Number of non-reflexive true relations in this model: {num_extra_edges_in_model}")
            
            # Sort for canonical representation before adding to all_found_po_tuples
            sorted_current_model_rels = sorted(list(set(current_model_true_relations_tuples)))
            if sorted_current_model_rels not in all_found_po_tuples :
                all_found_po_tuples.append(sorted_current_model_rels)
                print(f"  PO Relations for B2 script: candidate_po_true_relations = {sorted_current_model_rels}")
            else: # Found a duplicate model, SMT solver might not be exploring fully distinct interpretations of 'le'
                print("  (Found a PO model identical to a previous one, stopping iteration for this min_extra_edges to avoid loops with non-ideal blocking)")
                #This simple blocking clause below might not be sufficient for function 'le' if the solver provides equivalent functions.
                #A more robust blocking would involve blocking the entire model of 'le'.
                break


            blocking_clause_terms = []
            for x_block_smt in SMT_S_ORD_ELEMENTS:
                for y_block_smt in SMT_S_ORD_ELEMENTS:
                    val = model.get_value(le(x_block_smt, y_block_smt))
                    # Create a term that is true if this 'le' interpretation is NOT the current model
                    if val == TRUE():
                        blocking_clause_terms.append(Not(le(x_block_smt, y_block_smt)))
                    else:
                        blocking_clause_terms.append(le(x_block_smt, y_block_smt))
            if blocking_clause_terms:
                 s.add_assertion(Or(blocking_clause_terms))
            else: break 
        
        if found_models_count == 0:
            print(f"\nSMT Result for B1 (Ω={current_omega}, min_extra_edges={min_extra_edges}): UNSAT")
            print(f"  INTERPRETATION: UNSAT means NO common monotonic PO could be found.")
        else:
            print(f"\nFound {len(all_found_po_tuples)} distinct common monotonic PO(s) for Ω={current_omega}, min_extra_edges={min_extra_edges}.")

    print(f"\n====== Find_All_SL_Common_Monotonic_POs_OmegaN (Ω={current_omega}, min_extra_edges={min_extra_edges}) Finished ======")
    return all_found_po_tuples


if __name__ == "__main__":
    print("Running Task E-1: Searching for common monotonic POs on S_ord for Ω=4 and Ω=5.")
    print("This uses the full aspect-aware mapped AVCA operations.")
    
    for omega_to_test in [4, 5]:
        initialize_omega_dependent_globals(omega_to_test) # Re-init globals for each Omega

        print(f"\n--- Testing for Ω = {omega_to_test} ---")
        # Max non-reflexive edges for N elements is N*(N-1). S_ord size is omega+1.
        # For Omega=4, S_ord size=5. Max edges = 5*4 = 20.
        # For Omega=5, S_ord size=6. Max edges = 6*5 = 30.
        
        # We are primarily interested if *any* non-trivial ones exist with few edges first.
        # The previous UNSAT for Omega=3 at min_extra_edges=2 was key.
        
        print(f"\nSearching for POs with at least 0 non-reflexive edges (Ω={omega_to_test}):")
        found_pos_0_edges = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=0, max_models_to_find=1000000000)
        print("\n" + "-"*60 + "\n")

        print(f"Searching for POs with at least 1 non-reflexive edge (Ω={omega_to_test}):")
        found_pos_1_edge = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=1, max_models_to_find=1000000000)
        print("\n" + "-"*60 + "\n")

        print(f"Searching for POs with at least 2 non-reflexive edges (Ω={omega_to_test}):")
        found_pos_2_edges = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=2, max_models_to_find=1000000000)
    

        print(f"Searching for POs with at least 3 non-reflexive edge (Ω={omega_to_test}):")
        found_pos_3_edge = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=3, max_models_to_find=1000000000)


        print(f"Searching for POs with at least 4 non-reflexive edges (Ω={omega_to_test}):")
        found_pos_4_edges = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=4, max_models_to_find=1000000000)

        print(f"\nSearching for POs with at least 5 non-reflexive edges (Ω={omega_to_test}):")
        found_pos_5_edges = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=5, max_models_to_find=1000000000)


        print(f"Searching for POs with at least 6 non-reflexive edge (Ω={omega_to_test}):")
        found_pos_6_edge = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=6, max_models_to_find=1000000000)


        print(f"Searching for POs with at least 7 non-reflexive edges (Ω={omega_to_test}):")
        found_pos_7_edges = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=7, max_models_to_find=1000000000)

        print(f"\nSearching for POs with at least 8 non-reflexive edges (Ω={omega_to_test}):")
        found_pos_8_edges = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=8, max_models_to_find=1000000000)


        print(f"Searching for POs with at least 9 non-reflexive edge (Ω={omega_to_test}):")
        found_pos_9_edge = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=9, max_models_to_find=1000000000)


        print(f"Searching for POs with at least 10 non-reflexive edges (Ω={omega_to_test}):")
        found_pos_10_edges = run_B1_find_all_common_monotonic_pos_omegaN(current_omega=omega_to_test, min_extra_edges=10, max_models_to_find=1000000000)
                                
        if omega_to_test != 5:
            print("\n" + "="*70 + "\n")