# Find_Dual_Monotonic_POs_OmegaN_v3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, Function, GE, LT, LE) # Added LE
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable, Literal, Union, Set

# --- Global Mappings (will be initialized by current_omega) ---
SMT_S_ORD_ELEMENTS: List[FNode] = []
S_ORD_ELEMENT_MAP: Dict[int, str] = {} 
S_ORD_PY_KEYS: List[int] = []
AVCA_U_ALG_SMT: FNode = Int(0) 
AVCA_DFI_ALG_SMT_MAP: Dict[int, FNode] = {} 

# --- Semantic Aspect Definitions (Global) ---
SEM_ZERO_ASPECT = Int(0) 
SEM_AREO_ASPECT = Int(1) 
SEM_DFI_ASPECT  = Int(2) 

# --- Helper to initialize globals based on Omega ---
def initialize_omega_dependent_globals(current_omega: int):
    global SMT_S_ORD_ELEMENTS, S_ORD_ELEMENT_MAP, S_ORD_PY_KEYS
    global AVCA_U_ALG_SMT, AVCA_DFI_ALG_SMT_MAP

    if current_omega < 1:
        raise ValueError("current_omega must be >= 1")

    SMT_S_ORD_ELEMENTS.clear(); S_ORD_ELEMENT_MAP.clear(); 
    temp_s_ord_py_keys = []

    for i in range(current_omega - 1): 
        dfi_sem_val = i
        SMT_S_ORD_ELEMENTS.append(Int(dfi_sem_val))
        S_ORD_ELEMENT_MAP[dfi_sem_val] = f"DFIs{i+1}"
        temp_s_ord_py_keys.append(dfi_sem_val)
    
    zu_s_val = current_omega - 1 
    au_s_val = current_omega     
    SMT_S_ORD_ELEMENTS.append(Int(zu_s_val)); S_ORD_ELEMENT_MAP[zu_s_val] = "ZUs"; temp_s_ord_py_keys.append(zu_s_val)
    SMT_S_ORD_ELEMENTS.append(Int(au_s_val)); S_ORD_ELEMENT_MAP[au_s_val] = "AUs"; temp_s_ord_py_keys.append(au_s_val)
    S_ORD_PY_KEYS[:] = sorted(temp_s_ord_py_keys)

    AVCA_U_ALG_SMT = Int(0) 
    AVCA_DFI_ALG_SMT_MAP.clear()
    if current_omega > 1:
        for i in range(1, current_omega): 
            AVCA_DFI_ALG_SMT_MAP[i] = Int(i) 

# --- Quotient Map π and its Inverse π_inv (Omega-Parametric) ---
def pi_algebraic(s_ord_element_smt: FNode, current_omega: int) -> FNode:
    current_result = AVCA_U_ALG_SMT 
    if current_omega > 1:
        for i in range(current_omega - 2, -1, -1): 
            dfi_sem_val = i
            dfi_alg_val = i + 1 
            if dfi_alg_val in AVCA_DFI_ALG_SMT_MAP:
                 current_result = Ite(Equals(s_ord_element_smt, Int(dfi_sem_val)), 
                                      AVCA_DFI_ALG_SMT_MAP[dfi_alg_val], current_result)
    return current_result

def pi_aspect_inherent(s_ord_element_smt: FNode, current_omega: int) -> FNode:
    zu_s_val = current_omega - 1; au_s_val = current_omega
    return Ite(Equals(s_ord_element_smt, Int(zu_s_val)), SEM_ZERO_ASPECT,
           Ite(Equals(s_ord_element_smt, Int(au_s_val)), SEM_AREO_ASPECT, SEM_DFI_ASPECT))

def pi_inv_s_ord(avca_algebraic_result: FNode, avca_semantic_aspect: FNode, current_omega: int) -> FNode:
    is_alg_U = Equals(avca_algebraic_result, AVCA_U_ALG_SMT)
    zu_s_val = current_omega - 1; au_s_val = current_omega
    s_ord_dfi_fallback = Int(au_s_val) 
    current_dfi_map_result = s_ord_dfi_fallback
    if current_omega > 1:
        for i in range(current_omega - 1, 0, -1): 
            dfi_alg_val = i; dfi_sem_val = i - 1 
            if dfi_alg_val in AVCA_DFI_ALG_SMT_MAP:
                current_dfi_map_result = Ite(Equals(avca_algebraic_result, AVCA_DFI_ALG_SMT_MAP[dfi_alg_val]),
                                             Int(dfi_sem_val), current_dfi_map_result)
    return Ite(is_alg_U,
               Ite(Equals(avca_semantic_aspect, SEM_ZERO_ASPECT), Int(zu_s_val), Int(au_s_val)), 
               current_dfi_map_result)

# --- AVCA Operations (Algebraic & Aspect Determination Logic - Omega Parametric) ---
def avca_add_bc_omegaN_algebraic(a: FNode, b: FNode, current_omega: int) -> FNode:
    is_a_U=Equals(a,AVCA_U_ALG_SMT); is_b_U=Equals(b,AVCA_U_ALG_SMT)
    s=Plus(a,b); return Ite(is_a_U,b,Ite(is_b_U,a,Ite(LT(s,Int(current_omega)),s,AVCA_U_ALG_SMT)))

def avca_mul_bc_omegaN_algebraic(a: FNode, b: FNode, current_omega: int) -> FNode:
    is_a_U=Equals(a,AVCA_U_ALG_SMT); is_b_U=Equals(b,AVCA_U_ALG_SMT)
    dfi_prod_result=AVCA_U_ALG_SMT 
    if current_omega > 1:
        prod_val=Times(a,b)
        is_classical_prod=And(GE(prod_val,Int(1)),LT(prod_val,Int(current_omega)))
        dfi_prod_result=Ite(is_classical_prod,prod_val,AVCA_U_ALG_SMT)
    return Ite(Or(is_a_U,is_b_U),AVCA_U_ALG_SMT,dfi_prod_result)

def determine_avca_effective_aspects(op_char: Literal["add", "mul"], 
                                     s_ord_in1: FNode, s_ord_in2: FNode, 
                                     current_omega: int) -> Tuple[FNode, FNode]:
    pi_s1_alg=pi_algebraic(s_ord_in1,current_omega); pi_s2_alg=pi_algebraic(s_ord_in2,current_omega)
    asp_s1_inh=pi_aspect_inherent(s_ord_in1,current_omega); asp_s2_inh=pi_aspect_inherent(s_ord_in2,current_omega)
    eff_s1=Ite(Equals(asp_s1_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s1_inh)
    eff_s2=Ite(Equals(asp_s2_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s2_inh)
    is_pi_s1_dfi=Not(Equals(pi_s1_alg,AVCA_U_ALG_SMT));is_pi_s2_dfi=Not(Equals(pi_s2_alg,AVCA_U_ALG_SMT))
    is_dfi_dfi_interaction=And(is_pi_s1_dfi,is_pi_s2_dfi)
    dfi_dfi_op_causes_saturation=FALSE()
    if op_char=="add": dfi_dfi_op_causes_saturation=GE(Plus(pi_s1_alg,pi_s2_alg),Int(current_omega))
    elif op_char=="mul": dfi_dfi_op_causes_saturation=GE(Times(pi_s1_alg,pi_s2_alg),Int(current_omega))
    eff_s1=Ite(And(is_dfi_dfi_interaction,dfi_dfi_op_causes_saturation),SEM_AREO_ASPECT,eff_s1)
    eff_s2=Ite(And(is_dfi_dfi_interaction,dfi_dfi_op_causes_saturation),SEM_AREO_ASPECT,eff_s2)
    return eff_s1,eff_s2

def get_avca_result_aspect(alg_res_avca: FNode, eff_asp_a_avca: FNode, eff_asp_b_avca: FNode) -> FNode:
    is_res_U=Equals(alg_res_avca,AVCA_U_ALG_SMT)
    res_areo_if_U=Or(Equals(eff_asp_a_avca,SEM_AREO_ASPECT),Equals(eff_asp_b_avca,SEM_AREO_ASPECT))
    return Ite(is_res_U,Ite(res_areo_if_U,SEM_AREO_ASPECT,SEM_ZERO_ASPECT),SEM_DFI_ASPECT)

def mapped_avca_add_s_ord(s_ord_a: FNode, s_ord_b: FNode, current_omega: int) -> FNode:
    pi_a_alg=pi_algebraic(s_ord_a,current_omega); pi_b_alg=pi_algebraic(s_ord_b,current_omega)
    avca_alg_res=avca_add_bc_omegaN_algebraic(pi_a_alg,pi_b_alg,current_omega)
    eff_asp_a,eff_asp_b=determine_avca_effective_aspects("add",s_ord_a,s_ord_b,current_omega)
    avca_sem_asp=get_avca_result_aspect(avca_alg_res,eff_asp_a,eff_asp_b)
    return pi_inv_s_ord(avca_alg_res,avca_sem_asp,current_omega)

def mapped_avca_mul_s_ord(s_ord_a: FNode, s_ord_b: FNode, current_omega: int) -> FNode:
    pi_a_alg=pi_algebraic(s_ord_a,current_omega); pi_b_alg=pi_algebraic(s_ord_b,current_omega)
    avca_alg_res=avca_mul_bc_omegaN_algebraic(pi_a_alg,pi_b_alg,current_omega)
    eff_asp_a,eff_asp_b=determine_avca_effective_aspects("mul",s_ord_a,s_ord_b,current_omega)
    avca_sem_asp=get_avca_result_aspect(avca_alg_res,eff_asp_a,eff_asp_b)
    return pi_inv_s_ord(avca_alg_res,avca_sem_asp,current_omega)

def assert_po_axioms(assertions_list: List[FNode], le_func: FNode, s_ord_elements_for_po: List[FNode]):
    for x_refl in s_ord_elements_for_po: assertions_list.append(le_func(x_refl, x_refl))
    for x_anti in s_ord_elements_for_po:
        for y_anti in s_ord_elements_for_po:
            if not (x_anti.is_constant() and y_anti.is_constant() and x_anti.constant_value() == y_anti.constant_value()):
                assertions_list.append(Implies(And(le_func(x_anti,y_anti), le_func(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in s_ord_elements_for_po:
        for y_trans in s_ord_elements_for_po:
            for z_trans in s_ord_elements_for_po:
                assertions_list.append(Implies(And(le_func(x_trans,y_trans), le_func(y_trans,z_trans)), le_func(x_trans,z_trans)))

def assert_monotonicity_for_op(assertions_list: List[FNode], le_func: FNode, 
                               mapped_op_s_ord_callable: Callable[[FNode, FNode, int], FNode], 
                               current_omega: int, s_ord_elements_for_mono: List[FNode]):
    mono_conjuncts: List[FNode] = []
    for x1 in s_ord_elements_for_mono:
        for y1 in s_ord_elements_for_mono:
            premise = le_func(x1, y1)
            for a_mono in s_ord_elements_for_mono:
                res_x1_a = mapped_op_s_ord_callable(x1, a_mono, current_omega) 
                res_y1_a = mapped_op_s_ord_callable(y1, a_mono, current_omega)
                mono_conjuncts.append(Implies(premise, le_func(res_x1_a, res_y1_a)))
                res_a_x1 = mapped_op_s_ord_callable(a_mono, x1, current_omega)
                res_a_y1 = mapped_op_s_ord_callable(a_mono, y1, current_omega)
                mono_conjuncts.append(Implies(premise, le_func(res_a_x1, res_a_y1)))
    if mono_conjuncts: assertions_list.append(And(mono_conjuncts))

def assert_min_extra_edges(assertions_list: List[FNode], le_func: FNode, min_edges: int, s_ord_elements_for_edges: List[FNode]):
    all_possible_non_reflexive_le_relations: List[FNode] = []
    if len(s_ord_elements_for_edges) > 1:
        for x_smt_edge in s_ord_elements_for_edges:
            for y_smt_edge in s_ord_elements_for_edges:
                if x_smt_edge.constant_value() != y_smt_edge.constant_value():
                    all_possible_non_reflexive_le_relations.append(le_func(x_smt_edge, y_smt_edge))
    if not all_possible_non_reflexive_le_relations and min_edges > 0:
        assertions_list.append(FALSE())
    elif all_possible_non_reflexive_le_relations : 
        terms = [Ite(cond, Int(1), Int(0)) for cond in all_possible_non_reflexive_le_relations]
        sum_true = Plus(terms) if len(terms)>1 else (terms[0] if terms else Int(0))
        assertions_list.append(GE(sum_true, Int(min_edges)))
    elif min_edges > 0: assertions_list.append(FALSE())

def print_po_model(model: Solver, le_func: FNode, po_name: str, current_omega: int):
    print(f"  {po_name} True Relations (x_val <= y_val) for Ω={current_omega}:")
    output_lines: List[str] = []
    relations_tuples: List[Tuple[int,int]] = []
    num_extra = 0
    # Use globally initialized SMT_S_ORD_ELEMENTS and S_ORD_ELEMENT_MAP for printing
    for x_smt in SMT_S_ORD_ELEMENTS: 
        x_py = x_smt.constant_value()
        for y_smt in SMT_S_ORD_ELEMENTS: 
            y_py = y_smt.constant_value()
            le_val_model = model.get_value(le_func(x_smt, y_smt)) # Evaluate the SMT function
            if le_val_model == TRUE():
                output_lines.append(f"  {S_ORD_ELEMENT_MAP[x_py]:<7} <= {S_ORD_ELEMENT_MAP[y_py]:<7}")
                relations_tuples.append((x_py, y_py))
                if x_py != y_py: num_extra +=1
    for line in sorted(list(set(output_lines))): print(line)
    print(f"  Number of non-reflexive true relations in this {po_name} model: {num_extra}")

def run_T1_find_dual_monotonic_pos(current_omega: int, min_extra_edges_add: int, min_extra_edges_mul: int, max_models_to_find: int = 1000000000):
    initialize_omega_dependent_globals(current_omega) 

    # For this script, ensure mapped ops use the correct current_omega from the parameter
    # The lambda functions will capture the current_omega from this scope.
    
    print(f"\n====== SCRIPT: Find_Dual_Monotonic_POs_OmegaN_v3 (Ω={current_omega}, min_edges_⊕={min_extra_edges_add}, min_edges_⊗={min_extra_edges_mul}) ======")
    # (Rest of the print statements are fine)
    print(f"Purpose: Find pairs of POs (le_add, le_mul) on S_ord (size {len(SMT_S_ORD_ELEMENTS)}) such that")
    print(f"         mapped AVCA ⊕ is monotone w.r.t. le_add (with ≥{min_extra_edges_add} extra edges), AND")
    print(f"         mapped AVCA ⊗ is monotone w.r.t. le_mul (with ≥{min_extra_edges_mul} extra edges).")
    print(f"         (Up to {max_models_to_find} model pairs).")


    le_add_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le_add = Symbol(f"le_add_O{current_omega}", le_add_func_type) 
    le_mul_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le_mul = Symbol(f"le_mul_O{current_omega}", le_mul_func_type) 

    base_assertions = []
    
    print("--- Asserting PO Axioms for 'le_add' and 'le_mul' ---")
    assert_po_axioms(base_assertions, le_add, SMT_S_ORD_ELEMENTS)
    assert_po_axioms(base_assertions, le_mul, SMT_S_ORD_ELEMENTS)

    print("\n--- Asserting Monotonicity for mapped AVCA ⊕ w.r.t. 'le_add' ---")
    assert_monotonicity_for_op(base_assertions, le_add, mapped_avca_add_s_ord, current_omega, SMT_S_ORD_ELEMENTS)
    
    print("\n--- Asserting Monotonicity for mapped AVCA ⊗ w.r.t. 'le_mul' ---")
    assert_monotonicity_for_op(base_assertions, le_mul, mapped_avca_mul_s_ord, current_omega, SMT_S_ORD_ELEMENTS)


    # --- START OF TWEAK 1 IMPLEMENTATION ---
    print(f"\n--- Asserting min_extra_edges for 'le_add' ({min_extra_edges_add}) AND non-reflexive edges in le_add <= 1 (Auditor's Tweak) ---")
    # Original min_extra_edges constraint for le_add
    assert_min_extra_edges(base_assertions, le_add, min_extra_edges_add, SMT_S_ORD_ELEMENTS)
    
    # New constraint: sum of non-reflexive true relations for le_add <= 1
    all_possible_non_reflex_le_add_relations: List[FNode] = []
    if len(SMT_S_ORD_ELEMENTS) > 1:
        for x_smt_edge_lc in SMT_S_ORD_ELEMENTS:
            for y_smt_edge_lc in SMT_S_ORD_ELEMENTS:
                if x_smt_edge_lc.constant_value() != y_smt_edge_lc.constant_value():
                    all_possible_non_reflex_le_add_relations.append(le_add(x_smt_edge_lc, y_smt_edge_lc))
    
    if all_possible_non_reflex_le_add_relations: # If there are pairs to count from
        terms_for_sum_edges_add = [Ite(cond, Int(1), Int(0)) for cond in all_possible_non_reflex_le_add_relations]
        sum_of_true_relations_add = Plus(terms_for_sum_edges_add) if len(terms_for_sum_edges_add) > 1 else \
                                   (terms_for_sum_edges_add[0] if terms_for_sum_edges_add else Int(0))
        base_assertions.append(LE(sum_of_true_relations_add, Int(1))) # Auditor's short-circuit constraint
    elif 0 > 1 : # Only if S_ORD_ELEMENTS was < 2, and trying to assert sum <= 1 (which is fine)
        pass # No non-reflexive edges, so sum is 0, which is <= 1. No specific assertion needed if list empty.
    # If min_extra_edges_add was > 1, the GE assertion from assert_min_extra_edges
    # and this LE assertion for <=1 would create a contradiction, as intended if we
    # try to force le_add to be rich while also applying this new knowledge.
    # --- END OF TWEAK 1 IMPLEMENTATION ---

    print(f"\n--- Asserting min_extra_edges for 'le_add' ({min_extra_edges_add}) and 'le_mul' ({min_extra_edges_mul}) ---")
    assert_min_extra_edges(base_assertions, le_add, min_extra_edges_add, SMT_S_ORD_ELEMENTS)
    assert_min_extra_edges(base_assertions, le_mul, min_extra_edges_mul, SMT_S_ORD_ELEMENTS)
    
    found_models_count = 0
    found_model_signatures: Set[Tuple[frozenset, frozenset]] = set()

    print(f"\n--- Solving with SMT (Z3) to find dual monotonic POs ---")
    with Solver(name="z3", logic="QF_UFLIA") as s:
        for an_assertion in base_assertions:
            s.add_assertion(an_assertion)
        
        while len(found_model_signatures) < max_models_to_find and s.solve():
            model = s.get_model()
            
            current_le_add_tuples: List[Tuple[int,int]] = []
            for x_smt_m1 in SMT_S_ORD_ELEMENTS:
                for y_smt_m1 in SMT_S_ORD_ELEMENTS:
                    if model.get_value(le_add(x_smt_m1, y_smt_m1)) == TRUE():
                        current_le_add_tuples.append((x_smt_m1.constant_value(), y_smt_m1.constant_value()))
            
            current_le_mul_tuples: List[Tuple[int,int]] = []
            for x_smt_m2 in SMT_S_ORD_ELEMENTS:
                for y_smt_m2 in SMT_S_ORD_ELEMENTS:
                    if model.get_value(le_mul(x_smt_m2, y_smt_m2)) == TRUE():
                        current_le_mul_tuples.append((x_smt_m2.constant_value(), y_smt_m2.constant_value()))
            
            le_add_sig = frozenset(current_le_add_tuples)
            le_mul_sig = frozenset(current_le_mul_tuples)

            if (le_add_sig, le_mul_sig) not in found_model_signatures:
                found_model_signatures.add((le_add_sig, le_mul_sig))
                found_models_count +=1 
                print(f"\n--- Model Pair {found_models_count} (Ω={current_omega}, min_edges_⊕={min_extra_edges_add}, min_edges_⊗={min_extra_edges_mul}) ---")
                print_po_model(model, le_add, "le_add (for ⊕)", current_omega)
                print_po_model(model, le_mul, "le_mul (for ⊗)", current_omega)
            else: 
                print("  (Found a PO pair model identical to a previous one, simple blocking might not be enough for function interpretations)")
                break 

            # Corrected Blocking Clause Logic
            blocking_clause_terms_for_this_model_pair = []
            for x_b_add in SMT_S_ORD_ELEMENTS: # Iterate for le_add
                for y_b_add in SMT_S_ORD_ELEMENTS:
                    val_add_model = model.get_value(le_add(x_b_add, y_b_add))
                    if val_add_model == TRUE():
                        blocking_clause_terms_for_this_model_pair.append(Not(le_add(x_b_add, y_b_add)))
                    else: # val_add_model == FALSE()
                        blocking_clause_terms_for_this_model_pair.append(le_add(x_b_add, y_b_add))
            
            for x_b_mul in SMT_S_ORD_ELEMENTS: # Iterate for le_mul
                for y_b_mul in SMT_S_ORD_ELEMENTS:
                    val_mul_model = model.get_value(le_mul(x_b_mul, y_b_mul))
                    if val_mul_model == TRUE():
                        blocking_clause_terms_for_this_model_pair.append(Not(le_mul(x_b_mul, y_b_mul)))
                    else: # val_mul_model == FALSE()
                        blocking_clause_terms_for_this_model_pair.append(le_mul(x_b_mul, y_b_mul))
            
            if blocking_clause_terms_for_this_model_pair:
                s.add_assertion(Or(blocking_clause_terms_for_this_model_pair))
            else: break
        
        if not found_model_signatures: 
            print(f"\nSMT Result for T1 (Ω={current_omega}, min_edges_⊕={min_extra_edges_add}, min_edges_⊗={min_extra_edges_mul}): UNSAT")
            print(f"  INTERPRETATION: UNSAT means NO pair of POs (le_add, le_mul) could be found.")
        else:
            print(f"\nFound {len(found_model_signatures)} distinct pairs of monotonic PO(s).")

    print(f"\n====== Find_Dual_Monotonic_POs_OmegaN_v3 (Ω={current_omega}) Finished ======")
    return list(found_model_signatures)


if __name__ == "__main__":
    current_omega_test_t1 = 3 
    
    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=0, min_extra_edges_mul=0 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=0, 
                                   min_extra_edges_mul=0, 
                                   max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=1, min_extra_edges_mul=1 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=1, 
                                   min_extra_edges_mul=1, 
                                   max_models_to_find=1000000000)
    

    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=2, min_extra_edges_mul=0 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=2, 
                                   min_extra_edges_mul=2, 
                                   max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=3, min_extra_edges_mul=1 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=3, 
                                   min_extra_edges_mul=3, 
                                   max_models_to_find=1000000000)
    

    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=4, min_extra_edges_mul=0 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=4, 
                                   min_extra_edges_mul=4, 
                                   max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=5, min_extra_edges_mul=1 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=5, 
                                   min_extra_edges_mul=5, 
                                   max_models_to_find=1000000000)
    

    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=6, min_extra_edges_mul=0 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=6, 
                                   min_extra_edges_mul=6, 
                                   max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=7, min_extra_edges_mul=1 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=7, 
                                   min_extra_edges_mul=7, 
                                   max_models_to_find=1000000000)
    
    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=8, min_extra_edges_mul=0 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=8, 
                                   min_extra_edges_mul=8, 
                                   max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")

    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=9, min_extra_edges_mul=1 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=9, 
                                   min_extra_edges_mul=9, 
                                   max_models_to_find=1000000000)
    print("\n" + "="*70 + "\n")
    
    print(f"\n--- Running T1: Testing for Ω = {current_omega_test_t1}, min_extra_edges_add=10, min_extra_edges_mul=1 ---")
    run_T1_find_dual_monotonic_pos(current_omega=current_omega_test_t1, 
                                   min_extra_edges_add=10, 
                                   min_extra_edges_mul=10, 
                                   max_models_to_find=1000000000)
