# Find_Dual_Monotonic_POs_OmegaN_v4_Tweaked.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, Function, GE, LT, LE) # Corrected: Added LE
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable, Literal, Union, Set

# --- Global Mappings & Semantic Aspect Definitions (Identical to your v3 script) ---
SMT_S_ORD_ELEMENTS: List[FNode] = []
S_ORD_ELEMENT_MAP: Dict[int, str] = {} 
S_ORD_PY_KEYS: List[int] = []
AVCA_U_ALG_SMT: FNode = Int(0) 
AVCA_DFI_ALG_SMT_MAP: Dict[int, FNode] = {} 
SEM_ZERO_ASPECT = Int(0); SEM_AREO_ASPECT = Int(1); SEM_DFI_ASPECT  = Int(2)

# --- Helper to initialize globals based on Omega ---
def initialize_omega_dependent_globals(current_omega: int):
    global SMT_S_ORD_ELEMENTS, S_ORD_ELEMENT_MAP, S_ORD_PY_KEYS, AVCA_U_ALG_SMT, AVCA_DFI_ALG_SMT_MAP
    if current_omega < 1: raise ValueError("current_omega must be >= 1")
    SMT_S_ORD_ELEMENTS.clear(); S_ORD_ELEMENT_MAP.clear(); temp_s_ord_py_keys = []
    for i in range(current_omega - 1): 
        dfi_sem_val = i; SMT_S_ORD_ELEMENTS.append(Int(dfi_sem_val))
        S_ORD_ELEMENT_MAP[dfi_sem_val] = f"DFIs{i+1}"; temp_s_ord_py_keys.append(dfi_sem_val)
    zu_s_val=current_omega-1; au_s_val=current_omega
    SMT_S_ORD_ELEMENTS.append(Int(zu_s_val)); S_ORD_ELEMENT_MAP[zu_s_val]="ZUs"; temp_s_ord_py_keys.append(zu_s_val)
    SMT_S_ORD_ELEMENTS.append(Int(au_s_val)); S_ORD_ELEMENT_MAP[au_s_val]="AUs"; temp_s_ord_py_keys.append(au_s_val)
    S_ORD_PY_KEYS[:] = sorted(temp_s_ord_py_keys)
    AVCA_U_ALG_SMT=Int(0); AVCA_DFI_ALG_SMT_MAP.clear()
    if current_omega > 1:
        for i in range(1,current_omega): AVCA_DFI_ALG_SMT_MAP[i]=Int(i)

def pi_algebraic(s_ord_element_smt: FNode, current_omega: int) -> FNode:
    res=AVCA_U_ALG_SMT
    if current_omega>1:
        for i in range(current_omega-2,-1,-1):
            dfi_s_v=i; dfi_a_v=i+1
            if dfi_a_v in AVCA_DFI_ALG_SMT_MAP: res=Ite(Equals(s_ord_element_smt,Int(dfi_s_v)),AVCA_DFI_ALG_SMT_MAP[dfi_a_v],res)
            # else: if omega=1, this loop doesn't run, res stays U_ALG. If omega=2, DFIsem0 (val 0) -> DFIalg1 (val 1)
    return res
def pi_aspect_inherent(s_ord_element_smt:FNode,current_omega:int)->FNode:
    zu_s_v=current_omega-1;au_s_v=current_omega
    return Ite(Equals(s_ord_element_smt,Int(zu_s_v)),SEM_ZERO_ASPECT,Ite(Equals(s_ord_element_smt,Int(au_s_v)),SEM_AREO_ASPECT,SEM_DFI_ASPECT))
def pi_inv_s_ord(avca_alg_res:FNode,avca_sem_asp:FNode,current_omega:int)->FNode:
    is_U=Equals(avca_alg_res,AVCA_U_ALG_SMT)
    zu_s_v=current_omega-1;au_s_v=current_omega;s_ord_dfi_fb=Int(au_s_v) # Fallback to AUs
    cur_dfi_map_res=s_ord_dfi_fb
    if current_omega>1:
        for i in range(current_omega-1,0,-1): # DFIalg values from omega-1 down to 1
            dfi_a_v=i;dfi_s_v=i-1 # Corresponding DFIsem value (0 to omega-2)
            if dfi_a_v in AVCA_DFI_ALG_SMT_MAP:cur_dfi_map_res=Ite(Equals(avca_alg_res,AVCA_DFI_ALG_SMT_MAP[dfi_a_v]),Int(dfi_s_v),cur_dfi_map_res)
    return Ite(is_U,Ite(Equals(avca_sem_asp,SEM_ZERO_ASPECT),Int(zu_s_v),Int(au_s_v)),cur_dfi_map_res)
def avca_add_bc_omegaN_algebraic(a:FNode,b:FNode,omega:int)->FNode:
    is_a_U=Equals(a,AVCA_U_ALG_SMT);is_b_U=Equals(b,AVCA_U_ALG_SMT)
    s=Plus(a,b);return Ite(is_a_U,b,Ite(is_b_U,a,Ite(LT(s,Int(omega)),s,AVCA_U_ALG_SMT)))
def avca_mul_bc_omegaN_algebraic(a:FNode,b:FNode,omega:int)->FNode:
    is_a_U=Equals(a,AVCA_U_ALG_SMT);is_b_U=Equals(b,AVCA_U_ALG_SMT)
    dfi_prod_res=AVCA_U_ALG_SMT
    if omega>1: # Classical product only if DFIs exist
        # This check is only for DFI * DFI. If a or b is U, it's handled by outer ITE.
        # So, here a and b represent DFI algebraic values (1 to omega-1)
        prod_v=Times(a,b);is_classical=And(GE(prod_v,Int(1)),LT(prod_v,Int(omega)))
        dfi_prod_res=Ite(is_classical,prod_v,AVCA_U_ALG_SMT)
    return Ite(Or(is_a_U,is_b_U),AVCA_U_ALG_SMT,dfi_prod_res) # U annihilates
def determine_avca_effective_aspects(op_char,s_ord_in1,s_ord_in2,omega)->Tuple[FNode,FNode]:
    pi_s1_a=pi_algebraic(s_ord_in1,omega);pi_s2_a=pi_algebraic(s_ord_in2,omega)
    asp_s1_i=pi_aspect_inherent(s_ord_in1,omega);asp_s2_i=pi_aspect_inherent(s_ord_in2,omega)
    eff1=Ite(Equals(asp_s1_i,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s1_i)
    eff2=Ite(Equals(asp_s2_i,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s2_i)
    is_pi1_dfi=Not(Equals(pi_s1_a,AVCA_U_ALG_SMT));is_pi2_dfi=Not(Equals(pi_s2_a,AVCA_U_ALG_SMT))
    is_dfi_dfi=And(is_pi1_dfi,is_pi2_dfi)
    causes_sat_dfi_dfi=FALSE()
    if op_char=="add":causes_sat_dfi_dfi=GE(Plus(pi_s1_a,pi_s2_a),Int(omega))
    elif op_char=="mul":causes_sat_dfi_dfi=GE(Times(pi_s1_a,pi_s2_a),Int(omega)) # Only if both are DFI values
    eff1=Ite(And(is_dfi_dfi,causes_sat_dfi_dfi),SEM_AREO_ASPECT,eff1)
    eff2=Ite(And(is_dfi_dfi,causes_sat_dfi_dfi),SEM_AREO_ASPECT,eff2)
    return eff1,eff2
def get_avca_result_aspect(alg_res,eff_a,eff_b)->FNode:
    is_U=Equals(alg_res,AVCA_U_ALG_SMT)
    areo_if_U=Or(Equals(eff_a,SEM_AREO_ASPECT),Equals(eff_b,SEM_AREO_ASPECT))
    return Ite(is_U,Ite(areo_if_U,SEM_AREO_ASPECT,SEM_ZERO_ASPECT),SEM_DFI_ASPECT)
def mapped_avca_add_s_ord(s_a,s_b,omega)->FNode:
    pi_a_a=pi_algebraic(s_a,omega);pi_b_a=pi_algebraic(s_b,omega)
    avca_alg_r=avca_add_bc_omegaN_algebraic(pi_a_a,pi_b_a,omega)
    eff_a,eff_b=determine_avca_effective_aspects("add",s_a,s_b,omega)
    avca_sem_a=get_avca_result_aspect(avca_alg_r,eff_a,eff_b)
    return pi_inv_s_ord(avca_alg_r,avca_sem_a,omega)
def mapped_avca_mul_s_ord(s_a,s_b,omega)->FNode:
    pi_a_a=pi_algebraic(s_a,omega);pi_b_a=pi_algebraic(s_b,omega)
    avca_alg_r=avca_mul_bc_omegaN_algebraic(pi_a_a,pi_b_a,omega)
    eff_a,eff_b=determine_avca_effective_aspects("mul",s_a,s_b,omega)
    avca_sem_a=get_avca_result_aspect(avca_alg_r,eff_a,eff_b)
    return pi_inv_s_ord(avca_alg_r,avca_sem_a,omega)
def assert_po_axioms(assertions_list: List[FNode], le_func: FNode, s_ord_elements_for_po: List[FNode]):
    for x_refl in s_ord_elements_for_po: assertions_list.append(le_func(x_refl, x_refl))
    for x_anti in s_ord_elements_for_po:
        for y_anti in s_ord_elements_for_po:
            if not (x_anti.is_constant(SMT_INT_TYPE) and y_anti.is_constant(SMT_INT_TYPE) and x_anti.constant_value() == y_anti.constant_value()): # Check if FNodes are constants and equal
                assertions_list.append(Implies(And(le_func(x_anti,y_anti), le_func(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in s_ord_elements_for_po:
        for y_trans in s_ord_elements_for_po:
            for z_trans in s_ord_elements_for_po:
                assertions_list.append(Implies(And(le_func(x_trans,y_trans), le_func(y_trans,z_trans)), le_func(x_trans,z_trans)))

def assert_monotonicity_for_op(assertions_list: List[FNode], le_func: FNode, 
                               mapped_op_s_ord_callable: Callable[[FNode, FNode, int], FNode], 
                               current_omega: int, s_ord_elements_for_mono: List[FNode]):
    mono_conjuncts: List[FNode] = []
    if not s_ord_elements_for_mono: return # Skip if no elements (e.g. Omega=0 hypothetical)
    for x1 in s_ord_elements_for_mono:
        for y1 in s_ord_elements_for_mono:
            premise = le_func(x1, y1)
            for a_mono in s_ord_elements_for_mono:
                res_x1_a=mapped_op_s_ord_callable(x1,a_mono,current_omega); res_y1_a=mapped_op_s_ord_callable(y1,a_mono,current_omega)
                mono_conjuncts.append(Implies(premise, le_func(res_x1_a, res_y1_a)))
                res_a_x1=mapped_op_s_ord_callable(a_mono,x1,current_omega); res_a_y1=mapped_op_s_ord_callable(a_mono,y1,current_omega)
                mono_conjuncts.append(Implies(premise, le_func(res_a_x1, res_a_y1)))
    if mono_conjuncts: assertions_list.append(And(mono_conjuncts))

def assert_min_extra_edges(assertions_list: List[FNode], le_func: FNode, min_edges: int, s_ord_elements_for_edges: List[FNode]):
    all_possible_non_reflexive_le_relations: List[FNode] = []
    if len(s_ord_elements_for_edges) > 1:
        for x_smt_edge in s_ord_elements_for_edges:
            for y_smt_edge in s_ord_elements_for_edges:
                if not (x_smt_edge.is_constant(SMT_INT_TYPE) and y_smt_edge.is_constant(SMT_INT_TYPE) and x_smt_edge.constant_value() == y_smt_edge.constant_value()):
                    all_possible_non_reflexive_le_relations.append(le_func(x_smt_edge, y_smt_edge))
    
    if not all_possible_non_reflexive_le_relations and min_edges > 0:
        assertions_list.append(FALSE())
    elif all_possible_non_reflexive_le_relations : 
        terms = [Ite(cond, Int(1), Int(0)) for cond in all_possible_non_reflexive_le_relations]
        sum_true = Plus(terms) if len(terms)>1 else (terms[0] if terms else Int(0))
        assertions_list.append(GE(sum_true, Int(min_edges)))
    elif min_edges > 0: 
         assertions_list.append(FALSE())

def print_po_model(model: Solver, le_func: FNode, po_name: str, current_omega: int):
    print(f"  {po_name} True Relations (x_val <= y_val) for Ω={current_omega}:")
    output_lines: List[str] = []
    num_extra = 0
    # Use globally initialized SMT_S_ORD_ELEMENTS and S_ORD_ELEMENT_MAP for printing
    for x_smt in SMT_S_ORD_ELEMENTS: 
        x_py = x_smt.constant_value()
        for y_smt in SMT_S_ORD_ELEMENTS: 
            y_py = y_smt.constant_value()
            le_val_model = model.get_value(le_func(x_smt, y_smt))
            if le_val_model == TRUE():
                output_lines.append(f"  {S_ORD_ELEMENT_MAP[x_py]:<7} <= {S_ORD_ELEMENT_MAP[y_py]:<7}")
                if x_py != y_py: num_extra +=1
    for line in sorted(list(set(output_lines))): print(line)
    print(f"  Number of non-reflexive true relations in this {po_name} model: {num_extra}")

def run_T1_find_dual_monotonic_pos_tweaked(
    current_omega: int, 
    min_extra_edges_add_min: int,
    min_extra_edges_add_max: int, 
    min_extra_edges_mul: int, 
    max_models_to_find: int = 1000000000 
):
    initialize_omega_dependent_globals(current_omega) 

    script_version_name = "Find_Dual_Monotonic_POs_OmegaN_v4_TWEAKED"

    print(f"\n====== SCRIPT: {script_version_name} (Ω={current_omega}, {min_extra_edges_add_min}<=edges_⊕<={min_extra_edges_add_max}, edges_⊗≥{min_extra_edges_mul}) ======")
    print(f"Purpose: Find pairs of POs (le_add, le_mul) on S_ord (size {len(SMT_S_ORD_ELEMENTS)}) such that")
    print(f"         mapped AVCA ⊕ is monotone w.r.t. le_add (with {min_extra_edges_add_min} <= non-refl. edges <= {min_extra_edges_add_max}), AND") # Corrected to use parameter
    print(f"         mapped AVCA ⊗ is monotone w.r.t. le_mul (with ≥{min_extra_edges_mul} non-refl. edges).")
    print(f"         (Up to {max_models_to_find} model pairs).")

    le_add_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le_add = Symbol(f"le_add_O{current_omega}_t", le_add_func_type)  
    le_mul_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le_mul = Symbol(f"le_mul_O{current_omega}_t", le_mul_func_type) 

    base_assertions = []
    
    print("--- Asserting PO Axioms for 'le_add' and 'le_mul' ---")
    assert_po_axioms(base_assertions, le_add, SMT_S_ORD_ELEMENTS)
    assert_po_axioms(base_assertions, le_mul, SMT_S_ORD_ELEMENTS)

    print("\n--- Asserting Monotonicity for mapped AVCA ⊕ w.r.t. 'le_add' ---")
    assert_monotonicity_for_op(base_assertions, le_add, mapped_avca_add_s_ord, current_omega, SMT_S_ORD_ELEMENTS)
    
    print("\n--- Asserting Monotonicity for mapped AVCA ⊗ w.r.t. 'le_mul' ---")
    assert_monotonicity_for_op(base_assertions, le_mul, mapped_avca_mul_s_ord, current_omega, SMT_S_ORD_ELEMENTS)

    # --- AUDITOR'S TWEAK 1: Constrain non-reflexive edges for le_add ---
    print(f"\n--- Asserting {min_extra_edges_add_min} <= non-reflexive edges in le_add <= {min_extra_edges_add_max} (Auditor's Tweak) ---")
    all_possible_non_reflex_le_add_relations: List[FNode] = []
    if len(SMT_S_ORD_ELEMENTS) > 1:
        for x_smt_edge_lc in SMT_S_ORD_ELEMENTS:
            for y_smt_edge_lc in SMT_S_ORD_ELEMENTS:
                if not (x_smt_edge_lc.is_constant(SMT_INT_TYPE) and y_smt_edge_lc.is_constant(SMT_INT_TYPE) and x_smt_edge_lc.constant_value() == y_smt_edge_lc.constant_value()):
                    all_possible_non_reflex_le_add_relations.append(le_add(x_smt_edge_lc, y_smt_edge_lc))
    
    if all_possible_non_reflex_le_add_relations:
        terms_for_sum_edges_add = [Ite(cond, Int(1), Int(0)) for cond in all_possible_non_reflex_le_add_relations]
        sum_of_true_relations_add = Plus(terms_for_sum_edges_add) if len(terms_for_sum_edges_add) > 1 else \
                                   (terms_for_sum_edges_add[0] if terms_for_sum_edges_add else Int(0))
        base_assertions.append(GE(sum_of_true_relations_add, Int(min_extra_edges_add_min)))
        #base_assertions.append(LE(sum_of_true_relations_add, Int(min_extra_edges_add_max))) 
    elif min_extra_edges_add_min > 0 : 
         base_assertions.append(FALSE())
    # If min_extra_edges_add_min is 0, and no non-reflexive relations, sum is 0, GE(0,0) is true, LE(0,max) is true.

    print(f"\n--- Asserting min_extra_edges for 'le_mul' ({min_extra_edges_mul}) ---")
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
            le_add_sig = frozenset(current_le_add_tuples); le_mul_sig = frozenset(current_le_mul_tuples)

            if (le_add_sig, le_mul_sig) not in found_model_signatures:
                found_model_signatures.add((le_add_sig, le_mul_sig)); found_models_count +=1 
                print(f"\n--- Model Pair {found_models_count} (Ω={current_omega}) ---")
                print_po_model(model, le_add, f"le_add (⊕) ({min_extra_edges_add_min}≤edges≤{min_extra_edges_add_max})", current_omega)
                print_po_model(model, le_mul, f"le_mul (⊗) (≥{min_extra_edges_mul} edges)", current_omega)
            else: 
                print("  (Found a PO pair model identical to a previous one, stopping iteration.)"); break 
            
            blocking_clause_terms = []
            for x_b in SMT_S_ORD_ELEMENTS:
                for y_b in SMT_S_ORD_ELEMENTS:
                    val_add_m = model.get_value(le_add(x_b,y_b))
                    blocking_clause_terms.append(Iff(le_add(x_b,y_b), val_add_m)) 
                    val_mul_m = model.get_value(le_mul(x_b,y_b))
                    blocking_clause_terms.append(Iff(le_mul(x_b,y_b), val_mul_m))
            s.add_assertion(Not(And(blocking_clause_terms))) # Assert that the next model is NOT identical

        if not found_model_signatures: 
            print(f"\nSMT Result for T1_tweaked (Ω={current_omega}): UNSAT")
            print(f"  INTERPRETATION: UNSAT means NO pair of POs (le_add, le_mul) could be found.")
        else:
            print(f"\nFound {len(found_model_signatures)} distinct pairs of monotonic PO(s).")
    print(f"\n====== {script_version_name} (Ω={current_omega}) Finished ======")

if __name__ == "__main__":
    current_omega_test = 10
    initialize_omega_dependent_globals(current_omega_test) # Initialize once for this Omega

    print(f"\n--- Hardcore Test for Ω = {current_omega_test} ---")
    print(f"    Attempting to find le_add with AT LEAST 2 non-reflexive edges.")
    print(f"    (max_edges_add cap is high, e.g., {len(SMT_S_ORD_ELEMENTS) * (len(SMT_S_ORD_ELEMENTS)-1)})")
    print(f"    le_mul constrained to have at least 0 non-reflexive edges.")

    max_possible_non_reflex_edges = len(SMT_S_ORD_ELEMENTS) * (len(SMT_S_ORD_ELEMENTS) - 1)

    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test, 
        min_extra_edges_add_min=2,  # FORCE at least 2 non-reflexive edges for le_add
        min_extra_edges_add_max=max_possible_non_reflex_edges, # Allow le_add to be as rich as possible
        min_extra_edges_mul=0,      # Keep le_mul flexible
        max_models_to_find=5        # We only need one model if SAT, or UNSAT
    )
    print("\n" + "="*70 + "\n")
"""
    print(f"\n--- Test Case: le_add (exactly 1 edge), le_mul (≥1 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=1, 
        min_extra_edges_add_max=1, 
        min_extra_edges_mul=1, 
        max_models_to_find=1000000000
    )

 
    print(f"\n--- Test Case: le_add (exactly 1 edge), le_mul (≥0 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=1, 
        min_extra_edges_add_max=1, 
        min_extra_edges_mul=0, 
        max_models_to_find=1000000000 # Look for more models
    )
    print("\n" + "="*70 + "\n")

    print(f"\n--- Test Case: le_add (0-1 edges), le_mul (≥1 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=0, 
        min_extra_edges_add_max=1, 
        min_extra_edges_mul=1, 
        max_models_to_find=1000000000 # Look for more models
    
  
    )

    print("\n" + "="*70 + "\n")

    print(f"\n--- Test Case: le_add (0-4 edges), le_mul (≥0 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=0, 
        min_extra_edges_add_max=4, 
        min_extra_edges_mul=0, 
        max_models_to_find=1000000000 # Look for more models
    )
    print("\n" + "="*70 + "\n")

    print(f"\n--- Test Case: le_add (0-5 edges), le_mul (≥0 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=0, 
        min_extra_edges_add_max=5, 
        min_extra_edges_mul=0, 
        max_models_to_find=1000000000 # Look for more models
    )
    print("\n" + "="*70 + "\n")

    print(f"\n--- Test Case: le_add (0-6 edges), le_mul (≥0 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=0, 
        min_extra_edges_add_max=6, 
        min_extra_edges_mul=0, 
        max_models_to_find=1000000000 # Look for more models
    )
    print("\n" + "="*70 + "\n")

    print(f"\n--- Test Case: le_add (0-7 edges), le_mul (≥0 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=0, 
        min_extra_edges_add_max=7, 
        min_extra_edges_mul=0, 
        max_models_to_find=1000000000 # Look for more models
    )
    print("\n" + "="*70 + "\n")

    print(f"\n--- Test Case: le_add (0-8 edges), le_mul (≥0 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=0, 
        min_extra_edges_add_max=8, 
        min_extra_edges_mul=0, 
        max_models_to_find=1000000000 # Look for more models
    )
    print("\n" + "="*70 + "\n")

    print(f"\n--- Test Case: le_add (0-9 edges), le_mul (≥0 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=0, 
        min_extra_edges_add_max=9, 
        min_extra_edges_mul=0, 
        max_models_to_find=1000000000 # Look for more models
    )
    print("\n" + "="*70 + "\n")

    print(f"\n--- Test Case: le_add (0-10 edges), le_mul (≥0 edges) ---")
    run_T1_find_dual_monotonic_pos_tweaked(
        current_omega=current_omega_test_t1, 
        min_extra_edges_add_min=0, 
        min_extra_edges_add_max=10, 
        min_extra_edges_mul=0, 
        max_models_to_find=1000000000 # Look for more models
    )
    print("\n" + "="*70 + "\n")"""