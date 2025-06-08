# Test_C2_Full_Check_For_Candidate_PO_Omega3_v2.py
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

def determine_avca_effective_aspects(op_char: Literal["add", "mul"], 
                                     s_ord_in1: FNode, s_ord_in2: FNode, 
                                     omega: int = 3) -> Tuple[FNode, FNode]:
    pi_s1_alg=pi_algebraic(s_ord_in1); pi_s2_alg=pi_algebraic(s_ord_in2)
    asp_s1_inh=pi_aspect_inherent(s_ord_in1); asp_s2_inh=pi_aspect_inherent(s_ord_in2)
    eff_s1=Ite(Equals(asp_s1_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s1_inh)
    eff_s2=Ite(Equals(asp_s2_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s2_inh)
    is_pi_s1_dfi=Not(Equals(pi_s1_alg,AVCA_U_ALG));is_pi_s2_dfi=Not(Equals(pi_s2_alg,AVCA_U_ALG))
    is_dfi_dfi_interaction=And(is_pi_s1_dfi,is_pi_s2_dfi)
    dfi_dfi_op_causes_saturation=FALSE() # Renamed from causes_sat for clarity
    if op_char=="add": 
        classical_sum_avca = Plus(pi_s1_alg,pi_s2_alg)
        dfi_dfi_op_causes_saturation=GE(classical_sum_avca,Int(omega))
    elif op_char=="mul": 
        classical_prod_avca = Times(pi_s1_alg,pi_s2_alg)
        dfi_dfi_op_causes_saturation=GE(classical_prod_avca,Int(omega))
    eff_s1=Ite(And(is_dfi_dfi_interaction,dfi_dfi_op_causes_saturation),SEM_AREO_ASPECT,eff_s1)
    eff_s2=Ite(And(is_dfi_dfi_interaction,dfi_dfi_op_causes_saturation),SEM_AREO_ASPECT,eff_s2)
    return eff_s1,eff_s2

def get_avca_result_aspect(alg_res_avca: FNode, eff_asp_a_avca: FNode, eff_asp_b_avca: FNode) -> FNode:
    is_res_U=Equals(alg_res_avca,AVCA_U_ALG)
    res_areo_if_U=Or(Equals(eff_asp_a_avca,SEM_AREO_ASPECT),Equals(eff_asp_b_avca,SEM_AREO_ASPECT))
    return Ite(is_res_U,Ite(res_areo_if_U,SEM_AREO_ASPECT,SEM_ZERO_ASPECT),SEM_DFI_ASPECT)

def mapped_avca_add_s_ord(s_ord_a: FNode, s_ord_b: FNode) -> FNode: # Now defined globally
    pi_a_alg=pi_algebraic(s_ord_a); pi_b_alg=pi_algebraic(s_ord_b)
    avca_alg_res=avca_add_bc_omega3_algebraic(pi_a_alg,pi_b_alg)
    eff_asp_a,eff_asp_b=determine_avca_effective_aspects("add",s_ord_a,s_ord_b)
    avca_sem_asp=get_avca_result_aspect(avca_alg_res,eff_asp_a,eff_asp_b)
    return pi_inv_s_ord(avca_alg_res,avca_sem_asp)

def mapped_avca_mul_s_ord(s_ord_a: FNode, s_ord_b: FNode) -> FNode: # Now defined globally
    pi_a_alg=pi_algebraic(s_ord_a); pi_b_alg=pi_algebraic(s_ord_b)
    avca_alg_res=avca_mul_bc_omega3_algebraic(pi_a_alg,pi_b_alg)
    eff_asp_a,eff_asp_b=determine_avca_effective_aspects("mul",s_ord_a,s_ord_b)
    avca_sem_asp=get_avca_result_aspect(avca_alg_res,eff_asp_a,eff_asp_b)
    return pi_inv_s_ord(avca_alg_res,avca_sem_asp)

def op_table_to_str_c2_sl(op_func_symbol: FNode, model: Solver, op_char: str) -> str:
    s = f"   {op_char}  | " + " | ".join([S_ORD_ELEMENT_MAP[k].center(5) for k in S_ORD_PY_KEYS])
    separator = "-----|-" + "-|-".join(["-----" for _ in S_ORD_PY_KEYS]) + "-|"
    lines = [s, separator]
    for r_key in S_ORD_PY_KEYS:
        r_smt = Int(r_key)
        row_str = f"{S_ORD_ELEMENT_MAP[r_key]:<5}| "
        for c_key in S_ORD_PY_KEYS:
            c_smt = Int(c_key)
            op_call_result_fnode = op_func_symbol(r_smt, c_smt)
            val_fnode_in_model = model.get_value(op_call_result_fnode)
            row_str += f"{S_ORD_ELEMENT_MAP[val_fnode_in_model.constant_value()].center(5)}| "
        lines.append(row_str)
    return "\n".join(lines)

def run_C2_full_check_for_po(
    omega_val: int, 
    candidate_po_true_relations_int: List[Tuple[int, int]], 
    po_name: str
):
    if omega_val != 3:
        print(f"ERROR: This script version is hardcoded for Ω=3 (S_ord size 4).")
        return

    print(f"====== SCRIPT: Test_C2_Full_Check_For_Candidate_PO_Omega3_v2 (Ω={omega_val}) ======") # Added _v2 to name
    print(f"Purpose: For CANDIDATE PO '{po_name}' on S_ord = {{DFI1s,DFI2s,ZUs,AUs}}:")
    print("         1. Test if it's a valid PO and common monotonic for mapped AVCA ⊕,⊗.")
    print("         2. If yes, test if it forms a DISTRIBUTIVE LATTICE.")
    print("         3. If yes, test ASPECT HOMOMORPHISM to AVCA-Ω.")
    # Corrected: Printing only non-reflexive part of input for clarity
    non_reflex_input_po = [(S_ORD_ELEMENT_MAP[x], S_ORD_ELEMENT_MAP[y]) for x,y in candidate_po_true_relations_int if x!=y]
    print(f"Input True Non-Reflexive Relations for PO '{po_name}': {non_reflex_input_po}")
    print("Expected: SAT at each step if C-2 holds for this PO.\n")

    le_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    # Using a more unique name for the 'le' function symbol in SMT
    le_smt_func_name = f"le_{po_name.replace(' ','_').replace('≤','le').replace(',','').replace('(','').replace(')','')[:20]}" # Shorter unique name
    le = Symbol(le_smt_func_name, le_func_type) 
    
    po_assertions: List[FNode] = []
    all_true_relations_for_le_py_keys: Set[Tuple[int,int]] = set()
    for x_py_key in S_ORD_PY_KEYS: all_true_relations_for_le_py_keys.add((x_py_key, x_py_key))
    for lesser_py, greater_py in candidate_po_true_relations_int:
        all_true_relations_for_le_py_keys.add((lesser_py, greater_py))

    for x_smt in SMT_S_ORD_ELEMENTS:
        for y_smt in SMT_S_ORD_ELEMENTS:
            if (x_smt.constant_value(), y_smt.constant_value()) in all_true_relations_for_le_py_keys:
                po_assertions.append(le(x_smt, y_smt))
            else:
                po_assertions.append(Not(le(x_smt, y_smt)))
    
    for x_refl in SMT_S_ORD_ELEMENTS: po_assertions.append(le(x_refl, x_refl))
    for x_anti in SMT_S_ORD_ELEMENTS:
        for y_anti in SMT_S_ORD_ELEMENTS:
            po_assertions.append(Implies(And(le(x_anti,y_anti), le(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in SMT_S_ORD_ELEMENTS:
        for y_trans in SMT_S_ORD_ELEMENTS:
            for z_trans in SMT_S_ORD_ELEMENTS:
                po_assertions.append(Implies(And(le(x_trans,y_trans), le(y_trans,z_trans)), le(x_trans,z_trans)))

    monotonicity_conjuncts: List[FNode] = []
    for x1 in SMT_S_ORD_ELEMENTS:
        for y1 in SMT_S_ORD_ELEMENTS:
            premise = le(x1, y1)
            for a_mono in SMT_S_ORD_ELEMENTS:
                add_res_x1_a=mapped_avca_add_s_ord(x1,a_mono); add_res_y1_a=mapped_avca_add_s_ord(y1,a_mono)
                monotonicity_conjuncts.append(Implies(premise, le(add_res_x1_a, add_res_y1_a)))
                add_res_a_x1=mapped_avca_add_s_ord(a_mono,x1); add_res_a_y1=mapped_avca_add_s_ord(a_mono,y1)
                monotonicity_conjuncts.append(Implies(premise, le(add_res_a_x1, add_res_a_y1)))
                mul_res_x1_a=mapped_avca_mul_s_ord(x1,a_mono); mul_res_y1_a=mapped_avca_mul_s_ord(y1,a_mono)
                monotonicity_conjuncts.append(Implies(premise, le(mul_res_x1_a, mul_res_y1_a)))
                mul_res_a_x1=mapped_avca_mul_s_ord(a_mono,x1); mul_res_a_y1=mapped_avca_mul_s_ord(a_mono,y1)
                monotonicity_conjuncts.append(Implies(premise, le(mul_res_a_x1, mul_res_a_y1)))
    po_assertions.append(And(monotonicity_conjuncts))

    print(f"\n--- Stage 1: Checking PO Validity & Common Monotonicity for '{po_name}' ---")
    with Solver(name="z3", logic="QF_UFLIA") as s_po_mono:
        for an_assertion in po_assertions: s_po_mono.add_assertion(an_assertion)
        is_po_common_monotonic = s_po_mono.solve()
        print(f"SMT Result for PO Validity & Common Monotonicity: {'SAT (PO is valid & common monotonic)' if is_po_common_monotonic else 'UNSAT (PO invalid or not common monotonic)'}")
        if not is_po_common_monotonic:
            print(f"  PO '{po_name}' is NOT a valid common monotonic PO with current mapped ops. C-2 check stops here for this PO.")
            print(f"====== Test_C2_Full_Check for PO '{po_name}' Finished Early ======")
            return

    op_func_type = FunctionType(SMT_INT_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    # Using unique names for join/meet based on PO name to avoid SMT conflicts if function is run multiple times
    join_op = Symbol(f"join_{po_name.replace(' ','_')[:10]}", op_func_type)
    meet_op = Symbol(f"meet_{po_name.replace(' ','_')[:10]}", op_func_type)
    
    lattice_assertions = list(po_assertions) 
    print(f"\n--- Stage 2: Testing if PO '{po_name}' forms a Distributive Lattice ---")
    # (Lattice and Distributivity assertions remain the same)
    for x_lattice in SMT_S_ORD_ELEMENTS:
        for y_lattice in SMT_S_ORD_ELEMENTS:
            lub_xy = join_op(x_lattice, y_lattice); glb_xy = meet_op(x_lattice, y_lattice)
            lattice_assertions.append(Or([Equals(lub_xy, elem) for elem in SMT_S_ORD_ELEMENTS]))
            lattice_assertions.append(Or([Equals(glb_xy, elem) for elem in SMT_S_ORD_ELEMENTS]))
            lattice_assertions.append(le(x_lattice, lub_xy)); lattice_assertions.append(le(y_lattice, lub_xy))
            for z_lub in SMT_S_ORD_ELEMENTS: lattice_assertions.append(Implies(And(le(x_lattice, z_lub), le(y_lattice, z_lub)), le(lub_xy, z_lub)))
            lattice_assertions.append(le(glb_xy, x_lattice)); lattice_assertions.append(le(glb_xy, y_lattice))
            for z_glb in SMT_S_ORD_ELEMENTS: lattice_assertions.append(Implies(And(le(z_glb, x_lattice), le(z_glb, y_lattice)), le(z_glb, glb_xy)))
    for x_dist in SMT_S_ORD_ELEMENTS:
        for y_dist in SMT_S_ORD_ELEMENTS:
            for z_dist in SMT_S_ORD_ELEMENTS:
                lhs1 = meet_op(x_dist, join_op(y_dist, z_dist)); rhs1 = join_op(meet_op(x_dist, y_dist), meet_op(x_dist, z_dist))
                lattice_assertions.append(Equals(lhs1, rhs1))
                lhs2 = join_op(x_dist, meet_op(y_dist, z_dist)); rhs2 = meet_op(join_op(x_dist, y_dist), join_op(x_dist, z_dist))
                lattice_assertions.append(Equals(lhs2, rhs2))

    s_ord_join_py_table_model: Union[Dict[Tuple[int,int],int], None] = None
    s_ord_meet_py_table_model: Union[Dict[Tuple[int,int],int], None] = None

    with Solver(name="z3", logic="QF_UFLIA") as s_lattice:
        for an_assertion in lattice_assertions: s_lattice.add_assertion(an_assertion)
        is_distributive_lattice = s_lattice.solve()
        print(f"SMT Result for Distributive Lattice Check: {'SAT' if is_distributive_lattice else 'UNSAT'}")
        if not is_distributive_lattice:
            print(f"  PO '{po_name}' does NOT form a distributive lattice. C-2 check stops here for this PO.")
            print(f"====== Test_C2_Full_Check for PO '{po_name}' Finished Early ======")
            return
        else:
            model = s_lattice.get_model()
            print(f"  PO '{po_name}' CAN form a distributive lattice.")
            s_ord_join_py_table_model = {}
            s_ord_meet_py_table_model = {}
            for rk_py in S_ORD_PY_KEYS:
                for ck_py in S_ORD_PY_KEYS:
                    r_smt_tbl, c_smt_tbl = Int(rk_py), Int(ck_py)
                    s_ord_join_py_table_model[(rk_py,ck_py)] = model.get_value(join_op(r_smt_tbl,c_smt_tbl)).constant_value()
                    s_ord_meet_py_table_model[(rk_py,ck_py)] = model.get_value(meet_op(r_smt_tbl,c_smt_tbl)).constant_value()
            print("\n  JOIN (LUB) Table (Candidate ⊕̄):")
            print(op_table_to_str_c2_sl(join_op, model, "∨"))
            print("\n  MEET (GLB) Table (Candidate ⊗̄):")
            print(op_table_to_str_c2_sl(meet_op, model, "∧"))

    if s_ord_join_py_table_model is None or s_ord_meet_py_table_model is None:
        print("Critical error: Lattice tables not extracted after Stage 2 SAT. Aborting B3.")
        return

    hom_assertions: List[FNode] = []
    # Re-define join_op and meet_op as fixed based on the model for this stage
    # This is crucial: these are now constants, not functions being solved for.
    for x_py_key_hom in S_ORD_PY_KEYS:
        x_smt_hom_fixed = Int(x_py_key_hom)
        for y_py_key_hom in S_ORD_PY_KEYS:
            y_smt_hom_fixed = Int(y_py_key_hom)
            hom_assertions.append(Equals(join_op(x_smt_hom_fixed, y_smt_hom_fixed), Int(s_ord_join_py_table_model[(x_py_key_hom, y_py_key_hom)])))
            hom_assertions.append(Equals(meet_op(x_smt_hom_fixed, y_smt_hom_fixed), Int(s_ord_meet_py_table_model[(x_py_key_hom, y_py_key_hom)])))
            
    print(f"\n--- Stage 3: Testing Aspect Homomorphism for PO '{po_name}' (using derived lattice ops) ---")
    all_homomorphisms_hold_smt_conjuncts: List[FNode] = []
    # (Homomorphism assertion logic remains the same as previous B3 script)
    for x_s_ord_smt_loop in SMT_S_ORD_ELEMENTS: 
        for y_s_ord_smt_loop in SMT_S_ORD_ELEMENTS:
            res_s_ord_add = join_op(x_s_ord_smt_loop, y_s_ord_smt_loop) 
            lhs_aspect_add = pi_aspect_inherent(res_s_ord_add) 
            pi_x_avca_alg = pi_algebraic(x_s_ord_smt_loop); pi_y_avca_alg = pi_algebraic(y_s_ord_smt_loop)
            eff_asp_pi_x_add, eff_asp_pi_y_add = determine_avca_effective_aspects("add", x_s_ord_smt_loop, y_s_ord_smt_loop, omega_val)
            res_avca_alg_add = avca_add_bc_omega3_algebraic(pi_x_avca_alg, pi_y_avca_alg, omega_val)
            rhs_aspect_add = get_avca_result_aspect(res_avca_alg_add, eff_asp_pi_x_add, eff_asp_pi_y_add)
            all_homomorphisms_hold_smt_conjuncts.append(Equals(lhs_aspect_add, rhs_aspect_add))

            res_s_ord_mul = meet_op(x_s_ord_smt_loop, y_s_ord_smt_loop)
            lhs_aspect_mul = pi_aspect_inherent(res_s_ord_mul)
            eff_asp_pi_x_mul, eff_asp_pi_y_mul = determine_avca_effective_aspects("mul", x_s_ord_smt_loop, y_s_ord_smt_loop, omega_val)
            res_avca_alg_mul = avca_mul_bc_omega3_algebraic(pi_x_avca_alg, pi_y_avca_alg, omega_val)
            rhs_aspect_mul = get_avca_result_aspect(res_avca_alg_mul, eff_asp_pi_x_mul, eff_asp_pi_y_mul)
            all_homomorphisms_hold_smt_conjuncts.append(Equals(lhs_aspect_mul, rhs_aspect_mul))
    hom_assertions.append(And(all_homomorphisms_hold_smt_conjuncts))

    with Solver(name="z3", logic="QF_UFLIA") as s_hom:
        for an_assertion in hom_assertions: s_hom.add_assertion(an_assertion)
        aspect_hom_holds = s_hom.solve()
        print(f"SMT Result for Aspect Homomorphism: {'SAT (Homomorphism Holds!)' if aspect_hom_holds else 'UNSAT (Homomorphism FAILED)'}")
        if aspect_hom_holds:
            print(f"  SUCCESS! PO '{po_name}' forms a distributive lattice AND satisfies the aspect homomorphism.")
            print("  This STRONGLY SUPPORTS Conjecture C-2 with this PO as the classical cover.")
        else:
            print(f"  FAILURE. PO '{po_name}', while a distributive lattice, FAILED the aspect homomorphism test.")
            print("  This specific PO is falsified as the full C-2 classical cover.")

    print(f"\n====== Test_C2_Full_Check for PO '{po_name}' Finished ======")

if __name__ == "__main__":
    print("This script tests a specific candidate PO for the full C-2 conjecture.")
    print("User must provide a candidate PO from their B1 task (finding common monotonic POs).")
    
    # Candidate PO_A from 'Find_All_SL_Common_Monotonic_POs_Omega3.py' (min_extra_edges=1, Model 1)
    # Relations: ZUs <= AUs (plus reflexives).
    # S_ord: DFI1s=0, DFI2s=1, ZUs=2, AUs=3
    candidate_po_A_name = "DiscretePlus_ZUs_le_AUs"
    candidate_po_A_non_reflexive_true_relations = [(2,3)] # ZUs <= AUs
    run_C2_full_check_for_po(
        omega_val=3, 
        candidate_po_true_relations_int=candidate_po_A_non_reflexive_true_relations,
        po_name=candidate_po_A_name
    )

    print("\n" + "="*70 + "\n")

    # Candidate PO_B from 'Find_All_SL_Common_Monotonic_POs_Omega3.py' (min_extra_edges=1, Model 2)
    # Relations: AUs <= ZUs (plus reflexives).
    candidate_po_B_name = "DiscretePlus_AUs_le_ZUs"
    candidate_po_B_non_reflexive_true_relations = [(3,2)] # AUs <= ZUs
    run_C2_full_check_for_po(
        omega_val=3,
        candidate_po_true_relations_int=candidate_po_B_non_reflexive_true_relations,
        po_name=candidate_po_B_name
    )