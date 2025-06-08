# Test_T3_JoinSemiLattice_For_Add_Aspects_Omega3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, Function, GE, LT)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable, Literal, Union, Set

# --- Globals (Copied from previous, ensure initialize_omega_dependent_globals is called if Ω changes) ---
DFI1s, DFI2s, ZUs, AUs = Int(0), Int(1), Int(2), Int(3) 
SMT_S_ORD_ELEMENTS: List[FNode] = [DFI1s, DFI2s, ZUs, AUs] 
S_ORD_ELEMENT_MAP: Dict[int, str] = {0:"DFI1s",1:"DFI2s",2:"ZUs",3:"AUs"}
S_ORD_PY_KEYS: List[int] = sorted(S_ORD_ELEMENT_MAP.keys())
AVCA_U_ALG=Int(0); AVCA_DFI1_ALG=Int(1); AVCA_DFI2_ALG=Int(2)
SEM_ZERO_ASPECT=Int(0); SEM_AREO_ASPECT=Int(1); SEM_DFI_ASPECT=Int(2)

# --- Helper Functions (Copied from previous, ensure they are suitable for general Ω if used) ---
def pi_algebraic(s_ord_element_smt: FNode, current_omega: int = 3) -> FNode: # Omega param added
    # S_ord DFIsem_j (value j=0 for DFI1s, j=1 for DFI2s when omega=3) maps to DFIalg_(j+1)
    # S_ord ZUs (value omega-1) and AUs (value omega) map to Ualg (value 0)
    # For Omega=3: DFI1s(0)->DFI1a(1), DFI2s(1)->DFI2a(2), ZUs(2)->Ua(0), AUs(3)->Ua(0)
    return Ite(Equals(s_ord_element_smt, DFI1s), AVCA_DFI1_ALG,
           Ite(Equals(s_ord_element_smt, DFI2s), AVCA_DFI2_ALG, AVCA_U_ALG)) 

def pi_aspect_inherent(s_ord_element_smt: FNode, current_omega: int = 3) -> FNode: # Omega param added
    # For Omega=3: ZUs is Int(2), AUs is Int(3) if DFI1s=0, DFI2s=1
    # Needs to use generalized ZUs/AUs values if this were truly OmegaN
    # For fixed Omega=3 S_ord mapping:
    return Ite(Equals(s_ord_element_smt, ZUs), SEM_ZERO_ASPECT,
           Ite(Equals(s_ord_element_smt, AUs), SEM_AREO_ASPECT, SEM_DFI_ASPECT))

def pi_inv_s_ord(avca_algebraic_result: FNode, avca_semantic_aspect: FNode, current_omega: int = 3) -> FNode:
    is_alg_U = Equals(avca_algebraic_result, AVCA_U_ALG)
    # For fixed Omega=3 S_ord mapping:
    return Ite(is_alg_U,
               Ite(Equals(avca_semantic_aspect, SEM_ZERO_ASPECT), ZUs, AUs), 
           Ite(Equals(avca_algebraic_result, AVCA_DFI1_ALG), DFI1s,
           Ite(Equals(avca_algebraic_result, AVCA_DFI2_ALG), DFI2s, AUs))) # Fallback AUs

def avca_add_bc_omega3_algebraic(a: FNode, b: FNode, omega: int = 3) -> FNode:
    is_a_U=Equals(a,AVCA_U_ALG); is_b_U=Equals(b,AVCA_U_ALG)
    s=Plus(a,b); return Ite(is_a_U,b,Ite(is_b_U,a,Ite(LT(s,Int(omega)),s,AVCA_U_ALG)))

def determine_avca_effective_aspects(op_char, s_ord_in1, s_ord_in2, omega=3) -> Tuple[FNode, FNode]:
    pi_s1_alg=pi_algebraic(s_ord_in1,omega); pi_s2_alg=pi_algebraic(s_ord_in2,omega)
    asp_s1_inh=pi_aspect_inherent(s_ord_in1,omega); asp_s2_inh=pi_aspect_inherent(s_ord_in2,omega)
    eff_s1=Ite(Equals(asp_s1_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s1_inh)
    eff_s2=Ite(Equals(asp_s2_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s2_inh)
    is_pi_s1_dfi=Not(Equals(pi_s1_alg,AVCA_U_ALG));is_pi_s2_dfi=Not(Equals(pi_s2_alg,AVCA_U_ALG))
    is_dfi_dfi_interaction=And(is_pi_s1_dfi,is_pi_s2_dfi)
    dfi_dfi_op_causes_saturation=FALSE()
    if op_char=="add": dfi_dfi_op_causes_saturation=GE(Plus(pi_s1_alg,pi_s2_alg),Int(omega))
    # No mul needed for this script focusing on join-semilattice for addition
    eff_s1=Ite(And(is_dfi_dfi_interaction,dfi_dfi_op_causes_saturation),SEM_AREO_ASPECT,eff_s1)
    eff_s2=Ite(And(is_dfi_dfi_interaction,dfi_dfi_op_causes_saturation),SEM_AREO_ASPECT,eff_s2)
    return eff_s1,eff_s2

def get_avca_result_aspect(alg_res_avca: FNode, eff_asp_a_avca: FNode, eff_asp_b_avca: FNode) -> FNode:
    is_res_U=Equals(alg_res_avca,AVCA_U_ALG)
    res_areo_if_U=Or(Equals(eff_asp_a_avca,SEM_AREO_ASPECT),Equals(eff_asp_b_avca,SEM_AREO_ASPECT))
    return Ite(is_res_U,Ite(res_areo_if_U,SEM_AREO_ASPECT,SEM_ZERO_ASPECT),SEM_DFI_ASPECT)

def mapped_avca_add_s_ord(s_ord_a: FNode, s_ord_b: FNode, current_omega: int = 3) -> FNode:
    pi_a_alg=pi_algebraic(s_ord_a,current_omega); pi_b_alg=pi_algebraic(s_ord_b,current_omega)
    avca_alg_res=avca_add_bc_omega3_algebraic(pi_a_alg,pi_b_alg,current_omega)
    eff_asp_a,eff_asp_b=determine_avca_effective_aspects("add",s_ord_a,s_ord_b,current_omega)
    avca_sem_asp=get_avca_result_aspect(avca_alg_res,eff_asp_a,eff_asp_b)
    return pi_inv_s_ord(avca_alg_res,avca_sem_asp,current_omega)

def op_table_to_str_t3(op_func_symbol: FNode, model: Solver, op_char: str) -> str:
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


def run_T3_join_semilattice_check(
    candidate_po_true_relations_int: List[Tuple[int, int]], 
    po_name: str,
    current_omega: int = 3
):
    print(f"\n====== SCRIPT: Test_T3_JoinSemiLattice_For_Add_Aspects_Omega3 (PO: {po_name}) ======")
    print(f"Purpose: For Candidate PO '{po_name}' on S_ord (Ω=3):")
    print("         1. Verify it's a valid PO & mapped AVCA-⊕ is monotone w.r.t it.")
    print("         2. If yes, test if it forms a JOIN-SEMILATTICE (LUBs exist).")
    print("         3. If yes, test if mapped AVCA-⊕ IS this join & aspect homomorphism holds.")
    non_reflex_input_po = [(S_ORD_ELEMENT_MAP[x],S_ORD_ELEMENT_MAP[y]) for x,y in candidate_po_true_relations_int if x!=y]
    print(f"Input True Non-Reflexive Relations for PO '{po_name}': {non_reflex_input_po}")
    print("Expected: SAT at each step if this weaker C-2 variant holds.\n")

    le_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le = Symbol(f"le_T3_{po_name.replace(' ','_')[:10]}", le_func_type)
    
    base_assertions: List[FNode] = []
    # --- Stage 1: Define PO and Test Monotonicity for Mapped AVCA-⊕ ---
    print(f"--- Stage 1: Checking PO Validity & Monotonicity for mapped AVCA-⊕ for '{po_name}' ---")
    all_true_relations_for_le_py_keys: Set[Tuple[int,int]] = set()
    for x_py_key in S_ORD_PY_KEYS: all_true_relations_for_le_py_keys.add((x_py_key, x_py_key))
    for lesser_py, greater_py in candidate_po_true_relations_int:
        all_true_relations_for_le_py_keys.add((lesser_py, greater_py))

    for x_smt in SMT_S_ORD_ELEMENTS:
        for y_smt in SMT_S_ORD_ELEMENTS:
            if (x_smt.constant_value(), y_smt.constant_value()) in all_true_relations_for_le_py_keys:
                base_assertions.append(le(x_smt, y_smt))
            else:
                base_assertions.append(Not(le(x_smt, y_smt)))
    
    for x_refl in SMT_S_ORD_ELEMENTS: base_assertions.append(le(x_refl, x_refl))
    for x_anti in SMT_S_ORD_ELEMENTS:
        for y_anti in SMT_S_ORD_ELEMENTS:
            if not (x_anti.is_constant() and y_anti.is_constant() and x_anti.constant_value() == y_anti.constant_value()):
                base_assertions.append(Implies(And(le(x_anti,y_anti), le(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in SMT_S_ORD_ELEMENTS:
        for y_trans in SMT_S_ORD_ELEMENTS:
            for z_trans in SMT_S_ORD_ELEMENTS:
                base_assertions.append(Implies(And(le(x_trans,y_trans), le(y_trans,z_trans)), le(x_trans,z_trans)))

    mono_conjuncts_add: List[FNode] = []
    for x1 in SMT_S_ORD_ELEMENTS:
        for y1 in SMT_S_ORD_ELEMENTS:
            premise = le(x1, y1)
            for a_mono in SMT_S_ORD_ELEMENTS:
                add_res_x1_a=mapped_avca_add_s_ord(x1,a_mono,current_omega); add_res_y1_a=mapped_avca_add_s_ord(y1,a_mono,current_omega)
                mono_conjuncts_add.append(Implies(premise, le(add_res_x1_a, add_res_y1_a)))
                add_res_a_x1=mapped_avca_add_s_ord(a_mono,x1,current_omega); add_res_a_y1=mapped_avca_add_s_ord(a_mono,y1,current_omega)
                mono_conjuncts_add.append(Implies(premise, le(add_res_a_x1, add_res_a_y1)))
    if mono_conjuncts_add: base_assertions.append(And(mono_conjuncts_add))

    with Solver(name="z3", logic="QF_UFLIA") as s_po_mono_add:
        for an_assertion in base_assertions: s_po_mono_add.add_assertion(an_assertion)
        is_po_monotonic_for_add = s_po_mono_add.solve()
        print(f"SMT Result for PO Validity & AVCA-⊕ Monotonicity: {'SAT (PO valid & ⊕-monotonic)' if is_po_monotonic_for_add else 'UNSAT (PO invalid or not ⊕-monotonic)'}")
        if not is_po_monotonic_for_add:
            print(f"  PO '{po_name}' is NOT valid or not monotonic for mapped AVCA-⊕. T-3 check stops here.")
            print(f"====== Test_T3 for PO '{po_name}' Finished Early ======")
            return

    # --- Stage 2: Test if this PO forms a Join-Semilattice ---
    join_func_type = FunctionType(SMT_INT_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    join_op = Symbol(f"join_T3_{po_name.replace(' ','_')[:10]}", join_func_type)
    
    semilattice_assertions = list(base_assertions) # Start with valid monotonic PO assertions

    print(f"\n--- Stage 2: Testing if PO '{po_name}' forms a Join-Semilattice (LUBs exist) ---")
    for x_lattice in SMT_S_ORD_ELEMENTS:
        for y_lattice in SMT_S_ORD_ELEMENTS:
            lub_xy = join_op(x_lattice, y_lattice)
            semilattice_assertions.append(Or([Equals(lub_xy, elem) for elem in SMT_S_ORD_ELEMENTS])) # In S_ord
            semilattice_assertions.append(le(x_lattice, lub_xy))
            semilattice_assertions.append(le(y_lattice, lub_xy))
            for z_lub in SMT_S_ORD_ELEMENTS: 
                semilattice_assertions.append(Implies(And(le(x_lattice, z_lub), le(y_lattice, z_lub)), le(lub_xy, z_lub)))
    
    # Assert join operation properties: commutativity, associativity, idempotency for join_op
    for x_jsl in SMT_S_ORD_ELEMENTS:
        semilattice_assertions.append(Equals(join_op(x_jsl, x_jsl), x_jsl)) # Idempotency
        for y_jsl in SMT_S_ORD_ELEMENTS:
            semilattice_assertions.append(Equals(join_op(x_jsl, y_jsl), join_op(y_jsl, x_jsl))) # Commutativity
            for z_jsl in SMT_S_ORD_ELEMENTS:
                # Associativity: (x ∨ y) ∨ z = x ∨ (y ∨ z)
                lhs_assoc = join_op(join_op(x_jsl, y_jsl), z_jsl)
                rhs_assoc = join_op(x_jsl, join_op(y_jsl, z_jsl))
                semilattice_assertions.append(Equals(lhs_assoc, rhs_assoc))

    s_ord_join_py_table_model: Union[Dict[Tuple[int,int],int], None] = None
    with Solver(name="z3", logic="QF_UFLIA") as s_jsl:
        for an_assertion in semilattice_assertions: s_jsl.add_assertion(an_assertion)
        is_join_semilattice = s_jsl.solve()
        print(f"SMT Result for Join-Semilattice Check: {'SAT' if is_join_semilattice else 'UNSAT'}")
        if not is_join_semilattice:
            print(f"  PO '{po_name}' does NOT form a join-semilattice. T-3 check stops here.")
            print(f"====== Test_T3 for PO '{po_name}' Finished Early ======")
            return
        else:
            model = s_jsl.get_model()
            print(f"  PO '{po_name}' CAN form a join-semilattice.")
            s_ord_join_py_table_model = {}
            for rk_py in S_ORD_PY_KEYS:
                for ck_py in S_ORD_PY_KEYS:
                    r_smt_tbl, c_smt_tbl = Int(rk_py), Int(ck_py)
                    s_ord_join_py_table_model[(rk_py,ck_py)] = model.get_value(join_op(r_smt_tbl,c_smt_tbl)).constant_value()
            print("\n  JOIN (LUB) Table (Candidate ⊕̄ for join-semilattice):")
            print(op_table_to_str_t3(join_op, model, "∨_jsl"))

    if s_ord_join_py_table_model is None: return # Should not happen if SAT

    # --- Stage 3: Test if mapped AVCA-⊕ IS this join & Aspect Homomorphism ---
    hom_assertions: List[FNode] = []
     # Define join_op SMT function based on the model's table for this stage
    for x_py_key_hom in S_ORD_PY_KEYS:
        x_smt_hom_fixed = Int(x_py_key_hom)
        for y_py_key_hom in S_ORD_PY_KEYS:
            y_smt_hom_fixed = Int(y_py_key_hom)
            hom_assertions.append(Equals(join_op(x_smt_hom_fixed, y_smt_hom_fixed), Int(s_ord_join_py_table_model[(x_py_key_hom, y_py_key_hom)])))

    print(f"\n--- Stage 3: Testing if mapped AVCA-⊕ IS join_op AND Aspect Homomorphism holds ---")
    all_homomorphisms_hold_smt_conjuncts: List[FNode] = []
    for x_s_ord_smt_loop in SMT_S_ORD_ELEMENTS: 
        for y_s_ord_smt_loop in SMT_S_ORD_ELEMENTS:
            s_ord_join_result = join_op(x_s_ord_smt_loop, y_s_ord_smt_loop)
            mapped_avca_add_result = mapped_avca_add_s_ord(x_s_ord_smt_loop, y_s_ord_smt_loop, current_omega)
            
            # 1. Algebraic Homomorphism: mapped_avca_add_s_ord == s_ord_join_result
            all_homomorphisms_hold_smt_conjuncts.append(Equals(mapped_avca_add_result, s_ord_join_result))
            
            # 2. Aspect Homomorphism: aspect_of(π(s_ord_join_result)) == aspect_of_AVCA_add(π(x̄), π(ȳ))
            # LHS aspect comes from the s_ord_join_result
            lhs_aspect_add = pi_aspect_inherent(s_ord_join_result, current_omega)

            # RHS aspect (already calculated within mapped_avca_add_s_ord effectively)
            # We need to get the aspect of the S_ord element that mapped_avca_add_s_ord produced.
            rhs_aspect_add = pi_aspect_inherent(mapped_avca_add_result, current_omega) # Aspect of the mapped AVCA result

            all_homomorphisms_hold_smt_conjuncts.append(Equals(lhs_aspect_add, rhs_aspect_add))
            
    hom_assertions.append(And(all_homomorphisms_hold_smt_conjuncts))

    with Solver(name="z3", logic="QF_UFLIA") as s_hom:
        for an_assertion in hom_assertions: s_hom.add_assertion(an_assertion)
        aspect_hom_holds = s_hom.solve()
        print(f"SMT Result for 'mapped AVCA-⊕ IS join' AND Aspect Homomorphism: {'SAT (Holds!)' if aspect_hom_holds else 'UNSAT (Failed)'}")
        if aspect_hom_holds:
            print(f"  SUCCESS! For PO '{po_name}' (a join-semilattice):")
            print("          Mapped AVCA-⊕ IS its join operation, AND")
            print("          the aspect homomorphism holds (aspect of π(join) == aspect of mapped AVCA-⊕ result).")
            print("  This STRONGLY SUPPORTS a weaker C-2 variant (T-3) for AVCA-⊕ and its aspect logic.")
        else:
            print(f"  FAILURE. For PO '{po_name}' (a join-semilattice):")
            print("          Either mapped AVCA-⊕ is NOT its join operation, OR the aspect homomorphism FAILED.")
            print("          This candidate for T-3 is falsified.")

    print(f"\n====== Test_T3 for PO '{po_name}' Finished ======")


if __name__ == "__main__":
    print("This script tests Task T-3: For a given PO on S_ord (Ω=3),")
    print("is it a join-semilattice where mapped AVCA-⊕ is the join & aspect homomorphism holds?")
    
    # Candidate PO_A from previous B1 run (min_extra_edges=1, Model 1 for common mono)
    # This PO was: Reflexives + ZUs <= AUs. (DFI1s=0, DFI2s=1, ZUs=2, AUs=3)
    # It was common monotonic for ⊕ and ⊗. Now test only for ⊕ monotonicity and join-semilattice.
    candidate_po_A_name = "DiscretePlus_ZUs_le_AUs_for_Add"
    candidate_po_A_non_reflexive_true_relations = [(2,3)] # ZUs <= AUs
    
    run_T3_join_semilattice_check(
        candidate_po_true_relations_int=candidate_po_A_non_reflexive_true_relations,
        po_name=candidate_po_A_name,
        current_omega=3
    )

    print("\n" + "="*70 + "\n")

    # Candidate PO_B (Discrete + AUs <= ZUs) could also be tested.
    # And the Discrete PO itself.
    candidate_po_Discrete_name = "DiscretePO_for_Add"
    candidate_po_Discrete_non_reflex_relations = []
    run_T3_join_semilattice_check(
        candidate_po_true_relations_int=candidate_po_Discrete_non_reflex_relations,
        po_name=candidate_po_Discrete_name,
        current_omega=3
    )