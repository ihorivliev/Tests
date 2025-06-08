# Prove_DFI_Comparability_Breaks_Add_Monotonicity_Omega3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, Function, GE, LT, LE)
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
# S_ORD_PY_KEYS: List[int] = sorted(S_ORD_ELEMENT_MAP.keys()) # Not strictly needed here

# --- AVCA S_Ω (Algebraic Space for Ω=3) Definitions ---
AVCA_U_ALG = Int(0)
AVCA_DFI1_ALG = Int(1)
AVCA_DFI2_ALG = Int(2)

# --- Semantic Aspect Definitions ---
SEM_ZERO_ASPECT = Int(0) 
SEM_AREO_ASPECT = Int(1) 
SEM_DFI_ASPECT  = Int(2) 

# --- Helper Functions (Copied and verified from previous scripts) ---
# --- These define π, π⁻¹, AVCA ops, aspect determination, and mapped_avca_add_s_ord ---
def pi_algebraic(s_ord_element_smt: FNode, current_omega: int = 3) -> FNode:
    # For Omega=3: DFI1s(0)->DFI1a(1), DFI2s(1)->DFI2a(2), ZUs(2)->Ua(0), AUs(3)->Ua(0)
    return Ite(Equals(s_ord_element_smt, DFI1s), AVCA_DFI1_ALG,
           Ite(Equals(s_ord_element_smt, DFI2s), AVCA_DFI2_ALG, AVCA_U_ALG)) 

def pi_aspect_inherent(s_ord_element_smt: FNode, current_omega: int = 3) -> FNode:
    return Ite(Equals(s_ord_element_smt, ZUs), SEM_ZERO_ASPECT,
           Ite(Equals(s_ord_element_smt, AUs), SEM_AREO_ASPECT, SEM_DFI_ASPECT))

def pi_inv_s_ord(avca_algebraic_result: FNode, avca_semantic_aspect: FNode, current_omega: int = 3) -> FNode:
    is_alg_U = Equals(avca_algebraic_result, AVCA_U_ALG)
    return Ite(is_alg_U,
               Ite(Equals(avca_semantic_aspect, SEM_ZERO_ASPECT), ZUs, AUs), 
           Ite(Equals(avca_algebraic_result, AVCA_DFI1_ALG), DFI1s,
           Ite(Equals(avca_algebraic_result, AVCA_DFI2_ALG), DFI2s, AUs)))

def avca_add_bc_omega3_algebraic(a: FNode, b: FNode, omega: int = 3) -> FNode: # Name implies Omega=3 but takes omega param
    is_a_U=Equals(a,AVCA_U_ALG); is_b_U=Equals(b,AVCA_U_ALG)
    s=Plus(a,b); return Ite(is_a_U,b,Ite(is_b_U,a,Ite(LT(s,Int(omega)),s,AVCA_U_ALG)))

def determine_avca_effective_aspects(op_char: Literal["add"], 
                                     s_ord_in1: FNode, s_ord_in2: FNode, 
                                     omega: int = 3) -> Tuple[FNode, FNode]:
    pi_s1_alg=pi_algebraic(s_ord_in1,omega); pi_s2_alg=pi_algebraic(s_ord_in2,omega)
    asp_s1_inh=pi_aspect_inherent(s_ord_in1,omega); asp_s2_inh=pi_aspect_inherent(s_ord_in2,omega)
    eff_s1=Ite(Equals(asp_s1_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s1_inh)
    eff_s2=Ite(Equals(asp_s2_inh,SEM_DFI_ASPECT),SEM_ZERO_ASPECT,asp_s2_inh)
    is_pi_s1_dfi=Not(Equals(pi_s1_alg,AVCA_U_ALG));is_pi_s2_dfi=Not(Equals(pi_s2_alg,AVCA_U_ALG))
    is_dfi_dfi_interaction=And(is_pi_s1_dfi,is_pi_s2_dfi)
    dfi_dfi_op_causes_saturation=FALSE()
    if op_char=="add": dfi_dfi_op_causes_saturation=GE(Plus(pi_s1_alg,pi_s2_alg),Int(omega))
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

def assert_po_axioms(assertions_list: List[FNode], le_func: FNode, s_ord_elements_for_po: List[FNode]):
    for x_refl in s_ord_elements_for_po: assertions_list.append(le_func(x_refl, x_refl))
    for x_anti in s_ord_elements_for_po:
        for y_anti in s_ord_elements_for_po:
            if not (x_anti.is_constant(SMT_INT_TYPE) and y_anti.is_constant(SMT_INT_TYPE) and x_anti.constant_value() == y_anti.constant_value()):
                assertions_list.append(Implies(And(le_func(x_anti,y_anti), le_func(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in s_ord_elements_for_po:
        for y_trans in s_ord_elements_for_po:
            for z_trans in s_ord_elements_for_po:
                assertions_list.append(Implies(And(le_func(x_trans,y_trans), le_func(y_trans,z_trans)), le_func(x_trans,z_trans)))

def assert_monotonicity_for_add_op(assertions_list: List[FNode], le_func: FNode, 
                                   current_omega: int, s_ord_elements_for_mono: List[FNode]):
    mono_conjuncts: List[FNode] = []
    if not s_ord_elements_for_mono: return
    for x1 in s_ord_elements_for_mono:
        for y1 in s_ord_elements_for_mono:
            premise = le_func(x1, y1)
            for a_mono in s_ord_elements_for_mono:
                res_x1_a=mapped_avca_add_s_ord(x1,a_mono,current_omega); res_y1_a=mapped_avca_add_s_ord(y1,a_mono,current_omega)
                mono_conjuncts.append(Implies(premise, le_func(res_x1_a, res_y1_a)))
                res_a_x1=mapped_avca_add_s_ord(a_mono,x1,current_omega); res_a_y1=mapped_avca_add_s_ord(a_mono,y1,current_omega)
                mono_conjuncts.append(Implies(premise, le_func(res_a_x1, res_a_y1)))
    if mono_conjuncts: assertions_list.append(And(mono_conjuncts))

# --- Main Test Function ---
def run_T4_prove_le_add_sparseness_omega3(
    problematic_relation_to_test: Tuple[FNode, FNode], 
    relation_name: str
):
    current_omega = 3 # This script is hardcoded for Omega=3 for simplicity of S_ord elements
    
    print(f"\n====== SCRIPT: Prove_DFI_Comparability_Breaks_Add_Monotonicity_Omega3 ======")
    print(f"Purpose: For S_ord (Ω=3), test if a PO 'le_add' can exist such that:")
    print(f"         1. 'le_add' is a valid PO.")
    print(f"         2. Mapped AVCA-⊕ (⊕') is monotone w.r.t. 'le_add'.")
    print(f"         3. AND 'le_add' includes the specific relation: {S_ORD_ELEMENT_MAP[problematic_relation_to_test[0].constant_value()]} <= {S_ORD_ELEMENT_MAP[problematic_relation_to_test[1].constant_value()]}.")
    print(f"Expected: UNSAT (Proving this specific relation breaks ⊕'-monotonicity or PO validity under it).")

    le_add_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le_add = Symbol(f"le_add_T4_test_{relation_name}", le_add_func_type) 

    assertions = []
    
    print("\n--- Asserting 'le_add' is a PO ---")
    assert_po_axioms(assertions, le_add, SMT_S_ORD_ELEMENTS)

    print("\n--- Asserting Monotonicity for mapped AVCA-⊕ w.r.t. 'le_add' ---")
    assert_monotonicity_for_add_op(assertions, le_add, current_omega, SMT_S_ORD_ELEMENTS)
    
    print(f"\n--- Asserting the specific problematic relation: {S_ORD_ELEMENT_MAP[problematic_relation_to_test[0].constant_value()]} <= {S_ORD_ELEMENT_MAP[problematic_relation_to_test[1].constant_value()]} ---")
    # Ensure the relation is non-reflexive for it to be "problematic" in the context of T4's goal
    if problematic_relation_to_test[0].constant_value() == problematic_relation_to_test[1].constant_value():
        print("Error: Problematic relation must be non-reflexive for this T4 test.")
        return
    assertions.append(le_add(problematic_relation_to_test[0], problematic_relation_to_test[1]))

    print(f"\n--- Solving with SMT (Z3) ---")
    with Solver(name="z3", logic="QF_UFLIA") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        smt_status_msg = "SAT (Found a PO satisfying all conditions - CONTRADICTS HYPOTHESIS)" if result else \
                         "UNSAT (No such PO exists - SUPPORTS HYPOTHESIS)"
        print(f"\nSMT Result for T4 Test ({relation_name}): {smt_status_msg}")

        if result:
            model = s.get_model()
            print(f"  WARNING: SMT found a model. This means mapped AVCA-⊕ CAN be monotone w.r.t. a PO including {relation_name}.")
            print(f"  This contradicts the auditor's sketch proof for this specific relation at Ω=3.")
            print(f"  Model for 'le_add' including {relation_name}:")
            
            output_lines: List[str] = []
            num_extra = 0
            for x_smt in SMT_S_ORD_ELEMENTS: 
                x_py = x_smt.constant_value()
                for y_smt in SMT_S_ORD_ELEMENTS: 
                    y_py = y_smt.constant_value()
                    if model.get_value(le_add(x_smt, y_smt)) == TRUE():
                        output_lines.append(f"  {S_ORD_ELEMENT_MAP[x_py]:<7} <= {S_ORD_ELEMENT_MAP[y_py]:<7}")
                        if x_py != y_py: num_extra +=1
            for line in sorted(list(set(output_lines))): print(line)
            print(f"  Number of non-reflexive true relations in this model: {num_extra}")
        else: 
            print(f"  SUCCESS: SMT proved UNSAT. This means for Ω=3, mapped AVCA-⊕ cannot be monotone")
            print(f"           w.r.t. any valid PO that also includes the relation {relation_name}.")
            print(f"  This mechanised result supports the auditor's T-4 sketch proof for this specific DFI-related edge.")

    print(f"\n====== Prove_DFI_Comparability_Breaks_Add_Monotonicity_Omega3 ({relation_name}) Finished ======")

if __name__ == "__main__":
    # Auditor's T-4 sketch proof implies DFI-related comparabilities break ⊕-monotonicity.
    # Let's test a few key "problematic" DFI-related edges for le_add on S_ord (Ω=3).
    # S_ord elements: DFI1s=Int(0), DFI2s=Int(1), ZUs=Int(2), AUs=Int(3)
    
    # Test Case 1: DFI1s <= DFI2s
    print("\n" + "="*70 + "\n")
    run_T4_prove_le_add_sparseness_omega3(
        problematic_relation_to_test=(DFI1s, DFI2s),
        relation_name="DFI1s_le_DFI2s"
    )
    
    # Test Case 2: DFI1s <= ZUs
    print("\n" + "="*70 + "\n")
    run_T4_prove_le_add_sparseness_omega3(
        problematic_relation_to_test=(DFI1s, ZUs),
        relation_name="DFI1s_le_ZUs"
    )

    # Test Case 3: DFI1s <= AUs (This was part of a common monotonic PO in Ch.X for simpler mapped ops)
    # The previous B1/E-1 runs with Find_All_SL_Common_Monotonic_POs... for a *common* PO
    # already showed UNSAT for min_extra_edges=2 (which would include this relation if ZUs<=AUs was the other).
    # This test focuses on if *⊕ alone* can be monotone with this.
    print("\n" + "="*70 + "\n")
    run_T4_prove_le_add_sparseness_omega3(
        problematic_relation_to_test=(DFI1s, AUs),
        relation_name="DFI1s_le_AUs"
    )

    # Test Case 4: One of the "allowed" sparse relations (should be SAT if we ONLY assert this)
    # This is more of a sanity check for the script itself if it can find the known sparse solutions.
    # However, the script asserts THIS problematic relation *in addition* to seeking general monotonicity.
    # So if (DFI1s, DFI2s) is asserted, and it's already known that adding it breaks general monotonicity, we expect UNSAT.
    # The point of T4 is to prove specific edges make le_add non-⊕-monotonic.

    # Test Case from Auditor's sketch: d1 < d2 where d1, d2 are DFIs
    # Let d1 = DFI1s, d2 = DFI2s. We already tested this.
    # What if we test ZUs <= DFI1s?
    print("\n" + "="*70 + "\n")
    run_T4_prove_le_add_sparseness_omega3(
        problematic_relation_to_test=(ZUs, DFI1s),
        relation_name="ZUs_le_DFI1s"
    )