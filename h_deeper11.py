# Test_B3_SL_Aspect_Homomorphism_Omega3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, Function, GE, LT)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable, Literal, Union

# --- Definitions for S_ord (Ω=3) ---
# S_ord elements: DFI1s=0, DFI2s=1, ZUs=2, AUs=3
DFI1s, DFI2s, ZUs, AUs = Int(0), Int(1), Int(2), Int(3) 
SMT_S_ORD_ELEMENTS: List[FNode] = [DFI1s, DFI2s, ZUs, AUs] 
S_ORD_ELEMENT_MAP: Dict[int, str] = {
    DFI1s.constant_value(): "DFI1s", 
    DFI2s.constant_value(): "DFI2s", 
    ZUs.constant_value(): "ZUs", 
    AUs.constant_value(): "AUs"
}
S_ORD_PY_KEYS: List[int] = sorted(S_ORD_ELEMENT_MAP.keys())

# --- Definitions for AVCA S_Ω (Ω=3) ---
AVCA_U_ALG = Int(0)
AVCA_DFI1_ALG = Int(1)
AVCA_DFI2_ALG = Int(2)

# --- Aspect Representation for SMT (Semantic Aspects) ---
SEM_ZERO_ASPECT = Int(0) # Represents "zero" aspect
SEM_AREO_ASPECT = Int(1) # Represents "areo" aspect
SEM_DFI_ASPECT  = Int(2) # Placeholder for when result is DFI (neither ZU nor AU)

# --- Quotient Map π: S_ord -> S_Ω ---
def pi_algebraic(s_ord_element_smt: FNode) -> FNode:
    # Maps S_ord Int(0..3) to AVCA_S_Omega Int(0..2)
    return Ite(Equals(s_ord_element_smt, DFI1s), AVCA_DFI1_ALG,
           Ite(Equals(s_ord_element_smt, DFI2s), AVCA_DFI2_ALG,
           AVCA_U_ALG)) # Both ZUs and AUs map to AVCA_U_ALG

def pi_aspect_inherent(s_ord_element_smt: FNode) -> FNode:
    # Inherent semantic aspect of an S_ord element if it represents a Unio state
    return Ite(Equals(s_ord_element_smt, ZUs), SEM_ZERO_ASPECT,
           Ite(Equals(s_ord_element_smt, AUs), SEM_AREO_ASPECT,
           SEM_DFI_ASPECT)) # DFI S_ord elements don't pre-define a Unio aspect

# --- Standard AVCA Operations (Algebraic Part for S_Ω=3 - "Best Combination") ---
def avca_add_bc_omega3_algebraic(a_avca_smt: FNode, b_avca_smt: FNode, current_omega: int = 3) -> FNode:
    is_a_U = Equals(a_avca_smt, AVCA_U_ALG)
    is_b_U = Equals(b_avca_smt, AVCA_U_ALG)
    dfi_sum_val = Plus(a_avca_smt, b_avca_smt) 
    return Ite(is_a_U, b_avca_smt,
           Ite(is_b_U, a_avca_smt,
           Ite(LT(dfi_sum_val, Int(current_omega)), dfi_sum_val, AVCA_U_ALG)))

def avca_mul_bc_omega3_algebraic(a_avca_smt: FNode, b_avca_smt: FNode, current_omega: int = 3) -> FNode:
    is_a_U = Equals(a_avca_smt, AVCA_U_ALG)
    is_b_U = Equals(b_avca_smt, AVCA_U_ALG)
    cond1 = Or(is_a_U, is_b_U)
    res1 = AVCA_U_ALG
    cond2 = And(Equals(a_avca_smt, AVCA_DFI1_ALG), Equals(b_avca_smt, AVCA_DFI1_ALG))
    res2 = AVCA_DFI1_ALG # 1*1=1
    cond3_term1 = And(Equals(a_avca_smt, AVCA_DFI1_ALG), Equals(b_avca_smt, AVCA_DFI2_ALG))
    cond3_term2 = And(Equals(a_avca_smt, AVCA_DFI2_ALG), Equals(b_avca_smt, AVCA_DFI1_ALG))
    cond3 = Or(cond3_term1, cond3_term2)
    res3 = AVCA_DFI2_ALG # 1*2=2 or 2*1=2
    # Default is res4 (2*2=4 -> U for Omega=3)
    res4 = AVCA_U_ALG 
    return Ite(cond1, res1, Ite(cond2, res2, Ite(cond3, res3, res4)))

# --- AVCA Aspect Determination ("Unified Tagged-DFI MAX/OR Model") ---
def determine_avca_effective_aspects(
    op_char: Literal["add", "mul"],
    s_ord_input1_smt: FNode, # Original S_ord input 1
    s_ord_input2_smt: FNode, # Original S_ord input 2
    current_omega: int = 3
) -> Tuple[FNode, FNode]: # Returns (effective_aspect_pi_s1, effective_aspect_pi_s2)
    
    pi_s1_alg = pi_algebraic(s_ord_input1_smt)
    pi_s2_alg = pi_algebraic(s_ord_input2_smt)

    aspect_s1_inherent = pi_aspect_inherent(s_ord_input1_smt)
    aspect_s2_inherent = pi_aspect_inherent(s_ord_input2_smt)

    # Default effective aspect: inherent S_ord aspect if ZU/AU, else considered Z_ASPECT for DFI interaction with U.
    eff_aspect_s1 = Ite(Equals(aspect_s1_inherent, SEM_DFI_ASPECT), SEM_ZERO_ASPECT, aspect_s1_inherent)
    eff_aspect_s2 = Ite(Equals(aspect_s2_inherent, SEM_DFI_ASPECT), SEM_ZERO_ASPECT, aspect_s2_inherent)

    # P2 Override: DFI-Driven Saturation implies Areo-tagging for the DFI inputs to AVCA MAX/OR
    is_pi_s1_dfi = Not(Equals(pi_s1_alg, AVCA_U_ALG))
    is_pi_s2_dfi = Not(Equals(pi_s2_alg, AVCA_U_ALG))
    is_dfi_dfi_avca_interaction = And(is_pi_s1_dfi, is_pi_s2_dfi)
    
    dfi_dfi_op_causes_saturation_avca = FALSE() # Default to no saturation override
    if op_char == "add":
        classical_sum_avca = Plus(pi_s1_alg, pi_s2_alg) 
        dfi_dfi_op_causes_saturation_avca = GE(classical_sum_avca, Int(current_omega))
    elif op_char == "mul":
        # Only check product if both are DFI. Otherwise, U is annihilator, aspect logic for U@DFI is simpler.
        # If a_avca_smt and b_avca_smt are the algebraic values:
        # This logic assumes that if it's DFI*DFI, then pi_s1_alg and pi_s2_alg are DFI values > 0
        classical_prod_avca = Times(pi_s1_alg, pi_s2_alg) 
        dfi_dfi_op_causes_saturation_avca = GE(classical_prod_avca, Int(current_omega))
        # (Note: also includes DFI/ZU -> AU, but div not directly in this test's MAX/OR part)

    eff_aspect_s1 = Ite(And(is_dfi_dfi_avca_interaction, dfi_dfi_op_causes_saturation_avca), 
                        SEM_AREO_ASPECT, eff_aspect_s1)
    eff_aspect_s2 = Ite(And(is_dfi_dfi_avca_interaction, dfi_dfi_op_causes_saturation_avca), 
                        SEM_AREO_ASPECT, eff_aspect_s2)
    
    return eff_aspect_s1, eff_aspect_s2

def get_avca_result_aspect(
    algebraic_result_avca_smt: FNode, # AVCA S_Omega algebraic result
    effective_aspect_pi_s1_smt: FNode, 
    effective_aspect_pi_s2_smt: FNode
) -> FNode: # Returns SEM_ZERO_ASPECT, SEM_AREO_ASPECT, or SEM_DFI_ASPECT
    
    is_result_avca_unio = Equals(algebraic_result_avca_smt, AVCA_U_ALG)
    
    # MAX/OR logic for aspect if result is Unio: Areo (1) dominates Zero (0)
    result_aspect_if_unio_is_areo = Or(Equals(effective_aspect_pi_s1_smt, SEM_AREO_ASPECT), 
                                       Equals(effective_aspect_pi_s2_smt, SEM_AREO_ASPECT))
    
    return Ite(is_result_avca_unio,
               Ite(result_aspect_if_unio_is_areo, SEM_AREO_ASPECT, SEM_ZERO_ASPECT),
               SEM_DFI_ASPECT)


def run_B3_aspect_homomorphism_test(
    omega_val: int, 
    # INPUT LUB/GLB tables from a SUCCESSFUL B2 run (Python dicts mapping (int,int)->int)
    s_ord_join_py_table: Dict[Tuple[int,int],int], 
    s_ord_meet_py_table: Dict[Tuple[int,int],int], 
    po_name: str
):
    if omega_val != 3: # This script is hardcoded for S_ord of size 4
        print(f"ERROR: This script version is currently tuned for Ω=3 (S_ord size 4). Cannot run for Ω={omega_val}.")
        return

    print(f"\n====== SCRIPT: Test_B3_SL_Aspect_Homomorphism_Omega3 (Ω={omega_val}) ======")
    print(f"Purpose: Given S_ord lattice tables for PO '{po_name}', test aspect homomorphism.")
    print("Expected: SAT if homomorphism holds for aspects.\n")

    assertions = []

    # Define S_ord join/meet SMT functions based on input Python tables
    s_ord_op_func_type = FunctionType(SMT_INT_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    s_ord_join_op = Symbol("s_ord_join_func", s_ord_op_func_type)
    s_ord_meet_op = Symbol("s_ord_meet_func", s_ord_op_func_type)

    print(f"--- Defining S_ord join/meet SMT functions from input tables for PO '{po_name}' ---")
    for x_py_key in S_ORD_PY_KEYS:
        x_smt = Int(x_py_key)
        for y_py_key in S_ORD_PY_KEYS:
            y_smt = Int(y_py_key)
            
            join_res_py = s_ord_join_py_table.get((x_py_key, y_py_key))
            meet_res_py = s_ord_meet_py_table.get((x_py_key, y_py_key))
            if join_res_py is None or meet_res_py is None:
                print(f"CRITICAL ERROR: Missing entry in input S_ord operation tables for ({x_py_key},{y_py_key}) for PO '{po_name}'.")
                return
            assertions.append(Equals(s_ord_join_op(x_smt, y_smt), Int(join_res_py)))
            assertions.append(Equals(s_ord_meet_op(x_smt, y_smt), Int(meet_res_py)))

    print(f"\n--- Asserting Homomorphism for Aspects (Ω={omega_val}) ---")
    all_homomorphisms_hold_smt_conjuncts: List[FNode] = []

    for x_s_ord_smt in SMT_S_ORD_ELEMENTS: 
        for y_s_ord_smt in SMT_S_ORD_ELEMENTS:
            # --- For Addition (⊕̄ = S_ord join) ---
            res_s_ord_add = s_ord_join_op(x_s_ord_smt, y_s_ord_smt)
            # LHS aspect: inherent aspect of the S_ord join result
            lhs_aspect_add = pi_aspect_inherent(res_s_ord_add) 

            # RHS aspect: aspect of (π(x̄) ⊕_AVCA π(ȳ)) using Unified Tagged-DFI MAX/OR
            pi_x_avca_alg = pi_algebraic(x_s_ord_smt)
            pi_y_avca_alg = pi_algebraic(y_s_ord_smt)
            
            eff_aspect_pi_x_add, eff_aspect_pi_y_add = determine_avca_effective_aspects(
                "add", x_s_ord_smt, y_s_ord_smt, current_omega=omega_val
            )
            
            res_avca_alg_add = avca_add_bc_omega3_algebraic(pi_x_avca_alg, pi_y_avca_alg, omega_val)
            rhs_aspect_add = get_avca_result_aspect(res_avca_alg_add, 
                                                    eff_aspect_pi_x_add, eff_aspect_pi_y_add)
            
            all_homomorphisms_hold_smt_conjuncts.append(Equals(lhs_aspect_add, rhs_aspect_add))

            # --- For Multiplication (⊗̄ = S_ord meet) ---
            res_s_ord_mul = s_ord_meet_op(x_s_ord_smt, y_s_ord_smt)
            lhs_aspect_mul = pi_aspect_inherent(res_s_ord_mul)

            eff_aspect_pi_x_mul, eff_aspect_pi_y_mul = determine_avca_effective_aspects(
                "mul", x_s_ord_smt, y_s_ord_smt, current_omega=omega_val
            )

            res_avca_alg_mul = avca_mul_bc_omega3_algebraic(pi_x_avca_alg, pi_y_avca_alg, omega_val)
            rhs_aspect_mul = get_avca_result_aspect(res_avca_alg_mul,
                                                    eff_aspect_pi_x_mul, eff_aspect_pi_y_mul)

            all_homomorphisms_hold_smt_conjuncts.append(Equals(lhs_aspect_mul, rhs_aspect_mul))

    assertions.append(And(all_homomorphisms_hold_smt_conjuncts))

    print("\n--- Solving with SMT (Z3) ---")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Test B3 (Aspect Homomorphism for PO '{po_name}', Ω={omega_val}): {'SAT' if result else 'UNSAT'}")

        if result:
            print(f"  INTERPRETATION: SAT means the provided S_ord lattice join/meet operations, under quotient π,")
            print("                  CORRECTLY reproduce AVCA-Ω's aspect outcomes (as per Unified Tagged-DFI model).")
            print(f"  This STRONGLY SUPPORTS C-2 for this S_ord lattice candidate '{po_name}'.")
        else: 
            print(f"  INTERPRETATION: UNSAT means the aspect homomorphism FAILED for this S_ord lattice.")
            print(f"                  The aspect outcomes from π(join/meet) do not match AVCA's aspect logic.")
            print(f"                  This candidate S_ord lattice for C-2 (PO '{po_name}') is falsified regarding aspect homomorphism.")

    print(f"\n====== Test_B3_SL_Aspect_Homomorphism_Omega3 (Ω={omega_val}, PO='{po_name}') Finished ======")

if __name__ == "__main__":
    print("NOTE: This script REQUIRES valid join/meet tables from a SUCCESSFUL B2 SMT run")
    print("      (i.e., from an S_ord PO that was proven to be a distributive lattice).")
    print("      The example tables below are HYPOTHETICAL and derived from a simple")
    print("      diamond lattice DFI1s<AUs, DFI2s<AUs, ZUs<DFI1s, ZUs<DFI2s, where ZUs is bottom, AUs is top.")
    print("      User MUST replace these with actual tables from their B2 SMT model output.\n")
    
    hypothetical_po_name = "Hypothetical_Diamond_Lattice_ZUs_Bottom_AUs_Top"
    # S_ord: DFI1s=0, DFI2s=1, ZUs=2 (Bottom), AUs=3 (Top)
    # PO Example: ZUs < DFI1s < AUs, ZUs < DFI2s < AUs. (DFI1s, DFI2s incomparable above ZUs, meet at ZUs, join at AUs)
    
    # For this Diamond: LUB (join) and GLB (meet)
    # Elements: DFI1s (0), DFI2s (1), ZUs (2), AUs (3)
    # ZUs is ⊥, AUs is ⊤
    # DFI1s and DFI2s are between ZUs and AUs, and incomparable.
    # x ∨ y:
    # ZUs ∨ x = x
    # AUs ∨ x = AUs
    # DFI1s ∨ DFI1s = DFI1s
    # DFI1s ∨ DFI2s = AUs (their LUB in this diamond)
    # DFI1s ∨ ZUs = DFI1s
    # DFI1s ∨ AUs = AUs
    
    example_join_table_diamond = { 
        #       DFI1s(0) DFI2s(1)  ZUs(2)  AUs(3)
        (0,0):0, (0,1):3,   (0,2):0,   (0,3):3,  # DFI1s join X
        (1,0):3, (1,1):1,   (1,2):1,   (1,3):3,  # DFI2s join X
        (2,0):0, (2,1):1,   (2,2):2,   (2,3):3,  # ZUs   join X 
        (3,0):3, (3,1):3,   (3,2):3,   (3,3):3   # AUs   join X 
    }
    # x ∧ y:
    # ZUs ∧ x = ZUs
    # AUs ∧ x = x
    # DFI1s ∧ DFI1s = DFI1s
    # DFI1s ∧ DFI2s = ZUs (their GLB in this diamond)
    example_meet_table_diamond = { 
        #       DFI1s(0) DFI2s(1)  ZUs(2)  AUs(3)
        (0,0):0, (0,1):2,   (0,2):2,   (0,3):0,  # DFI1s meet X
        (1,0):2, (1,1):1,   (1,2):2,   (1,3):1,  # DFI2s meet X
        (2,0):2, (2,1):2,   (2,2):2,   (2,3):2,  # ZUs   meet X 
        (3,0):0, (3,1):1,   (3,2):2,   (3,3):3   # AUs   meet X 
    }
    
    run_B3_aspect_homomorphism_test(
        omega_val=3, 
        s_ord_join_py_table=example_join_table_diamond,
        s_ord_meet_py_table=example_meet_table_diamond,
        po_name=hypothetical_po_name
    )