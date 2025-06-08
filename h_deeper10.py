# Test_B3_SplitUnio_Aspect_Homomorphism_Omega3_v3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             Solver, TRUE, FALSE, Plus, Times, Ite, Function, GE, LT) # Added GE, LT
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable, Literal, Union

# --- Definitions for S_ord (Ω=3) ---
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

# --- Aspect Representation for SMT ---
ZERO_ASPECT_SMT = Int(0) 
AREO_ASPECT_SMT = Int(1) 
DFI_ASPECT_SMT  = Int(2) 

# --- Quotient Map π: S_ord -> S_Ω (algebraic and aspectual) ---
def pi_algebraic(s_ord_element_smt: FNode) -> FNode:
    return Ite(Equals(s_ord_element_smt, DFI1s), AVCA_DFI1_ALG,
           Ite(Equals(s_ord_element_smt, DFI2s), AVCA_DFI2_ALG,
           AVCA_U_ALG)) 

def pi_aspect(s_ord_element_smt: FNode) -> FNode:
    return Ite(Equals(s_ord_element_smt, ZUs), ZERO_ASPECT_SMT,
           Ite(Equals(s_ord_element_smt, AUs), AREO_ASPECT_SMT,
           DFI_ASPECT_SMT))

# --- Standard AVCA Operations (Algebraic Part for S_Ω=3) ---
def avca_add_omega3_algebraic(a_avca_smt: FNode, b_avca_smt: FNode, current_omega: int = 3) -> FNode:
    is_a_U = Equals(a_avca_smt, AVCA_U_ALG)
    is_b_U = Equals(b_avca_smt, AVCA_U_ALG)
    # Ensure DFI inputs are used for sum if not U. Assume they are already in {0,1,2}
    # If a_avca_smt = 0 (U_alg), its value for sum is effectively handled by ITE.
    # If a_avca_smt = 1 or 2 (DFI_alg), it's used directly.
    dfi_sum_val = Plus(a_avca_smt, b_avca_smt) 
    
    return Ite(is_a_U, b_avca_smt,
           Ite(is_b_U, a_avca_smt,
           Ite(LT(dfi_sum_val, Int(current_omega)), dfi_sum_val, AVCA_U_ALG)))

def avca_mul_omega3_algebraic(a_avca_smt: FNode, b_avca_smt: FNode, current_omega: int = 3) -> FNode:
    is_a_U = Equals(a_avca_smt, AVCA_U_ALG)
    is_b_U = Equals(b_avca_smt, AVCA_U_ALG)
    
    # For DFI*DFI product part. We need to ensure we are multiplying DFI values.
    # The inputs a_avca_smt, b_avca_smt are already SMT Ints {0,1,2}.
    # Times(0,X) = 0, Times(X,0)=0.
    # Times(1,1)=1, Times(1,2)=2, Times(2,1)=2, Times(2,2)=4.
    
    # Case 1: Either is U_alg (0) -> result is U_alg (0)
    cond1 = Or(is_a_U, is_b_U)
    res1 = AVCA_U_ALG
    
    # Case 2: a=1, b=1 -> result is 1
    cond2 = And(Equals(a_avca_smt, AVCA_DFI1_ALG), Equals(b_avca_smt, AVCA_DFI1_ALG))
    res2 = AVCA_DFI1_ALG

    # Case 3: (a=1, b=2) or (a=2, b=1) -> result is 2
    cond3_term1 = And(Equals(a_avca_smt, AVCA_DFI1_ALG), Equals(b_avca_smt, AVCA_DFI2_ALG))
    cond3_term2 = And(Equals(a_avca_smt, AVCA_DFI2_ALG), Equals(b_avca_smt, AVCA_DFI1_ALG))
    cond3 = Or(cond3_term1, cond3_term2)
    res3 = AVCA_DFI2_ALG
    
    # Case 4: a=2, b=2 -> result is U_alg (0) (2*2=4 >= Omega=3)
    cond4 = And(Equals(a_avca_smt, AVCA_DFI2_ALG), Equals(b_avca_smt, AVCA_DFI2_ALG))
    res4 = AVCA_U_ALG
    
    return Ite(cond1, res1, Ite(cond2, res2, Ite(cond3, res3, res4)))


# --- AVCA Aspect Determination ("Unified Tagged-DFI MAX/OR Model") ---
def get_avca_operation_aspect(
    op_char: Literal["add", "mul"],
    a_avca_alg_smt: FNode, 
    b_avca_alg_smt: FNode,
    effective_aspect_a_smt: FNode, 
    effective_aspect_b_smt: FNode,
    algebraic_result_avca_smt: FNode 
) -> FNode: 
    
    is_result_unio = Equals(algebraic_result_avca_smt, AVCA_U_ALG)
    result_is_areo_aspected_if_unio = Or(Equals(effective_aspect_a_smt, AREO_ASPECT_SMT), 
                                         Equals(effective_aspect_b_smt, AREO_ASPECT_SMT))
    
    return Ite(is_result_unio,
               Ite(result_is_areo_aspected_if_unio, AREO_ASPECT_SMT, ZERO_ASPECT_SMT),
               DFI_ASPECT_SMT)

def determine_dfi_effective_aspect_for_avca_op(
    op_char: Literal["add", "mul"],
    # These are S_ORD elements (inputs to the S_ord operation)
    s_ord_input1_smt: FNode, 
    s_ord_input2_smt: FNode,
    current_omega: int = 3
) -> Tuple[FNode, FNode]:
    
    pi_s1_alg = pi_algebraic(s_ord_input1_smt)
    pi_s2_alg = pi_algebraic(s_ord_input2_smt)

    aspect_s1_inherent = pi_aspect(s_ord_input1_smt)
    aspect_s2_inherent = pi_aspect(s_ord_input2_smt)

    eff_aspect_s1 = Ite(Equals(aspect_s1_inherent, DFI_ASPECT_SMT), ZERO_ASPECT_SMT, aspect_s1_inherent)
    eff_aspect_s2 = Ite(Equals(aspect_s2_inherent, DFI_ASPECT_SMT), ZERO_ASPECT_SMT, aspect_s2_inherent)

    is_pi_s1_dfi = Not(Equals(pi_s1_alg, AVCA_U_ALG))
    is_pi_s2_dfi = Not(Equals(pi_s2_alg, AVCA_U_ALG))
    is_dfi_dfi_avca_interaction = And(is_pi_s1_dfi, is_pi_s2_dfi)
    
    dfi_dfi_op_causes_saturation = FALSE() # Default
    if op_char == "add":
        # Check for DFI+DFI overflow
        # Need to ensure pi_s1_alg and pi_s2_alg are treated as their DFI int values for sum
        # The Plus operator works directly on SMT Int FNodes.
        classical_sum_avca = Plus(pi_s1_alg, pi_s2_alg) 
        dfi_dfi_op_causes_saturation = GE(classical_sum_avca, Int(current_omega))
    elif op_char == "mul":
        # Check for DFI*DFI overflow
        # This assumes pi_s1_alg, pi_s2_alg correctly represent DFI values 1 or 2 for Omega=3
        # The Times operator works directly on SMT Int FNodes.
        classical_prod_avca = Times(pi_s1_alg, pi_s2_alg) 
        dfi_dfi_op_causes_saturation = GE(classical_prod_avca, Int(current_omega))

    # If it's a DFI-DFI interaction AND it causes saturation, then DFI inputs are Areo-tagged for MAX/OR
    eff_aspect_s1 = Ite(And(is_dfi_dfi_avca_interaction, dfi_dfi_op_causes_saturation), AREO_ASPECT_SMT, eff_aspect_s1)
    eff_aspect_s2 = Ite(And(is_dfi_dfi_avca_interaction, dfi_dfi_op_causes_saturation), AREO_ASPECT_SMT, eff_aspect_s2)
    
    return eff_aspect_s1, eff_aspect_s2


def op_table_to_str_c2_sl(
    op_func_symbol: FNode, 
    model: Solver, 
    op_char: str
) -> str:
    # This function expects op_func_symbol to be an SMT Function Symbol
    s = f"   {op_char}  | " + " | ".join([S_ORD_ELEMENT_MAP[k].center(5) for k in S_ORD_PY_KEYS])
    separator = "-----|-" + "-|-".join(["-----" for _ in S_ORD_PY_KEYS]) + "-|"
    
    lines = [s, separator]
    for r_key in S_ORD_PY_KEYS:
        r_smt = Int(r_key) # Get SMT Int FNode for the row key
        row_str = f"{S_ORD_ELEMENT_MAP[r_key]:<5}| " 
        for c_key in S_ORD_PY_KEYS:
            c_smt = Int(c_key) # Get SMT Int FNode for the column key
            op_call_result_fnode = op_func_symbol(r_smt, c_smt) 
            val_fnode_in_model = model.get_value(op_call_result_fnode)
            row_str += f"{S_ORD_ELEMENT_MAP[val_fnode_in_model.constant_value()].center(5)}| "
        lines.append(row_str)
    return "\n".join(lines)

def run_B3_aspect_homomorphism_test(
    omega_val: int, 
    s_ord_join_py_table: Dict[Tuple[int,int],int], 
    s_ord_meet_py_table: Dict[Tuple[int,int],int], 
    po_name: str
):
    if omega_val != 3:
        print(f"ERROR: This script version is currently hardcoded for Ω=3. Cannot run for Ω={omega_val}.")
        return

    print(f"\n====== SCRIPT: Test_B3_SplitUnio_Aspect_Homomorphism_Omega3_v3.py (Ω={omega_val}) ======")
    print(f"Purpose: Given distributive lattice tables (join/meet) on S_ord for PO '{po_name}',")
    print("         test if quotient map π is a homomorphism for aspects with AVCA ops.")
    print("Expected: SAT if homomorphism holds for aspects.\n")

    assertions = []

    s_ord_join_func_type = FunctionType(SMT_INT_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    s_ord_meet_func_type = FunctionType(SMT_INT_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    s_ord_join_op = Symbol("s_ord_join", s_ord_join_func_type)
    s_ord_meet_op = Symbol("s_ord_meet", s_ord_meet_func_type)

    print(f"--- Defining S_ord join/meet ops from provided tables for PO '{po_name}' ---")
    for x_py_key in S_ORD_PY_KEYS:
        x_smt = Int(x_py_key)
        for y_py_key in S_ORD_PY_KEYS:
            y_smt = Int(y_py_key)
            join_result_py = s_ord_join_py_table.get((x_py_key, y_py_key))
            meet_result_py = s_ord_meet_py_table.get((x_py_key, y_py_key))
            if join_result_py is None or meet_result_py is None:
                print(f"ERROR: Missing entry in input tables for ({x_py_key},{y_py_key})")
                return
            assertions.append(Equals(s_ord_join_op(x_smt, y_smt), Int(join_result_py)))
            assertions.append(Equals(s_ord_meet_op(x_smt, y_smt), Int(meet_result_py)))

    print(f"\n--- Asserting Homomorphism for Aspects (Ω={omega_val}) ---")
    all_homomorphisms_hold_smt_conjuncts: List[FNode] = []

    for x_s_ord_smt_loop in SMT_S_ORD_ELEMENTS: 
        for y_s_ord_smt_loop in SMT_S_ORD_ELEMENTS:
            # --- For Addition (⊕̄ = S_ord join) ---
            res_s_ord_add = s_ord_join_op(x_s_ord_smt_loop, y_s_ord_smt_loop)
            lhs_aspect_add = pi_aspect(res_s_ord_add) 

            pi_x_avca_alg = pi_algebraic(x_s_ord_smt_loop)
            pi_y_avca_alg = pi_algebraic(y_s_ord_smt_loop)
            
            eff_aspect_pi_x_add, eff_aspect_pi_y_add = determine_dfi_effective_aspect_for_avca_op(
                "add", x_s_ord_smt_loop, y_s_ord_smt_loop, 
                current_omega=omega_val
            )
            
            res_avca_alg_add = avca_add_omega3_algebraic(pi_x_avca_alg, pi_y_avca_alg, omega_val)
            rhs_aspect_add = get_avca_operation_aspect("add", 
                                                       pi_x_avca_alg, pi_y_avca_alg, # Pass algebraic AVCA inputs
                                                       eff_aspect_pi_x_add, eff_aspect_pi_y_add, 
                                                       res_avca_alg_add)
            
            all_homomorphisms_hold_smt_conjuncts.append(Equals(lhs_aspect_add, rhs_aspect_add))

            # --- For Multiplication (⊗̄ = S_ord meet) ---
            res_s_ord_mul = s_ord_meet_op(x_s_ord_smt_loop, y_s_ord_smt_loop)
            lhs_aspect_mul = pi_aspect(res_s_ord_mul)

            eff_aspect_pi_x_mul, eff_aspect_pi_y_mul = determine_dfi_effective_aspect_for_avca_op(
                "mul", x_s_ord_smt_loop, y_s_ord_smt_loop,
                current_omega=omega_val
            )

            res_avca_alg_mul = avca_mul_omega3_algebraic(pi_x_avca_alg, pi_y_avca_alg, omega_val)
            rhs_aspect_mul = get_avca_operation_aspect("mul", 
                                                       pi_x_avca_alg, pi_y_avca_alg, # Pass algebraic AVCA inputs
                                                       eff_aspect_pi_x_mul, eff_aspect_pi_y_mul,
                                                       res_avca_alg_mul)

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

    print(f"\n====== Test_B3_SplitUnio_Aspect_Homomorphism_Omega3_v3.py (Ω={omega_val}, PO='{po_name}') Finished ======")


if __name__ == "__main__":
    print("NOTE: This script REQUIRES valid join/meet tables from a SUCCESSFUL B2 run")
    print("      (i.e., from an S_ord PO that was proven to be a distributive lattice).")
    print("      The example tables below are HYPOTHETICAL and may not correspond to a real lattice.")
    print("      User MUST replace these with actual tables from their B2 SMT model output.\n")
    
    hypothetical_po_name = "Hypothetical_Diamond_Lattice_S_ord"
    # S_ord: DFI1s=0, DFI2s=1, ZUs=2 (Bottom), AUs=3 (Top)
    # Order example: ZUs < DFI1s < AUs, ZUs < DFI2s < AUs. (DFI1s, DFI2s incomparable)
    
    example_join_table = {
        (0,0):0, (0,1):3, (0,2):0, (0,3):3,  
        (1,0):3, (1,1):1, (1,2):1, (1,3):3,  
        (2,0):0, (2,1):1, (2,2):2, (2,3):3,  
        (3,0):3, (3,1):3, (3,2):3, (3,3):3   
    }
    example_meet_table = {
        (0,0):0, (0,1):2, (0,2):2, (0,3):0,  
        (1,0):2, (1,1):1, (1,2):2, (1,3):1,  
        (2,0):2, (2,1):2, (2,2):2, (2,3):2,  
        (3,0):0, (3,1):1, (3,2):2, (3,3):3   
    }
    
    run_B3_aspect_homomorphism_test(
        omega_val=3, 
        s_ord_join_py_table=example_join_table,
        s_ord_meet_py_table=example_meet_table,
        po_name=hypothetical_po_name
    )