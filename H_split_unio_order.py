from pysmt.shortcuts import (Symbol, And, Or, Implies, Solver, Equals, Not, Int, Plus, # ToInt removed
                             TRUE, FALSE, GE, LE, Ite) # Added Ite
from pysmt.typing import BOOL as SMT_BOOL_TYPE, INT as SMT_INT_TYPE, FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable

# --- Configuration ---
OMEGA_VAL = 3
U_ALG = 0     # Algebraic Unio
DFI1_ALG = 1
DFI2_ALG = 2
S_alg_py = [U_ALG, DFI1_ALG, DFI2_ALG] # Elements for AVCA operations

# Semantic representations for ordering space S_ord
DFI1_ORD = 1 
DFI2_ORD = 2
ZU_ORD = 3 # Represents algebraic U with Zero aspect for ordering
AU_ORD = 4 # Represents algebraic U with Areo aspect for ordering
S_ord_py = [DFI1_ORD, DFI2_ORD, ZU_ORD, AU_ORD] 
# Note: U_ALG (0) is not directly in S_ord_py; it's mapped to ZU_ORD or AU_ORD.

# Aspect values for internal logic
Z_ASPECT_VAL = 0
A_ASPECT_VAL = 1
DFI_EFF_ASPECT_FOR_OR_VAL_DEFAULT = Z_ASPECT_VAL 
DFI_EFF_ASPECT_FOR_OR_VAL_SATURATION_DRIVER = A_ASPECT_VAL 

# Standard AVCA operation tables for Omega=3 (outputs are algebraic: 0,1,2)
avca_add_table_alg_omega3 = {
    (U_ALG,U_ALG):U_ALG, (U_ALG,DFI1_ALG):DFI1_ALG, (U_ALG,DFI2_ALG):DFI2_ALG,
    (DFI1_ALG,U_ALG):DFI1_ALG, (DFI1_ALG,DFI1_ALG):DFI2_ALG, (DFI1_ALG,DFI2_ALG):U_ALG,
    (DFI2_ALG,U_ALG):DFI2_ALG, (DFI2_ALG,DFI1_ALG):U_ALG, (DFI2_ALG,DFI2_ALG):U_ALG
}
avca_mul_table_alg_omega3 = { # avc_mul_v1.2 logic
    (U_ALG,U_ALG):U_ALG, (U_ALG,DFI1_ALG):U_ALG, (U_ALG,DFI2_ALG):U_ALG,
    (DFI1_ALG,U_ALG):U_ALG, (DFI1_ALG,DFI1_ALG):DFI1_ALG, (DFI1_ALG,DFI2_ALG):DFI2_ALG,
    (DFI2_ALG,U_ALG):U_ALG, (DFI2_ALG,DFI1_ALG):DFI2_ALG, (DFI2_ALG,DFI2_ALG):U_ALG
}

# --- Aspect Determination Logic (Unified Tagged-DFI Model) ---
def aspect_OR_on_values(eff_asp1_val: int, eff_asp2_val: int) -> int:
    """Calculates resulting aspect value using MAX/OR logic on Python ints."""
    return A_ASPECT_VAL if eff_asp1_val == A_ASPECT_VAL or eff_asp2_val == A_ASPECT_VAL else Z_ASPECT_VAL

def get_effective_input_aspect(operand_alg: int, # Algebraic value U_ALG, DFI1_ALG, DFI2_ALG
                                 input_unio_aspect_val: int, # Z_ASPECT_VAL or A_ASPECT_VAL if operand_alg is U_ALG
                                 is_dfi_saturation_driver: bool) -> int:
    """Determines the effective aspect of an algebraic operand for the OR operation."""
    if operand_alg == U_ALG:
        return input_unio_aspect_val # Use the provided aspect for Unio inputs
    elif is_dfi_saturation_driver:
        return DFI_EFF_ASPECT_FOR_OR_VAL_SATURATION_DRIVER
    else:
        return DFI_EFF_ASPECT_FOR_OR_VAL_DEFAULT

def determine_aspect_of_avca_result(op_name: str, a_alg: int, b_alg: int, result_alg: int,
                                    a_input_aspect_val: int = Z_ASPECT_VAL, # Default input U to ZU
                                    b_input_aspect_val: int = Z_ASPECT_VAL  # Default input U to ZU
                                   ) -> int:
    """
    Determines the SEMANTIC aspect (Z_ASPECT_VAL or A_ASPECT_VAL) of result_alg 
    if result_alg is U_ALG, based on the Unified Tagged-DFI model.
    Returns -1 if result_alg is DFI (aspect not directly relevant for mapping to ZU/AU).
    """
    if result_alg != U_ALG:
        return -1 

    # Determine if this operation is a DFI-driven saturation event
    is_dfi_driven_saturation_event = False
    # Both operands are DFI
    if a_alg != U_ALG and b_alg != U_ALG: 
        if op_name == "add" and (a_alg + b_alg >= OMEGA_VAL): is_dfi_driven_saturation_event = True
        if op_name == "mul" and (a_alg * b_alg >= OMEGA_VAL): is_dfi_driven_saturation_event = True
        if op_name == "div": # DFI/DFI problematic -> U (simplified check)
            if b_alg == U_ALG: # This case should be DFI / U, not DFI/DFI
                 pass # Will be handled by DFI / U logic
            elif b_alg == 0 : # Python int 0, not U_ALG if DFI means positive
                is_dfi_driven_saturation_event = True # Division by actual zero
            else: # b_alg is DFI1_ALG or DFI2_ALG
                # Check if standard AVCA DFI/DFI division for these specific values results in U_ALG
                # This is complex as it requires simulating the div logic.
                # For Omega=3: 1/2 -> U, 2/1 -> 2 (DFI), 1/1->1 (DFI), 2/2->1 (DFI)
                # So only 1/2 -> U for DFI/DFI in Omega=3
                if (a_alg == DFI1_ALG and b_alg == DFI2_ALG) and result_alg == U_ALG : # 1/2 -> U
                    is_dfi_driven_saturation_event = True
    # DFI / ZU (b_alg is U, and its input aspect is ZU)
    elif op_name == "div" and a_alg != U_ALG and b_alg == U_ALG and b_input_aspect_val == Z_ASPECT_VAL:
        is_dfi_driven_saturation_event = True

    # Determine effective aspects for the OR operation
    eff_a_aspect = get_effective_input_aspect(a_alg, a_input_aspect_val, 
                                              is_dfi_driven_saturation_event and a_alg != U_ALG)
    eff_b_aspect = get_effective_input_aspect(b_alg, b_input_aspect_val,
                                              is_dfi_driven_saturation_event and b_alg != U_ALG)
    
    # For U-U operations, the "is_dfi_saturation_driver" is false for both,
    # so get_effective_input_aspect will return their respective a_input_aspect_val, b_input_aspect_val
    
    if is_dfi_driven_saturation_event: # Principle P2: DFI-driven saturation unconditionally yields Areo
        return A_ASPECT_VAL
    else: # Principle P1: Other Unio results determined by MAX/OR of effective input aspects
        # This needs to handle the specific AltD U/U logic if op_name is "div" and a,b are U
        if op_name == "div" and a_alg == U_ALG and b_alg == U_ALG:
            # AltD U/U: if divisor aspect is Areo -> Areo; else (divisor Zero) -> preserve dividend aspect
            return A_ASPECT_VAL if b_input_aspect_val == A_ASPECT_VAL else a_input_aspect_val
        else: # For Add U+U, Mul U@U, Mul U@DFI, Div U/DFI
            return aspect_OR_on_values(eff_a_aspect, eff_b_aspect)


def map_avca_alg_to_ord_space(res_alg: int, op_name: str, a_alg: int, b_alg: int,
                              # Pass input aspects if they are Unio, for determine_aspect_of_avca_result
                              a_input_aspect_val: int = Z_ASPECT_VAL, 
                              b_input_aspect_val: int = Z_ASPECT_VAL) -> int:
    """Maps an algebraic AVCA result to the S_ord space based on its determined aspect."""
    if res_alg == DFI1_ALG: return DFI1_ORD
    if res_alg == DFI2_ALG: return DFI2_ORD
    if res_alg == U_ALG:
        aspect_val = determine_aspect_of_avca_result(op_name, a_alg, b_alg, res_alg, a_input_aspect_val, b_input_aspect_val)
        return AU_ORD if aspect_val == A_ASPECT_VAL else ZU_ORD
    raise ValueError(f"Unknown algebraic result to map: {res_alg}")

def run_split_unio_order_discovery(omega_val_alg: int = 3, 
                                   op_to_test: str = "add", 
                                   min_nontrivial_relations: int = 1):
    print(f"\n--- split_unio_order.py: SMT Search for Monotonic PO on Split-Unio Space (Algorithmic Ω={omega_val_alg}) ---")
    print(f"    Testing {op_to_test}-monotonicity with S_ord = DFI1_ORD({DFI1_ORD}), DFI2_ORD({DFI2_ORD}), ZU_ORD({ZU_ORD}), AU_ORD({AU_ORD}).")
    print(f"    Attempting to find an order with at least {min_nontrivial_relations} non-reflexive true relation(s).")

    if omega_val_alg != 3: print("Warning: AVCA op tables & aspect logic primarily hardcoded for Omega=3.")

    avca_op_table = avca_add_table_alg_omega3 if op_to_test == "add" else avca_mul_table_alg_omega3

    le_split: Dict[Tuple[int,int], FNode] = {}
    for i_o in S_ord_py: 
        for j_o in S_ord_py:
            le_split[(i_o,j_o)] = Symbol(f"leS_{i_o}_{j_o}", SMT_BOOL_TYPE)

    po_axioms_list = []
    for i_o in S_ord_py: po_axioms_list.append(le_split[(i_o,i_o)])
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            if i_o != j_o: po_axioms_list.append(Implies(And(le_split[(i_o,j_o)], le_split[(j_o,i_o)]), FALSE()))
            for k_o in S_ord_py: # Transitivity
                if i_o != k_o : # Avoid trivial Leq(i,i) from Leq(i,j) & Leq(j,i) if i=k
                     po_axioms_list.append(Implies(And(le_split[(i_o,j_o)], le_split[(j_o,k_o)]), le_split[(i_o,k_o)]))
    smt_po_axioms = And(po_axioms_list)
    print(f"Asserted {len(po_axioms_list)} partial order axioms for S_ord.")

    mono_axioms_list = []
    print(f"  Including {op_to_test}-monotonicity constraints for S_ord...")
    
    # Iterate over S_alg_py for a,b,x to define AVCA operations
    # Then map results to S_ord_py for monotonicity check
    for a_alg_input in S_alg_py:
        for b_alg_input in S_alg_py:
            # For premise map_a_ord <= map_b_ord:
            # Assume input U_ALG are ZU_ORD by default for defining the premise order relation
            map_a_ord_premise = ZU_ORD if a_alg_input == U_ALG else (DFI1_ORD if a_alg_input == DFI1_ALG else DFI2_ORD)
            map_b_ord_premise = ZU_ORD if b_alg_input == U_ALG else (DFI1_ORD if b_alg_input == DFI1_ALG else DFI2_ORD)
            premise_leq_ab_ord = le_split[(map_a_ord_premise, map_b_ord_premise)]

            for x_alg_input in S_alg_py:
                map_x_ord_premise = ZU_ORD if x_alg_input == U_ALG else (DFI1_ORD if x_alg_input == DFI1_ALG else DFI2_ORD)

                # x op a
                res_xa_alg = avca_op_table[(x_alg_input, a_alg_input)]
                # Determine aspects of x_alg_input and a_alg_input if they are U_ALG for aspect determination
                x_input_aspect = Z_ASPECT_VAL if x_alg_input == U_ALG else Z_ASPECT_VAL # Defaulting DFI to Z for input to op
                a_input_aspect = Z_ASPECT_VAL if a_alg_input == U_ALG else Z_ASPECT_VAL
                map_res_xa_ord = map_avca_alg_to_ord_space(res_xa_alg, op_to_test, x_alg_input, a_alg_input, x_input_aspect, a_input_aspect)
                
                # x op b
                res_xb_alg = avca_op_table[(x_alg_input, b_alg_input)]
                b_input_aspect = Z_ASPECT_VAL if b_alg_input == U_ALG else Z_ASPECT_VAL
                map_res_xb_ord = map_avca_alg_to_ord_space(res_xb_alg, op_to_test, x_alg_input, b_alg_input, x_input_aspect, b_input_aspect)
                mono_axioms_list.append(Implies(premise_leq_ab_ord, le_split[(map_res_xa_ord, map_res_xb_ord)]))

                # a op x 
                res_ax_alg = avca_op_table[(a_alg_input, x_alg_input)]
                map_res_ax_ord = map_avca_alg_to_ord_space(res_ax_alg, op_to_test, a_alg_input, x_alg_input, a_input_aspect, x_input_aspect)
                
                # b op x
                res_bx_alg = avca_op_table[(b_alg_input, x_alg_input)]
                map_res_bx_ord = map_avca_alg_to_ord_space(res_bx_alg, op_to_test, b_alg_input, x_alg_input, b_input_aspect, x_input_aspect)
                mono_axioms_list.append(Implies(premise_leq_ab_ord, le_split[(map_res_ax_ord, map_res_bx_ord)]))
    
    smt_mono_axioms = And(mono_axioms_list)
    print(f"    Added {len(mono_axioms_list)} {op_to_test}-monotonicity implication clauses for S_ord.")

    non_reflexive_le_split_int_vars = []
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            if i_o != j_o:
                non_reflexive_le_split_int_vars.append(Ite(le_split[(i_o, j_o)], Int(1), Int(0)))
    sum_true_non_reflexive_ord = Plus(non_reflexive_le_split_int_vars) if non_reflexive_le_split_int_vars else Int(0)
    nontriviality_ord_constraint = GE(sum_true_non_reflexive_ord, Int(min_nontrivial_relations))
    print(f"  Adding constraint for at least {min_nontrivial_relations} non-reflexive true relation(s) in S_ord.")

    with Solver(name="z3") as s:
        s.add_assertion(smt_po_axioms)
        s.add_assertion(smt_mono_axioms)
        s.add_assertion(nontriviality_ord_constraint)

        print(f"  Searching for NON-TRIVIAL PO on Split-Unio Space S_ord making {op_to_test} monotone...")
        if s.solve():
            print("  SAT: Found a NON-TRIVIAL partial order on S_ord satisfying monotonicity!")
            model = s.get_model()
            true_non_reflexive_relations_count = 0
            print("    Discovered Partial Order le_split(x,y) [x <= y]:")
            ord_map_to_name = {DFI1_ORD: "DFI1sem", DFI2_ORD: "DFI2sem", ZU_ORD: "ZUsem", AU_ORD: "AUsem"}
            for i_o_model in S_ord_py:
                related_to_i_list_names = []
                for j_o_model in S_ord_py:
                    le_var = le_split.get((i_o_model,j_o_model))
                    if le_var and model.get_value(le_var).is_true(): 
                        related_to_i_list_names.append(ord_map_to_name.get(j_o_model, str(j_o_model)))
                        if i_o_model != j_o_model:
                            true_non_reflexive_relations_count +=1
                related_to_i_list_names.sort() 
                print(f"      {ord_map_to_name.get(i_o_model, str(i_o_model))} <= {related_to_i_list_names}")
            print(f"    Number of true non-reflexive relations in S_ord model: {true_non_reflexive_relations_count}")
        else:
            print(f"  UNSAT: No NON-TRIVIAL PO on S_ord (with >= {min_nontrivial_relations} non-refl rels) makes {op_to_test} monotone.")

if __name__ == "__main__":
    # run_nontrivial_order_discovery_for_mul(omega_val=3, min_nontrivial_relations=1) # Previous script
    
    print("\n--- Running Split-Unio Order Discovery (Test for ADD Monotonicity) ---")
    run_split_unio_order_discovery(omega_val_alg=3, op_to_test="add", min_nontrivial_relations=1)
