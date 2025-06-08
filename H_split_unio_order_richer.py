from pysmt.shortcuts import (Symbol, And, Or, Implies, Solver, Equals, Not, Int, Plus, Ite,
                             TRUE, FALSE, GE, LE) # ToInt removed, Ite is present
from pysmt.typing import BOOL as SMT_BOOL_TYPE, INT as SMT_INT_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Optional

# --- Configuration ---
OMEGA_VAL = 3         # AVCA Algebraic Omega
U_ALG = 0             # Algebraic Unio representation
DFI1_ALG = 1
DFI2_ALG = 2
S_alg_py = [U_ALG, DFI1_ALG, DFI2_ALG]

# Semantic representations for the ordering space S_ord
DFI1_ORD = 1 
DFI2_ORD = 2
ZU_ORD = 3 # Represents algebraic U with Zero aspect for ordering
AU_ORD = 4 # Represents algebraic U with Areo aspect for ordering
S_ord_py = [DFI1_ORD, DFI2_ORD, ZU_ORD, AU_ORD] 
S_ord_smt = [Int(i) for i in S_ord_py]

# Aspect values for internal logic
Z_ASPECT_VAL = 0
A_ASPECT_VAL = 1
DFI_EFF_ASPECT_FOR_OR_DEFAULT_VAL = Z_ASPECT_VAL 
DFI_EFF_ASPECT_FOR_OR_SATURATION_DRIVER_VAL = A_ASPECT_VAL

# Standard AVCA operation tables for Omega=3 (algebraic outputs)
avca_add_table_alg_omega3 = {
    (U_ALG,U_ALG):U_ALG, (U_ALG,DFI1_ALG):DFI1_ALG, (U_ALG,DFI2_ALG):DFI2_ALG,
    (DFI1_ALG,U_ALG):DFI1_ALG, (DFI1_ALG,DFI1_ALG):DFI2_ALG, (DFI1_ALG,DFI2_ALG):U_ALG,
    (DFI2_ALG,U_ALG):DFI2_ALG, (DFI2_ALG,DFI1_ALG):U_ALG, (DFI2_ALG,DFI2_ALG):U_ALG
}
avca_mul_table_alg_omega3 = {
    (U_ALG,U_ALG):U_ALG, (U_ALG,DFI1_ALG):U_ALG, (U_ALG,DFI2_ALG):U_ALG,
    (DFI1_ALG,U_ALG):U_ALG, (DFI1_ALG,DFI1_ALG):DFI1_ALG, (DFI1_ALG,DFI2_ALG):DFI2_ALG,
    (DFI2_ALG,U_ALG):U_ALG, (DFI2_ALG,DFI1_ALG):DFI2_ALG, (DFI2_ALG,DFI2_ALG):U_ALG
}

# --- Aspect Determination Logic (Unified Tagged-DFI Model) ---
def aspect_OR_on_values(eff_asp1_val: int, eff_asp2_val: int) -> int:
    return A_ASPECT_VAL if eff_asp1_val == A_ASPECT_VAL or eff_asp2_val == A_ASPECT_VAL else Z_ASPECT_VAL

def get_effective_input_aspect(operand_alg: int, 
                                 operand_input_aspect_val: int, 
                                 is_dfi_saturation_driver_context: bool) -> int:
    if operand_alg != U_ALG: # It's DFI
        return DFI_EFF_ASPECT_FOR_OR_SATURATION_DRIVER_VAL if is_dfi_saturation_driver_context else DFI_EFF_ASPECT_FOR_OR_DEFAULT_VAL
    return operand_input_aspect_val # For Unio, use its passed aspect

def determine_output_aspect_val(op_name: str, a_alg: int, b_alg: int, result_alg: int,
                                a_input_aspect_val: int = Z_ASPECT_VAL, 
                                b_input_aspect_val: int = Z_ASPECT_VAL
                               ) -> int:
    if result_alg != U_ALG: return -1 

    dfi_driven_saturation = False
    if a_alg != U_ALG and b_alg != U_ALG: 
        if op_name == "add" and (a_alg + b_alg >= OMEGA_VAL): dfi_driven_saturation = True
        if op_name == "mul" and (a_alg * b_alg >= OMEGA_VAL): dfi_driven_saturation = True
        if op_name == "div": 
            if (a_alg == DFI1_ALG and b_alg == DFI2_ALG): dfi_driven_saturation = True
    elif op_name == "div" and a_alg != U_ALG and b_alg == U_ALG and b_input_aspect_val == Z_ASPECT_VAL: 
        dfi_driven_saturation = True
    
    if dfi_driven_saturation:
        return A_ASPECT_VAL

    eff_a_asp = get_effective_input_aspect(a_alg, a_input_aspect_val, False)
    eff_b_asp = get_effective_input_aspect(b_alg, b_input_aspect_val, False)
    
    if op_name == "div" and a_alg == U_ALG and b_alg == U_ALG: 
        return A_ASPECT_VAL if b_input_aspect_val == A_ASPECT_VAL else a_input_aspect_val
    
    return aspect_OR_on_values(eff_a_asp, eff_b_asp)

def map_avca_alg_to_ord_id(alg_val: int, op_name:str, context_a_alg: int, context_b_alg: int,
                            a_input_aspect_val: int = Z_ASPECT_VAL, 
                            b_input_aspect_val: int = Z_ASPECT_VAL) -> int:
    if alg_val == DFI1_ALG: return DFI1_ORD
    if alg_val == DFI2_ALG: return DFI2_ORD
    if alg_val == U_ALG:
        aspect = determine_output_aspect_val(op_name, context_a_alg, context_b_alg, alg_val, a_input_aspect_val, b_input_aspect_val)
        return AU_ORD if aspect == A_ASPECT_VAL else ZU_ORD
    raise ValueError(f"Cannot map algebraic value {alg_val} to S_ord ID")

# --- Main Test Function ---
def run_split_unio_order_richer(test_ops: List[str], min_extra_edges: int):
    omega_alg = 3 
    print(f"\n--- split_unio_order_richer.py (Omega_alg={omega_alg}) ---")
    print(f"    Ops to make monotone: {test_ops}, Min non-reflexive relations: {min_extra_edges}")

    le_split: Dict[Tuple[int,int], FNode] = {}
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            le_split[(i_o,j_o)] = Symbol(f"leS_{i_o}_{j_o}", SMT_BOOL_TYPE)

    po_axioms_list = []
    for i_o in S_ord_py: po_axioms_list.append(le_split[(i_o,i_o)])
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            if i_o != j_o: po_axioms_list.append(Implies(And(le_split[(i_o,j_o)], le_split[(j_o,i_o)]), FALSE()))
            for k_o in S_ord_py:
                po_axioms_list.append(Implies(And(le_split[(i_o,j_o)], le_split[(j_o,k_o)]), le_split[(i_o,k_o)]))
    smt_po_axioms = And(po_axioms_list)

    all_monotonicity_assertions = []
    for op_name_to_test in test_ops:
        current_op_table = avca_add_table_alg_omega3 if op_name_to_test == "add" else avca_mul_table_alg_omega3
        mono_op_axioms_list = []
        for a_alg_py in S_alg_py: 
            a_input_aspect = Z_ASPECT_VAL 
            map_a_ord_premise = map_avca_alg_to_ord_id(a_alg_py, op_name_to_test, a_alg_py, U_ALG, a_input_aspect, Z_ASPECT_VAL) # CORRECTED Function Name

            for b_alg_py in S_alg_py:
                b_input_aspect = Z_ASPECT_VAL
                map_b_ord_premise = map_avca_alg_to_ord_id(b_alg_py, op_name_to_test, b_alg_py, U_ALG, b_input_aspect, Z_ASPECT_VAL) # CORRECTED
                
                premise_leq_ab_ord = le_split[(map_a_ord_premise, map_b_ord_premise)]

                for x_alg_py in S_alg_py:
                    x_input_aspect = Z_ASPECT_VAL
                    
                    res_xa_alg = current_op_table[(x_alg_py, a_alg_py)]
                    map_res_xa_ord = map_avca_alg_to_ord_id(res_xa_alg, op_name_to_test, x_alg_py, a_alg_py, x_input_aspect, a_input_aspect) # CORRECTED
                    
                    res_xb_alg = current_op_table[(x_alg_py, b_alg_py)]
                    map_res_xb_ord = map_avca_alg_to_ord_id(res_xb_alg, op_name_to_test, x_alg_py, b_alg_py, x_input_aspect, b_input_aspect) # CORRECTED
                    mono_op_axioms_list.append(Implies(premise_leq_ab_ord, le_split[(map_res_xa_ord, map_res_xb_ord)]))

                    res_ax_alg = current_op_table[(a_alg_py, x_alg_py)]
                    map_res_ax_ord = map_avca_alg_to_ord_id(res_ax_alg, op_name_to_test, a_alg_py, x_alg_py, a_input_aspect, x_input_aspect) # CORRECTED
                    
                    res_bx_alg = current_op_table[(b_alg_py, x_alg_py)]
                    map_res_bx_ord = map_avca_alg_to_ord_id(res_bx_alg, op_name_to_test, b_alg_py, x_alg_py, b_input_aspect, x_input_aspect) # CORRECTED
                    mono_op_axioms_list.append(Implies(premise_leq_ab_ord, le_split[(map_res_ax_ord, map_res_bx_ord)]))
        
        all_monotonicity_assertions.append(And(mono_op_axioms_list))
    smt_mono_axioms = And(all_monotonicity_assertions) if all_monotonicity_assertions else TRUE()
    
    non_reflexive_le_int_vars = []
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            if i_o != j_o:
                non_reflexive_le_int_vars.append(Ite(le_split[(i_o, j_o)], Int(1), Int(0))) # CORRECTED ToInt
    sum_true_non_reflexive_ord = Plus(non_reflexive_le_int_vars) if non_reflexive_le_int_vars else Int(0)
    nontriviality_ord_constraint = GE(sum_true_non_reflexive_ord, Int(min_extra_edges))

    with Solver(name="z3", logic="QF_LIA") as s: 
        s.add_assertion(smt_po_axioms)
        s.add_assertion(smt_mono_axioms)
        s.add_assertion(nontriviality_ord_constraint)

        print(f"  ► Solving for ≥{min_extra_edges} extra edges, ops={test_ops} …")
        if s.solve():
            print("      SAT ✓")
            model = s.get_model()
            true_non_reflexive_relations_count = 0
            print("      Discovered Partial Order le_split(x,y) [x <= y]:")
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
                print(f"        {ord_map_to_name.get(i_o_model, str(i_o_model)):<8} <= {related_to_i_list_names}")
            print(f"      Number of true non-reflexive relations in S_ord model: {true_non_reflexive_relations_count}")
        else:
            print("      UNSAT ✗")

if __name__ == "__main__":
    # from pysmt.typing import FunctionType # Not strictly needed as Leq is not used as UF in this script's main logic
                                        # le_split is a dict of Boolean SMT Symbols

    run_split_unio_order_richer(test_ops=["add"], min_extra_edges=1)
    
    print("\nAttempting richer order for ⊕-monotonicity:")
    run_split_unio_order_richer(test_ops=["add"], min_extra_edges=2)
    run_split_unio_order_richer(test_ops=["add"], min_extra_edges=3)

    print("\nAttempting non-trivial order for ⊗-monotonicity:")
    run_split_unio_order_richer(test_ops=["mul"], min_extra_edges=1)

    print("\nAttempting common non-trivial order for both ⊕ and ⊗ monotonicity:")
    run_split_unio_order_richer(test_ops=["add", "mul"], min_extra_edges=1)
