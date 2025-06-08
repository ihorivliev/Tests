from pysmt.shortcuts import (Symbol, And, Or, Implies, Solver, Equals, Not, Int, Plus, Ite,
                             TRUE, FALSE, GE, LE, ForAll, Exists) # ToInt removed, Ite is present
from pysmt.typing import BOOL as SMT_BOOL_TYPE, INT as SMT_INT_TYPE, FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Optional

# --- Configuration & AVCA Definitions ---
OMEGA_VAL = 3; U_ALG = 0; DFI1_ALG = 1; DFI2_ALG = 2
S_alg_py = [U_ALG, DFI1_ALG, DFI2_ALG] # Algebraic elements for AVCA ops

DFI1_ORD = 1 
DFI2_ORD = 2
ZU_ORD = 3 
AU_ORD = 4 
S_ord_py = [DFI1_ORD, DFI2_ORD, ZU_ORD, AU_ORD] # Semantic elements for ordering
S_ord_smt = [Int(i) for i in S_ord_py]

Z_ASPECT_VAL = 0; A_ASPECT_VAL = 1
DFI_EFF_ASPECT_FOR_OR_DEFAULT_VAL = Z_ASPECT_VAL
DFI_EFF_ASPECT_FOR_OR_SATURATION_DRIVER_VAL = A_ASPECT_VAL

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

# --- Aspect Determination & Mapping (from previous successful scripts) ---
def aspect_OR_on_values(eff_asp1_val: int, eff_asp2_val: int) -> int:
    return A_ASPECT_VAL if eff_asp1_val == A_ASPECT_VAL or eff_asp2_val == A_ASPECT_VAL else Z_ASPECT_VAL

def get_effective_input_aspect(operand_alg: int, operand_input_aspect_val: int, 
                               is_dfi_saturation_driver_context: bool) -> int:
    if operand_alg != U_ALG: # DFI
        return DFI_EFF_ASPECT_FOR_OR_SATURATION_DRIVER_VAL if is_dfi_saturation_driver_context else DFI_EFF_ASPECT_FOR_OR_DEFAULT_VAL
    return operand_input_aspect_val

def determine_output_aspect_val(op_name: str, a_alg: int, b_alg: int, result_alg: int,
                                a_input_aspect_val: int = Z_ASPECT_VAL, 
                                b_input_aspect_val: int = Z_ASPECT_VAL) -> int:
    if result_alg != U_ALG: return -1 
    dfi_driven_saturation = False
    if a_alg != U_ALG and b_alg != U_ALG: 
        if op_name == "add" and (a_alg + b_alg >= OMEGA_VAL): dfi_driven_saturation = True
        if op_name == "mul" and (a_alg * b_alg >= OMEGA_VAL): dfi_driven_saturation = True
        # Division DFI/DFI overflow not explicitly tested here but logic would be similar
    elif op_name == "div_placeholder" and a_alg != U_ALG and b_alg == U_ALG and b_input_aspect_val == Z_ASPECT_VAL: # DFI / ZU
        dfi_driven_saturation = True # Placeholder for division aspect logic
    if dfi_driven_saturation: return A_ASPECT_VAL
    
    eff_a_asp = get_effective_input_aspect(a_alg, a_input_aspect_val, False)
    eff_b_asp = get_effective_input_aspect(b_alg, b_input_aspect_val, False)
    
    if op_name == "div_placeholder" and a_alg == U_ALG and b_alg == U_ALG: # AltD U/U for division
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
    raise ValueError(f"Cannot map algebraic value {alg_val}")

def print_model_order(model: Dict, le_vars: Dict[Tuple[int,int],FNode], s_ord_keys: List[int]):
    print("    Discovered Partial Order le(x,y) [x <= y]:")
    ord_map_to_name = {DFI1_ORD: "DFI1s", DFI2_ORD: "DFI2s", ZU_ORD: "ZUs", AU_ORD: "AUs"}
    for i_o in s_ord_keys:
        related_to_i_list_names = []
        for j_o in s_ord_keys:
            le_var = le_vars.get((i_o,j_o))
            if le_var and model.get_value(le_var).is_true(): 
                related_to_i_list_names.append(ord_map_to_name.get(j_o, str(j_o)))
        related_to_i_list_names.sort() 
        print(f"      {ord_map_to_name.get(i_o, str(i_o)):<7} <= {related_to_i_list_names}")

# --- Main Lattice Check Function ---
def run_split_unio_lattice_check(
    candidate_order_true_edges: List[Tuple[int,int]], 
    ops_to_test_str_list: List[str] = ["add", "mul"] 
    ):
    omega_alg = 3 
    print(f"\n--- split_unio_order_lattice_check.py (Omega_alg={omega_alg}) ---")
    print(f"    Testing candidate order defined by TRUE non-reflexive edges: {candidate_order_true_edges}")
    print(f"    Checking if it's a lattice and if AVCA ops {ops_to_test_str_list} are join/meet.")

    le_split_vars: Dict[Tuple[int,int], FNode] = {}
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            le_split_vars[(i_o,j_o)] = Symbol(f"leS_{i_o}_{j_o}_lat", SMT_BOOL_TYPE)

    s = Solver(name="z3", logic="QF_LIA") 
    order_assertions = []

    # 1. Assert the candidate partial order
    for i_o in S_ord_py: 
        order_assertions.append(le_split_vars[(i_o,i_o)]) # Reflexivity
        for j_o in S_ord_py:
            if i_o == j_o: continue
            if (i_o, j_o) in candidate_order_true_edges:
                order_assertions.append(le_split_vars[(i_o,j_o)])
            else: 
                order_assertions.append(Not(le_split_vars[(i_o,j_o)]))
    
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            if i_o != j_o: 
                order_assertions.append(Implies(And(le_split_vars[(i_o,j_o)], le_split_vars[(j_o,i_o)]), FALSE()))
            for k_o in S_ord_py: 
                order_assertions.append(Implies(And(le_split_vars[(i_o,j_o)], le_split_vars[(j_o,k_o)]), le_split_vars[(i_o,k_o)]))
    s.add_assertions(order_assertions)
    
    print("  Checking consistency of defined candidate partial order...")
    if not s.solve():
        print("    UNSAT: The candidate EDGES are inconsistent with Partial Order axioms. Halting.")
        return
    print("    Candidate order is consistent with PO axioms.")
    
    join_vars: Dict[Tuple[int,int], FNode] = {}
    meet_vars: Dict[Tuple[int,int], FNode] = {}
    lattice_prop_assertions = []

    for a_o in S_ord_py:
        for b_o in S_ord_py:
            j_var = Symbol(f"join_{a_o}_{b_o}", SMT_INT_TYPE)
            join_vars[(a_o,b_o)] = j_var
            lattice_prop_assertions.append(Or([Equals(j_var, Int(s_el)) for s_el in S_ord_py])) 
            # LUB Property 1: j is an upper bound of a and b
            lattice_prop_assertions.append(Or([And(Equals(j_var, Int(k_ub)), le_split_vars[(a_o, k_ub)]) for k_ub in S_ord_py]))
            lattice_prop_assertions.append(Or([And(Equals(j_var, Int(k_ub)), le_split_vars[(b_o, k_ub)]) for k_ub in S_ord_py]))
            # LUB Property 2: j is the *least* of the upper bounds
            # Forall z in S_ord: (a_o <= z AND b_o <= z) => j_var <= z
            lub_min_clauses_for_pair = []
            for z_o in S_ord_py:
                prem_z_is_upper_bound = And(le_split_vars[(a_o,z_o)], le_split_vars[(b_o,z_o)])
                # cons_j_le_z must be true if j_var takes value k, then le_split_vars[(k, z_o)] is true
                cons_j_le_z_clauses = []
                for k_j_val in S_ord_py:
                    cons_j_le_z_clauses.append(Implies(Equals(j_var, Int(k_j_val)), le_split_vars[(k_j_val, z_o)]))
                lub_min_clauses_for_pair.append(Implies(prem_z_is_upper_bound, And(cons_j_le_z_clauses)))
            lattice_prop_assertions.append(And(lub_min_clauses_for_pair))

            m_var = Symbol(f"meet_{a_o}_{b_o}", SMT_INT_TYPE)
            meet_vars[(a_o,b_o)] = m_var
            lattice_prop_assertions.append(Or([Equals(m_var, Int(s_el)) for s_el in S_ord_py]))
            # GLB Property 1: m is a lower bound
            lattice_prop_assertions.append(Or([And(Equals(m_var, Int(k_lb)), le_split_vars[(k_lb, a_o)]) for k_lb in S_ord_py]))
            lattice_prop_assertions.append(Or([And(Equals(m_var, Int(k_lb)), le_split_vars[(k_lb, b_o)]) for k_lb in S_ord_py]))
            # GLB Property 2: m is the *greatest* of the lower bounds
            # Forall z in S_ord: (z <= a_o AND z <= b_o) => z <= m_var
            glb_max_clauses_for_pair = []
            for z_o in S_ord_py:
                prem_z_is_lower_bound = And(le_split_vars[(z_o,a_o)], le_split_vars[(z_o,b_o)])
                cons_z_le_m_clauses = []
                for k_m_val in S_ord_py:
                    cons_z_le_m_clauses.append(Implies(Equals(m_var, Int(k_m_val)), le_split_vars[(z_o, k_m_val)]))
                glb_max_clauses_for_pair.append(Implies(prem_z_is_lower_bound, And(cons_z_le_m_clauses)))
            lattice_prop_assertions.append(And(glb_max_clauses_for_pair))
    
    s.add_assertions(lattice_prop_assertions)
    print(f"  Added {len(lattice_prop_assertions)} assertions to define join/meet variables as LUB/GLB.")
    print("  Checking if the candidate order forms a lattice...")
    
    if not s.solve():
        print("    UNSAT: The candidate order DOES NOT form a lattice. Halting.")
        return
    print("    SAT: The candidate order IS a lattice.")
    model_lattice_vars = s.get_model()

    solved_joins = {}
    solved_meets = {}
    for a_o in S_ord_py:
        for b_o in S_ord_py:
            join_var_node = join_vars.get((a_o,b_o))
            meet_var_node = meet_vars.get((a_o,b_o))
            if join_var_node: solved_joins[(a_o,b_o)] = model_lattice_vars.get_value(join_var_node)
            if meet_var_node: solved_meets[(a_o,b_o)] = model_lattice_vars.get_value(meet_var_node)

    op_match_assertions = []
    for op_name in ops_to_test_str_list:
        current_op_table = avca_add_table_alg_omega3 if op_name == "add" else avca_mul_table_alg_omega3
        is_join_op = True if op_name == "add" else False

        print(f"    Asserting mapped AVCA-{op_name} {'IS join' if is_join_op else 'IS meet'}...")
        for a_alg_py in S_alg_py:
            a_input_aspect = Z_ASPECT_VAL 
            map_a_ord = map_avca_alg_to_ord_id(a_alg_py, op_name, a_alg_py, U_ALG, a_input_aspect, Z_ASPECT_VAL)
            for b_alg_py in S_alg_py:
                b_input_aspect = Z_ASPECT_VAL
                map_b_ord = map_avca_alg_to_ord_id(b_alg_py, op_name, b_alg_py, U_ALG, b_input_aspect, Z_ASPECT_VAL) # CORRECTED TYPO

                res_op_alg = current_op_table[(a_alg_py, b_alg_py)]
                map_res_op_ord_val = map_avca_alg_to_ord_id(res_op_alg, op_name, a_alg_py, b_alg_py, a_input_aspect, b_input_aspect)
                
                target_lattice_op_val_smt = solved_joins.get((map_a_ord, map_b_ord)) if is_join_op else solved_meets.get((map_a_ord, map_b_ord))
                if target_lattice_op_val_smt is not None: # Ensure key exists
                    op_match_assertions.append(Equals(Int(map_res_op_ord_val), target_lattice_op_val_smt))
                else:
                    print(f"Warning: Could not find solved join/meet for ({map_a_ord},{map_b_ord})")

    s.add_assertions(op_match_assertions) 
    print(f"  Added {len(op_match_assertions)} assertions for AVCA ops matching solved join/meet values.")
    
    print("  Solving final combined constraints (Order is Lattice AND AVCA ops are Join/Meet)...")
    if s.solve():
        print("  OVERALL RESULT: SAT!")
        print(f"    SUCCESS: Candidate order IS a lattice, AND mapped AVCA op(s) {ops_to_test_str_list} behave as join/meet.")
    else:
        print("  OVERALL RESULT: UNSAT.")
        print(f"    FAILURE: Candidate order IS a lattice, BUT mapped AVCA op(s) {ops_to_test_str_list} DO NOT behave as join/meet.")

if __name__ == "__main__":
    candidate_edges_2extra = [
        (DFI1_ORD, AU_ORD), 
        (ZU_ORD, AU_ORD)
    ]
    # run_split_unio_lattice_check(candidate_order_true_edges=candidate_edges_2extra, ops_to_test_str_list=["add","mul"])
    
    candidate_edges_1extra = [(DFI2_ORD, AU_ORD)]
    run_split_unio_lattice_check(candidate_order_true_edges=candidate_edges_1extra, ops_to_test_str_list=["add","mul"])

    print("\nINFO: The LUB/GLB SMT constraints in this script are complex and may need further refinement for full generality and efficiency.")
