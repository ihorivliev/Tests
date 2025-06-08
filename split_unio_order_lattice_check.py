from pysmt.shortcuts import (Symbol, And, Or, Implies, Solver, Equals, Not, Int, Plus, Ite,
                             TRUE, FALSE, GE, LE, ForAll, Exists)
from pysmt.typing import BOOL as SMT_BOOL_TYPE, INT as SMT_INT_TYPE
from pysmt.fnode import FNode # Corrected: FNode was missing from imports in some earlier versions
from typing import List, Dict, Tuple, Optional

# --- Configuration & AVCA Definitions ---
OMEGA_VAL = 3; U_ALG = 0; DFI1_ALG = 1; DFI2_ALG = 2
S_alg_py = [U_ALG, DFI1_ALG, DFI2_ALG] 

DFI1_ORD = 1 
DFI2_ORD = 2
ZU_ORD = 3 
AU_ORD = 4 
S_ord_py = [DFI1_ORD, DFI2_ORD, ZU_ORD, AU_ORD] 
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

# --- Aspect Determination & Mapping ---
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
        if op_name == "div": # Simplified for this context
            if result_alg == U_ALG : dfi_driven_saturation = True
    elif op_name == "div" and a_alg != U_ALG and b_alg == U_ALG and b_input_aspect_val == Z_ASPECT_VAL: 
        dfi_driven_saturation = True
    if dfi_driven_saturation: return A_ASPECT_VAL
    
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
    raise ValueError(f"Cannot map algebraic value {alg_val}")

def print_model_order(model: Optional[Dict], le_vars: Dict[Tuple[int,int],FNode], 
                          s_ord_keys: List[int], title:str="Candidate Order Relations"):
    if model:
        print(f"    {title} le(x,y) [x <= y]:")
        ord_map_to_name = {DFI1_ORD: "D1s", DFI2_ORD: "D2s", ZU_ORD: "ZUs", AU_ORD: "AUs"}
        for i_o in s_ord_keys:
            related_to_i_list_names = []
            for j_o in s_ord_keys:
                le_var = le_vars.get((i_o,j_o))
                if le_var and model.get_value(le_var).is_true(): 
                    related_to_i_list_names.append(ord_map_to_name.get(j_o, str(j_o)))
            related_to_i_list_names.sort() 
            print(f"      {ord_map_to_name.get(i_o, str(i_o)):<5} <= {related_to_i_list_names}")

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
            le_split_vars[(i_o,j_o)] = Symbol(f"leS_{i_o}_{j_o}_lat_fixed", SMT_BOOL_TYPE)

    s = Solver(name="z3", logic="QF_UFLIA") # CORRECTED LOGIC
    
    order_assertions = []
    # 1. Assert the fixed candidate partial order
    for i_o in S_ord_py: 
        order_assertions.append(le_split_vars[(i_o,i_o)]) # Reflexivity
        for j_o in S_ord_py:
            if i_o == j_o: continue
            # If (i_o, j_o) is a specified true edge
            if (i_o, j_o) in candidate_order_true_edges:
                order_assertions.append(le_split_vars[(i_o,j_o)])
            # If its symmetric counterpart (j_o, i_o) is a specified true edge, then le(i,j) must be false by antisymmetry
            elif (j_o, i_o) in candidate_order_true_edges:
                 order_assertions.append(Not(le_split_vars[(i_o,j_o)]))
            # Otherwise, if not specified and not reflexive, assert false to fix the sparse order
            else:
                order_assertions.append(Not(le_split_vars[(i_o,j_o)]))
    
    # Assert PO axioms (Antisymmetry, Transitivity) for the defined le_split_vars
    # These will act as consistency checks on the fixed order defined above.
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            if i_o != j_o: 
                order_assertions.append(Implies(And(le_split_vars[(i_o,j_o)], le_split_vars[(j_o,i_o)]), FALSE()))
            for k_o in S_ord_py: 
                order_assertions.append(Implies(And(le_split_vars[(i_o,j_o)], le_split_vars[(j_o,k_o)]), le_split_vars[(i_o,k_o)]))
    s.add_assertions(order_assertions)
    
    print("  Step 1: Checking consistency of defined candidate partial order...")
    if not s.solve():
        print("    UNSAT: The candidate EDGES are INCONSISTENT with Partial Order axioms. Halting.")
        return
    print("    Candidate order is a consistent Partial Order.")
    # model_po = s.get_model() # Can inspect the le_split_vars
    # print_order_relations(model_po, le_split_vars, S_ord_py, "Fixed Candidate Order")

    # 2. Declare symbolic join/meet variables and assert their LUB/GLB properties
    join_vars: Dict[Tuple[int,int], FNode] = {}
    meet_vars: Dict[Tuple[int,int], FNode] = {}
    lattice_prop_assertions = []

    for a_o_py_lattice in S_ord_py: # Renamed to avoid clash
        for b_o_py_lattice in S_ord_py:
            # --- LUB (Join) j = LUB(a,b) ---
            j_var = Symbol(f"join_{a_o_py_lattice}_{b_o_py_lattice}", SMT_INT_TYPE)
            join_vars[(a_o_py_lattice,b_o_py_lattice)] = j_var
            lattice_prop_assertions.append(Or([Equals(j_var, Int(s_el)) for s_el in S_ord_py])) 

            # Property 1: j_var is an upper bound of a_o and b_o
            # le_split_vars[(a_o, k)] must hold if j_var = k
            # This means: Forall k_val in S_ord_py, (j_var == k_val) IMPLIES (le_split_vars[(a_o_py_lattice, k_val)] AND le_split_vars[(b_o_py_lattice, k_val)])
            # No, this is backwards. It should be: le_split_vars[(a_o_py_lattice, j_var_val)] where j_var_val is the value of j_var
            # This needs to be: j_var is some k. Assert le(a,k) and le(b,k)
            upper_bound_conds_j = []
            for k_val_j in S_ord_py:
                upper_bound_conds_j.append(
                    Implies(Equals(j_var, Int(k_val_j)), 
                            And(le_split_vars[(a_o_py_lattice, k_val_j)], le_split_vars[(b_o_py_lattice, k_val_j)]))
                )
            lattice_prop_assertions.append(And(upper_bound_conds_j))
            
            # Property 2: j_var is the *least* of the upper bounds
            # Forall z_o in S_ord_py: (le_split_vars[(a_o_py_lattice,z_o)] AND le_split_vars[(b_o_py_lattice,z_o)]) IMPLIES le_split_vars_for_j_z
            lub_minimality_clauses_for_pair = []
            for z_o_py in S_ord_py:
                prem_z_is_upper_bound = And(le_split_vars[(a_o_py_lattice,z_o_py)], le_split_vars[(b_o_py_lattice,z_o_py)])
                cons_j_le_z_clauses = [] # If j_var = k_val, then le_split_vars[(k_val, z_o_py)]
                for k_j_val in S_ord_py:
                    cons_j_le_z_clauses.append(Implies(Equals(j_var, Int(k_j_val)), le_split_vars[(k_j_val, z_o_py)]))
                lub_minimality_clauses_for_pair.append(Implies(prem_z_is_upper_bound, And(cons_j_le_z_clauses)))
            lattice_prop_assertions.append(And(lub_minimality_clauses_for_pair))

            # --- GLB (Meet) m = GLB(a,b) --- (Symmetric logic)
            m_var = Symbol(f"meet_{a_o_py_lattice}_{b_o_py_lattice}", SMT_INT_TYPE)
            meet_vars[(a_o_py_lattice,b_o_py_lattice)] = m_var
            lattice_prop_assertions.append(Or([Equals(m_var, Int(s_el)) for s_el in S_ord_py]))
            lower_bound_conds_m = []
            for k_val_m in S_ord_py:
                lower_bound_conds_m.append(
                    Implies(Equals(m_var, Int(k_val_m)),
                            And(le_split_vars[(k_val_m, a_o_py_lattice)], le_split_vars[(k_val_m, b_o_py_lattice)]))
                )
            lattice_prop_assertions.append(And(lower_bound_conds_m))
            
            glb_maximality_clauses_for_pair = []
            for z_o_py in S_ord_py:
                prem_z_is_lower_bound = And(le_split_vars[(z_o_py,a_o_py_lattice)], le_split_vars[(z_o_py,b_o_py_lattice)])
                cons_z_le_m_clauses = []
                for k_m_val in S_ord_py:
                    cons_z_le_m_clauses.append(Implies(Equals(m_var, Int(k_m_val)), le_split_vars[(z_o_py, k_m_val)]))
                glb_maximality_clauses_for_pair.append(Implies(prem_z_is_lower_bound, And(cons_z_le_m_clauses)))
            lattice_prop_assertions.append(And(glb_maximality_clauses_for_pair))
    
    s.add_assertions(lattice_prop_assertions)
    print(f"  Added {len(lattice_prop_assertions)} assertions defining symbolic join/meet variables as LUB/GLB.")
    print("  Step 2: Checking if the candidate order forms a lattice...")
    
    if not s.solve():
        print("    UNSAT: The candidate order DOES NOT form a lattice. LUB/GLB properties cannot be satisfied for all pairs. Halting.")
        return
    print("    SAT: The candidate order IS a lattice (LUB/GLB variables assigned consistently).")
    model_lattice_vars = s.get_model()

    solved_joins_map: Dict[Tuple[int,int], FNode] = {}
    solved_meets_map: Dict[Tuple[int,int], FNode] = {}
    print("    Solved Join Table (LUBs for the candidate order, S_ord values):")
    header_join = "Join |" + "".join([f" {str(k):<3}" for k in S_ord_py])
    print(f"    {header_join}")
    for a_o in S_ord_py:
        row = f"    {str(a_o):<3}|"
        for b_o in S_ord_py:
            join_var_node = join_vars.get((a_o,b_o))
            val_node = model_lattice_vars.get_value(join_var_node) if join_var_node else None
            solved_joins_map[(a_o,b_o)] = val_node
            row += f" {str(val_node.constant_value() if val_node else '?'):<3}"
        print(row)
        
    print("    Solved Meet Table (GLBs for the candidate order, S_ord values):")
    header_meet = "Meet |" + "".join([f" {str(k):<3}" for k in S_ord_py])
    print(f"    {header_meet}")
    for a_o in S_ord_py:
        row = f"    {str(a_o):<3}|"
        for b_o in S_ord_py:
            meet_var_node = meet_vars.get((a_o,b_o))
            val_node = model_lattice_vars.get_value(meet_var_node) if meet_var_node else None
            solved_meets_map[(a_o,b_o)] = val_node
            row += f" {str(val_node.constant_value() if val_node else '?'):<3}"
        print(row)

    # 3. Assert that mapped AVCA ops deliver these solved joins/meets
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
                map_b_ord = map_avca_alg_to_ord_id(b_alg_py, op_name, b_alg_py, U_ALG, b_input_aspect, Z_ASPECT_VAL)

                res_op_alg = current_op_table[(a_alg_py, b_alg_py)]
                map_res_op_ord_val = map_avca_alg_to_ord_id(res_op_alg, op_name, a_alg_py, b_alg_py, a_input_aspect, b_input_aspect)
                
                target_lattice_op_val_smt = solved_joins_map.get((map_a_ord, map_b_ord)) if is_join_op else solved_meets_map.get((map_a_ord, map_b_ord))
                
                if target_lattice_op_val_smt is not None:
                    op_match_assertions.append(Equals(Int(map_res_op_ord_val), target_lattice_op_val_smt))
                else:
                    print(f"ERROR: Missing solved join/meet for S_ord pair ({map_a_ord},{map_b_ord}) for op {op_name}")
                    s.add_assertion(FALSE()) 
    
    s.add_assertions(op_match_assertions)
    print(f"  Added {len(op_match_assertions)} assertions for AVCA ops matching solved join/meet values.")
    
    print("  Step 3: Solving final combined constraints (Order is Lattice AND AVCA ops are Join/Meet)...")
    if s.solve():
        print("  OVERALL RESULT: SAT!")
        print(f"    SUCCESS: The candidate order IS a lattice, AND mapped AVCA op(s) {ops_to_test_str_list} behave as join/meet.")
    else:
        print("  OVERALL RESULT: UNSAT.")
        print(f"    FAILURE: The candidate order IS a lattice, BUT mapped AVCA op(s) {ops_to_test_str_list} DO NOT behave as join/meet.")

if __name__ == "__main__":
    # Candidate order from split_unio_order_richer.py for ops=["add", "mul"], min_extra_edges=2
    # S_ord_py = [DFI1s=1, DFI2s=2, ZUs=3, AUs=4]
    # Order relations: 1<=1, 2<=2, 3<=3, 4<=4 (reflexive)
    #                  1<=4 (DFI1s <= AUs)
    #                  3<=4 (ZUs <= AUs)
    # All other distinct pairs are INCOMPARABLE (le_split is false for them).
    candidate_edges_2extra_common_mono = [
        (DFI1_ORD, AU_ORD), 
        (ZU_ORD, AU_ORD)
        # Implied by transitivity if DFI1 <= DFI2 and DFI2 <= AU, then DFI1 <= AU.
        # The richer order found for add only with min_extra_edges=2 was:
        # DFI1sem <= ['AUsem', 'DFI1sem', 'DFI2sem'] -> (1,4), (1,2)
        # DFI2sem <= ['AUsem', 'DFI2sem']           -> (2,4)
        # ZUsem   <= ['AUsem', 'ZUsem']             -> (3,4)
        # This is: (1,2), (1,4), (2,4), (3,4)
    ]
    print("Testing Richer 2-edge Common Monotonic Order (DFI1<=AU, ZU<=AU):")
    run_split_unio_lattice_check(candidate_order_true_edges=candidate_edges_2extra_common_mono, 
                                 ops_to_test_str_list=["add","mul"])

    print("\nTesting Minimal 1-edge Common Monotonic Order (DFI2<=AU):")
    candidate_edges_1extra_common_mono = [(DFI2_ORD, AU_ORD)]
    run_split_unio_lattice_check(candidate_order_true_edges=candidate_edges_1extra_common_mono, 
                                 ops_to_test_str_list=["add","mul"])
