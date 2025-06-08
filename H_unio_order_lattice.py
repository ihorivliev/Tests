from pysmt.shortcuts import (Symbol, And, Or, Implies, Solver, Equals, Not, Int, Plus, Ite,
                             TRUE, FALSE, GE, LE, ForAll, Exists) # Ensure ForAll, Exists imported
from pysmt.typing import BOOL as SMT_BOOL_TYPE, INT as SMT_INT_TYPE, FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Optional

# --- Configuration ---
OMEGA_VAL = 3
U_ALG = 0
DFI1_ALG = 1
DFI2_ALG = 2
S_alg_py = [U_ALG, DFI1_ALG, DFI2_ALG]

DFI1_ORD = 1 
DFI2_ORD = 2
ZU_ORD = 3 
AU_ORD = 4 
S_ord_py = [DFI1_ORD, DFI2_ORD, ZU_ORD, AU_ORD]
S_ord_smt = [Int(i) for i in S_ord_py]

Z_ASPECT_VAL = 0
A_ASPECT_VAL = 1
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

# --- Aspect Logic & Mapping (from aspect_tagged_dfi_check.py, slightly adapted) ---
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
        if op_name == "div_placeholder": # Assuming div means ⊘
            if (a_alg == DFI1_ALG and b_alg == DFI2_ALG): dfi_driven_saturation = True 
    elif op_name == "div_placeholder" and a_alg != U_ALG and b_alg == U_ALG and b_input_aspect_val == Z_ASPECT_VAL: 
        dfi_driven_saturation = True
    if dfi_driven_saturation: return A_ASPECT_VAL
    
    eff_a_asp = get_effective_input_aspect(a_alg, a_input_aspect_val, False)
    eff_b_asp = get_effective_input_aspect(b_alg, b_input_aspect_val, False)
    
    if op_name == "div_placeholder" and a_alg == U_ALG and b_alg == U_ALG: # AltD U/U
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

# --- Main Lattice Check Function ---
def run_split_unio_lattice_check(test_ops_str_list: List[str], 
                                 candidate_order_edges: List[Tuple[int,int]],
                                 candidate_order_non_edges: List[Tuple[int,int]] = None): # Optional non-edges

    print(f"\n--- split_unio_order_lattice_check.py (Omega_alg=3) ---")
    print(f"    Testing order defined by EDGES = {candidate_order_edges}")
    if candidate_order_non_edges: print(f"    and NON_EDGES = {candidate_order_non_edges}")
    print(f"    Checking if it's a lattice and if AVCA ops {test_ops_str_list} are join/meet.")

    le_split_vars: Dict[Tuple[int,int], FNode] = {}
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            le_split_vars[(i_o,j_o)] = Symbol(f"leS_{i_o}_{j_o}", SMT_BOOL_TYPE)

    s = Solver(name="z3", logic="QF_LIA") # Using QF_LIA as we have Ints for join/meet vars

    # 1. Assert the candidate partial order from EDGES
    order_assertions = []
    # Reflexivity is always true for a PO, SMT will ensure this if trying to find a model for le_split_vars
    for i_o in S_ord_py: order_assertions.append(le_split_vars[(i_o,i_o)]) 
    # Assert specified edges
    for (i,j) in candidate_order_edges:
        if (i,j) in le_split_vars: order_assertions.append(le_split_vars[(i,j)])
    # Assert specified non-edges (if any)
    if candidate_order_non_edges:
        for (i,j) in candidate_order_non_edges:
            if (i,j) in le_split_vars: order_assertions.append(Not(le_split_vars[(i,j)]))
    
    # To ensure it's a specific order, one might need to assert False for all other non-reflexive pairs not in EDGES.
    # For now, let's assume EDGES define the primary non-reflexive true relations.
    # The PO axioms will propagate these.

    # 2. Assert Partial Order axioms for le_split_vars
    for i_o in S_ord_py:
        for j_o in S_ord_py:
            if i_o != j_o: 
                order_assertions.append(Implies(And(le_split_vars[(i_o,j_o)], le_split_vars[(j_o,i_o)]), FALSE())) # Antisymmetry
            for k_o in S_ord_py: # Transitivity
                order_assertions.append(Implies(And(le_split_vars[(i_o,j_o)], le_split_vars[(j_o,k_o)]), le_split_vars[(i_o,k_o)]))
    s.add_assertions(order_assertions)
    
    # Check if this defined order is itself consistent
    print("  Checking consistency of defined partial order...")
    if not s.solve():
        print("    UNSAT: The defined EDGES and NON_EDGES are inconsistent with Partial Order axioms. Halting.")
        return
    print("    Defined order is consistent with PO axioms.")

    # 3. Declare symbolic join/meet variables and assert their LUB/GLB properties
    join_vars: Dict[Tuple[int,int], FNode] = {}
    meet_vars: Dict[Tuple[int,int], FNode] = {}
    lattice_property_assertions = []

    for a_ord in S_ord_py:
        for b_ord in S_ord_py:
            j_var = Symbol(f"join_{a_ord}_{b_ord}", SMT_INT_TYPE)
            m_var = Symbol(f"meet_{a_ord}_{b_ord}", SMT_INT_TYPE)
            join_vars[(a_ord,b_ord)] = j_var
            meet_vars[(a_ord,b_ord)] = m_var

            # Constrain j_var and m_var to be elements of S_ord
            lattice_property_assertions.append(Or([Equals(j_var, s_el_smt) for s_el_smt in S_ord_smt]))
            lattice_property_assertions.append(Or([Equals(m_var, s_el_smt) for s_el_smt in S_ord_smt]))

            # Assert j_var is LUB of a_ord, b_ord
            lattice_property_assertions.append(le_split_vars[(a_ord, j_var.constant_value() if j_var.is_int_constant() else a_ord )]) # Placeholder for j_var if symbolic for now
            lattice_property_assertions.append(le_split_vars[(b_ord, j_var.constant_value() if j_var.is_int_constant() else b_ord )])
            
            # Forall z in S_ord: (a_ord <= z AND b_ord <= z) => j_var <= z
            lub_min_clauses = []
            for z_ord in S_ord_py:
                lub_min_clauses.append(Implies(And(le_split_vars[(a_ord,z_ord)], le_split_vars[(b_ord,z_ord)]), 
                                             le_split_vars[(j_var.constant_value() if j_var.is_int_constant() else a_ord, z_ord)])) # Placeholder
            lattice_property_assertions.append(And(lub_min_clauses))

            # Assert m_var is GLB of a_ord, b_ord
            lattice_property_assertions.append(le_split_vars[(m_var.constant_value() if m_var.is_int_constant() else a_ord, a_ord)]) # Placeholder
            lattice_property_assertions.append(le_split_vars[(m_var.constant_value() if m_var.is_int_constant() else b_ord, b_ord)])
            
            glb_max_clauses = []
            for z_ord in S_ord_py:
                glb_max_clauses.append(Implies(And(le_split_vars[(z_ord, a_ord)], le_split_vars[(z_ord, b_ord)]),
                                             le_split_vars[(z_ord, m_var.constant_value() if m_var.is_int_constant() else a_ord)])) # Placeholder
            lattice_property_assertions.append(And(glb_max_clauses))
    
    # This direct assertion of LUB/GLB properties for symbolic join/meet vars is complex.
    # A simpler SMT check for "is it a lattice" is:
    # For every pair (a,b), does there EXIST a unique LUB and unique GLB?
    # The auditor's skeleton was more direct: define join/meet vars and then assert AVCA ops equal them.
    # Let's follow that, but be aware that if the order from EDGES isn't a lattice, the join/meet constraints might make it UNSAT.

    # Using auditor's approach: constrain join_vars and meet_vars to BE the LUB/GLB
    # This assumes the LUB/GLB exist for the given 'le_split_vars' defined by EDGES.
    # The SMT solver will fail if 'le_split_vars' doesn't form a lattice.
    
    s.add_assertions(lattice_property_assertions) # These assertions define join_vars and meet_vars
    
    print(f"  Added {len(lattice_property_assertions)} assertions to define join/meet variables as LUB/GLB.")
    print("  Checking if the defined order forms a lattice (i.e., if LUBs/GLBs consistently exist)...")
    if not s.solve():
        print("    UNSAT: The defined order from EDGES does NOT form a lattice (LUB/GLB properties are inconsistent). Halting.")
        return
    print("    SAT: The defined order IS a lattice (LUB/GLB properties are consistent).")
    # model_lattice = s.get_model() # Can inspect join_vars and meet_vars if needed

    # 4. Assert that mapped AVCA ops deliver these joins/meets
    op_match_assertions = []
    for op_name in test_ops_str_list:
        current_op_table = avca_add_table_alg_omega3 if op_name == "add" else avca_mul_table_alg_omega3
        is_join_op = True if op_name == "add" else False # Assume ⊕ is join, ⊗ is meet

        print(f"    Asserting mapped AVCA-{op_name} {'IS join' if is_join_op else 'IS meet'}...")
        for a_alg_py in S_alg_py:
            a_input_aspect = Z_ASPECT_VAL # Default input aspect for U_ALG
            map_a_ord = map_avca_alg_to_ord_id(a_alg_py, op_name, a_alg_py, U_ALG, a_input_aspect, Z_ASPECT_VAL)
            for b_alg_py in S_alg_py:
                b_input_aspect = Z_ASPECT_VAL
                map_b_ord = map_avca_alg_to_ord_id(b_alg_py, op_name, b_alg_py, U_ALG, b_input_aspect, Z_ASPECT_VAL)

                res_op_alg = current_op_table[(a_alg_py, b_alg_py)]
                map_res_op_ord = map_avca_alg_to_ord_id(res_op_alg, op_name, a_alg_py, b_alg_py, a_input_aspect, b_input_aspect)
                
                target_lattice_op_var = join_vars[(map_a_ord, map_b_ord)] if is_join_op else meet_vars[(map_a_ord, map_b_ord)]
                op_match_assertions.append(Equals(Int(map_res_op_ord), target_lattice_op_var))
    
    s.add_assertions(op_match_assertions)
    print(f"  Added {len(op_match_assertions)} assertions for AVCA ops matching join/meet.")
    
    print("  Solving final combined constraints (Order is Lattice AND AVCA ops are Join/Meet)...")
    if s.solve():
        print("  OVERALL RESULT: SAT!")
        print(f"    SUCCESS: The candidate order defined by EDGES={candidate_order_edges}")
        print(f"             IS a lattice, AND mapped AVCA operation(s) {test_ops_str_list}")
        print(f"             behave as {'join' if 'add' in test_ops_str_list else ''}{' and ' if 'add' in test_ops_str_list and 'mul' in test_ops_str_list else ''}{'meet' if 'mul' in test_ops_str_list else ''} respectively.")
        # model_final = s.get_model()
        # print_model_table(model_final, le_split_vars_dict_for_printing, S_ord_py, "Final Order") # Need to adapt print
    else:
        print("  OVERALL RESULT: UNSAT.")
        print(f"    FAILURE: The candidate order defined by EDGES={candidate_order_edges}")
        print(f"             either is not a lattice OR mapped AVCA operation(s) {test_ops_str_list}")
        print(f"             do not behave as join/meet.")

if __name__ == "__main__":
    # Candidate order found in previous run (split_unio_order_richer.py for ops=["add","mul"], min_extra_edges=1)
    # was DFI2_sem <= AU_sem (i.e., 2 <= 4 in S_ord_py = [1,2,3,4]) and reflexive.
    # All other distinct pairs were incomparable.
    
    # Let's define this specific order:
    # S_ord_py = [DFI1_ORD=1, DFI2_ORD=2, ZU_ORD=3, AU_ORD=4]
    # Reflexive: (1,1), (2,2), (3,3), (4,4) are TRUE for le_split
    # Specified non-reflexive edge: (2,4) is TRUE for le_split (DFI2 <= AU)
    # All other le_split(i,j) where i!=j and (i,j)!=(2,4) are FALSE to make it specific.
    
    # This script structure is complex because defining LUB/GLB properties for symbolic join/meet vars
    # with ForAll quantifiers is hard for SMT. The auditor's skeleton for assert_join_meet_property
    # directly equates the mapped AVCA op result with the symbolic join/meet var.
    # The declare_join_meet then has to successfully constrain these vars.

    # The placeholders in `declare_join_meet` from auditor's skeleton:
    # `le[(a,j)]` etc. inside `declare_join_meet` used SMT variables `a,b,j,z` that are SMT Ints from S_ORD.
    # My `le_split_vars` uses Python int tuples as keys. This needs to be reconciled.

    # For this iteration, I will simplify the script to focus on:
    # 1. Asserting a USER-PROVIDED fixed order via le_split_vars values.
    # 2. Checking if THIS fixed order is a lattice by testing LUB/GLB existence for all pairs.
    # 3. If it is, checking if mapped AVCA ops match LUB/GLB.

    print("INFO: The SMT script 'split_unio_order_lattice_check.py' provided is a complex framework.")
    print("      It requires careful definition of the LUB/GLB constraints (placeholder used).")
    print("      A simpler first step might be to manually define a candidate lattice structure for S_ord")
    print("      (all le(i,j) pairs) in get_user_defined_order_assertions() of the *previous* script")
    print("      (H_O1_SMT_Order_Check_Framework) and test basic PO properties + monotonicity there first.")
    print("      The full lattice check with join/meet variables as LUB/GLB is advanced SMT.")
    print("      Due to this complexity and the placeholder nature of LUB/GLB constraints,")
    print("      this script is provided as a template for further development and not run by default.")

    # To make this runnable, one would need to fully flesh out the LUB/GLB SMT constraints
    # in declare_join_meet and how assert_join_meet_property uses them,
    # or adopt a simpler instance-checking approach for LUB/GLB for the fixed S_ord.
    # For now, I will not call run_split_unio_lattice_check from here as it's not complete.

