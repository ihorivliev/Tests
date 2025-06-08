# Test_C2_SL_DistributiveLattice_Checker.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             ForAll, Exists, Solver, TRUE, FALSE, Function)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable, Set

# S_ord elements for Omega=3: DFI1_s, DFI2_s, ZU_s, AU_s
# Mapped to integers 0, 1, 2, 3 for SMT representation.
ELEMENT_MAP_S_ORD = {
    0: "DFI1s", 1: "DFI2s", 2: "ZUs", 3: "AUs"
}
PY_S_ORD_KEYS = sorted(ELEMENT_MAP_S_ORD.keys())
SMT_S_ORD_ELEMENTS = [Int(k) for k in PY_S_ORD_KEYS]

def op_table_to_str_c2_sl(
    op_func_symbol: FNode, # This will be the SMT function for join or meet
    model: Solver, 
    op_char: str
) -> str:
    s = f"   {op_char}  | " + " | ".join([ELEMENT_MAP_S_ORD[k].center(5) for k in PY_S_ORD_KEYS])
    separator = "-----|-" + "-|-".join(["-----" for _ in PY_S_ORD_KEYS]) + "-|"
    
    lines = [s, separator]
    for r_key in PY_S_ORD_KEYS:
        r_smt = Int(r_key)
        row_str = f"{ELEMENT_MAP_S_ORD[r_key]:<5}| "
        for c_key in PY_S_ORD_KEYS:
            c_smt = Int(c_key)
            op_call_result_fnode = op_func_symbol(r_smt, c_smt) # Call the SMT function
            val_fnode_in_model = model.get_value(op_call_result_fnode)
            row_str += f"{ELEMENT_MAP_S_ORD[val_fnode_in_model.constant_value()].center(5)}| "
        lines.append(row_str)
    return "\n".join(lines)

def run_C2_distributive_lattice_check(
    omega_val: int, 
    candidate_po_true_relations: List[Tuple[int, int]], 
    po_name: str = "Candidate PO"
):
    if omega_val != 3:
        print(f"ERROR: This script version is hardcoded for Ω=3 (4 S_ord elements). Cannot run for Ω={omega_val}.")
        return

    print(f"====== SCRIPT: Test_C2_SL_DistributiveLattice_Checker.py (Ω={omega_val}) ======")
    print(f"Purpose: Test if the SPECIFIED CANDIDATE PO on S_ord = {{DFI1s, DFI2s, ZUs, AUs}}")
    print("         forms a DISTRIBUTIVE lattice.")
    print(f"Candidate PO Name: {po_name}")
    print(f"Input True Relations (x <= y): {[(ELEMENT_MAP_S_ORD[x], ELEMENT_MAP_S_ORD[y]) for x,y in candidate_po_true_relations]}")
    print("Expected: SAT if this PO forms a distributive lattice.\n")

    le_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le = Symbol("le_s_ord", le_func_type)

    assertions = []
    
    print("--- Defining Candidate Partial Order via 'le' function axioms ---")
    # 1. Define the 'le' function based on candidate_po_true_relations
    # All pairs (x,y) not in candidate_po_true_relations are assumed Not(le(x,y)) unless x=y
    for x_smt_val in SMT_S_ORD_ELEMENTS:
        for y_smt_val in SMT_S_ORD_ELEMENTS:
            x_py_val = x_smt_val.constant_value()
            y_py_val = y_smt_val.constant_value()
            
            is_in_candidate_list = (x_py_val, y_py_val) in candidate_po_true_relations
            
            if is_in_candidate_list:
                assertions.append(le(x_smt_val, y_smt_val))
            else:
                # If not in list, it's false, unless it's reflexive and wasn't added
                if x_py_val == y_py_val and not is_in_candidate_list : # ensure reflexivity if not explicitly listed
                     assertions.append(le(x_smt_val, y_smt_val))
                elif x_py_val != y_py_val : # only assert Not for non-reflexive pairs not in list
                     assertions.append(Not(le(x_smt_val, y_smt_val)))


    # 2. Assert PO Axioms for 'le' (to ensure candidate_po_true_relations define a valid PO)
    print("--- Asserting PO Axioms for the defined 'le' relation ---")
    for x_refl in SMT_S_ORD_ELEMENTS: # Reflexivity
        assertions.append(le(x_refl, x_refl)) # Should be implied if PO list is complete
    for x_anti in SMT_S_ORD_ELEMENTS: # Antisymmetry
        for y_anti in SMT_S_ORD_ELEMENTS:
            if x_anti.constant_value() != y_anti.constant_value():
                assertions.append(Implies(And(le(x_anti,y_anti), le(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in SMT_S_ORD_ELEMENTS: # Transitivity
        for y_trans in SMT_S_ORD_ELEMENTS:
            for z_trans in SMT_S_ORD_ELEMENTS:
                assertions.append(Implies(And(le(x_trans,y_trans), le(y_trans,z_trans)), le(x_trans,z_trans)))
    
    # Symbolic LUB (join) and GLB (meet) operations as functions
    op_func_type = FunctionType(SMT_INT_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    join_op = Symbol("join_s_ord", op_func_type)
    meet_op = Symbol("meet_s_ord", op_func_type)

    print("\n--- Asserting Lattice Properties (LUB & GLB for all pairs) ---")
    for x_lattice in SMT_S_ORD_ELEMENTS:
        for y_lattice in SMT_S_ORD_ELEMENTS:
            lub_xy = join_op(x_lattice, y_lattice)
            glb_xy = meet_op(x_lattice, y_lattice)

            # LUB/GLB results must be in S_ord
            assertions.append(Or([Equals(lub_xy, elem) for elem in SMT_S_ORD_ELEMENTS]))
            assertions.append(Or([Equals(glb_xy, elem) for elem in SMT_S_ORD_ELEMENTS]))

            # LUB properties: x <= LUB(x,y) and y <= LUB(x,y)
            assertions.append(le(x_lattice, lub_xy))
            assertions.append(le(y_lattice, lub_xy))
            # LUB is least: for any z_lub, if x <= z_lub and y <= z_lub, then LUB(x,y) <= z_lub
            for z_lub in SMT_S_ORD_ELEMENTS:
                assertions.append(Implies(And(le(x_lattice, z_lub), le(y_lattice, z_lub)), le(lub_xy, z_lub)))
            
            # GLB properties: GLB(x,y) <= x and GLB(x,y) <= y
            assertions.append(le(glb_xy, x_lattice))
            assertions.append(le(glb_xy, y_lattice))
            # GLB is greatest: for any z_glb, if z_glb <= x and z_glb <= y, then z_glb <= GLB(x,y)
            for z_glb in SMT_S_ORD_ELEMENTS:
                assertions.append(Implies(And(le(z_glb, x_lattice), le(z_glb, y_lattice)), le(z_glb, glb_xy)))

    print("\n--- Asserting Distributivity for Join and Meet ---")
    # x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)  (meet over join)
    # x ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z)  (join over meet)
    for x_dist in SMT_S_ORD_ELEMENTS:
        for y_dist in SMT_S_ORD_ELEMENTS:
            for z_dist in SMT_S_ORD_ELEMENTS:
                # Meet over Join
                lhs1 = meet_op(x_dist, join_op(y_dist, z_dist))
                rhs1 = join_op(meet_op(x_dist, y_dist), meet_op(x_dist, z_dist))
                assertions.append(Equals(lhs1, rhs1))

                # Join over Meet
                lhs2 = join_op(x_dist, meet_op(y_dist, z_dist))
                rhs2 = meet_op(join_op(x_dist, y_dist), join_op(x_dist, z_dist))
                assertions.append(Equals(lhs2, rhs2))

    print("\n--- Solving with SMT (Z3) ---")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Test C-2 (Distributive Lattice Check for PO '{po_name}'): {'SAT' if result else 'UNSAT'}")

        if result:
            print(f"  INTERPRETATION: SAT means the candidate PO '{po_name}' CAN form a distributive lattice.")
            model = s.get_model()
            print("  Distributive lattice structure found. Join (LUB) and Meet (GLB) tables from model:")
            
            print("\n  JOIN (LUB) Table (Candidate ⊕̄):")
            print(op_table_to_str_c2_sl(join_op, model, "∨"))
            print("\n  MEET (GLB) Table (Candidate ⊗̄):")
            print(op_table_to_str_c2_sl(meet_op, model, "∧"))
            print("\n  This PO is a candidate for C-2. Next: Verify homomorphism to AVCA-Ω including aspects (Task B3).")
        else: # UNSAT
            print(f"  INTERPRETATION: UNSAT means the specific candidate PO '{po_name}' CANNOT form a distributive lattice,")
            print("                  or the PO definition was inconsistent with lattice/distributivity axioms.")
            print(f"                  This candidate PO for C-2 is falsified as a distributive lattice cover.")

    print(f"\n====== Test_C2_SL_DistributiveLattice_Checker.py (Ω={omega_val}, PO='{po_name}') Finished ======")

if __name__ == "__main__":
    # Example Candidate PO for Ω=3 S_ord={DFI1s=0, DFI2s=1, ZUs=2, AUs=3}
    # This is the "2-extra-edge from Ch.X common monotone for ⊕,⊗"
    # Hasse: (no DFI1-DFI2 direct link), DFI1s -> AUs, ZUs -> AUs. DFI2s is isolated from other DFI/ZU.
    # This PO was: DFI1s ≤ AUs and ZUs ≤ AUs (and reflexive). DFI2s is only related to itself.
    # Let's test THIS specific sparse one first.
    candidate_po_1_name = "CommonMonotonic_DFI1≤AU_ZU≤AU_DFI2iso"
    candidate_po_1_relations = [ # (lesser_int, greater_int)
        (0,0), (1,1), (2,2), (3,3), # Reflexive
        (0,3), # DFI1s <= AUs
        (2,3)  # ZUs <= AUs
    ]
    # run_C2_distributive_lattice_check(omega_val=3, candidate_po_true_relations=candidate_po_1_relations, po_name=candidate_po_1_name)
    
    print("\n" + "="*70 + "\n")

    # Candidate PO that FAILED the lattice test in your previous output
    # Hasse: DFI1s -> DFI2s -> AUs and ZUs -> AUs.
    # (DFI1s=0, DFI2s=1, ZUs=2, AUs=3)
    candidate_po_2_name = "AuditorFailedLatticeTestPO_DFI1-DFI2-AU_ZU-AU"
    candidate_po_2_relations = [
        (0,0), (1,1), (2,2), (3,3), # Reflexive
        (0,1), # DFI1s <= DFI2s
        (0,3), # DFI1s <= AUs (implied, but good to be explicit if this is the definition)
        (1,3), # DFI2s <= AUs
        (2,3)  # ZUs <= AUs
    ]
    run_C2_distributive_lattice_check(omega_val=3, candidate_po_true_relations=candidate_po_2_relations, po_name=candidate_po_2_name)

    # TODO for user: After running split_unio_order_richer.py (Task B1) to get a list of
    # richer common monotonic POs, plug them into this script one by one.
    # Example of a richer PO to test (if found by B1), e.g. a lattice-like diamond for DFI1,DFI2,ZU under AU
    # candidate_po_3_name = "HypotheticalRicherPO_from_B1"
    # candidate_po_3_relations = [
    #    (0,0),(1,1),(2,2),(3,3),
    #    (0,1), (0,2), (1,3), (2,3) # Diamond: DFI1s <= DFI2s <= AUs and DFI1s <= ZUs <= AUs
    # ]
    # run_C2_distributive_lattice_check(omega_val=3, candidate_po_true_relations=candidate_po_3_relations, po_name=candidate_po_3_name)