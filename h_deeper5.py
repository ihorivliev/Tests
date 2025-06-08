# Test_C2_Candidate_PO_Lattice_Check_Omega3.py (Corrected Imports and op_table_to_str_c2)
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             ForAll, Exists, Solver, TRUE, FALSE, Function) # Removed BV
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.typing import FunctionType
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable
import itertools

# S_ord elements for Omega=3: DFI1_s, DFI2_s, ZU_s, AU_s
DFI1s, DFI2s, ZUs, AUs = Int(0), Int(1), Int(2), Int(3) 
s_ord_elements = [DFI1s, DFI2s, ZUs, AUs]
s_ord_names = {0: "DFI1s", 1: "DFI2s", 2: "ZUs", 3: "AUs"}
py_s_ord_keys = [0,1,2,3]

def op_table_to_str_c2(table_func: Callable[[FNode, FNode], FNode], model: Solver, op_char: str) -> str:
    # This line defines 'header_str' which is the header
    header_str = f"   {op_char}  | " + " | ".join([s_ord_names[k].center(5) for k in py_s_ord_keys])
    separator = "-----|-" + "-|-".join(["-----" for _ in py_s_ord_keys]) + "-|"
    
    lines = [header_str, separator] # Corrected: Used header_str instead of undefined 'header'
    for r_key in py_s_ord_keys:
        r_smt = s_ord_elements[r_key] # Get the SMT FNode for the row key
        row_str = f"{s_ord_names[r_key]:<5}| " # Use Python int key for s_ord_names
        for c_key in py_s_ord_keys:
            c_smt = s_ord_elements[c_key] # Get the SMT FNode for the column key
            # Get value by creating the function call and getting its model value
            op_call_result_fnode = table_func(r_smt, c_smt)
            val_fnode_in_model = model.get_value(op_call_result_fnode)
            row_str += f"{s_ord_names[val_fnode_in_model.constant_value()].center(5)}| "
        lines.append(row_str)
    return "\n".join(lines)

def run_C2_lattice_distributive_test_omega3():
    print("====== SCRIPT: Test_C2_Candidate_PO_Lattice_Check_Omega3.py ======")
    print("Purpose: Test if a SPECIFIC CANDIDATE common monotonic PO on S_ord (for Ω=3)")
    print("         forms a DISTRIBUTIVE lattice.")
    print("Candidate PO: DFI1s≤DFI2s, DFI2s≤AUs, ZUs≤AUs, (and DFI1s≤AUs by transitivity) & reflexive.")
    print("Expected: SAT if this PO forms a distributive lattice.\n")

    le_func_type = FunctionType(SMT_BOOL_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    le = Symbol("le_s_ord", le_func_type)

    assertions = []
    
    print("--- Defining Candidate Partial Order via 'le' function axioms ---")
    # Hasse diagram: DFI1s -> DFI2s -> AUs and ZUs -> AUs.
    # True non-reflexive relations: le(DFI1s, DFI2s), le(DFI2s, AUs), le(ZUs, AUs), le(DFI1s, AUs)

    # 1. Assert PO Axioms for 'le'
    for x_refl in s_ord_elements: # Reflexivity
        assertions.append(le(x_refl, x_refl))
    for x_anti in s_ord_elements: # Antisymmetry
        for y_anti in s_ord_elements:
            if x_anti.constant_value() != y_anti.constant_value(): 
                assertions.append(Implies(And(le(x_anti,y_anti), le(y_anti,x_anti)), Equals(x_anti,y_anti)))
    for x_trans in s_ord_elements: # Transitivity
        for y_trans in s_ord_elements:
            for z_trans in s_ord_elements:
                assertions.append(Implies(And(le(x_trans,y_trans), le(y_trans,z_trans)), le(x_trans,z_trans)))

    # 2. Assert the specific relations for the candidate PO
    specific_true_relations = [
        le(DFI1s, DFI2s), le(DFI2s, AUs), le(ZUs, AUs), le(DFI1s, AUs)
    ]
    for r_true in specific_true_relations:
        assertions.append(r_true)

    specific_false_relations = [
        le(DFI2s, DFI1s), le(AUs, DFI2s), le(AUs, ZUs), le(AUs, DFI1s),
        le(DFI1s, ZUs), le(ZUs, DFI1s),  
        le(DFI2s, ZUs), le(ZUs, DFI2s)   
    ]
    for r_false in specific_false_relations:
        assertions.append(Not(r_false))
    
    join_func_type = FunctionType(SMT_INT_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    meet_func_type = FunctionType(SMT_INT_TYPE, [SMT_INT_TYPE, SMT_INT_TYPE])
    join_op = Symbol("join_s_ord", join_func_type)
    meet_op = Symbol("meet_s_ord", meet_func_type)

    print("\n--- Asserting Lattice Properties (LUB & GLB for all pairs) ---")
    for x_lattice in s_ord_elements:
        for y_lattice in s_ord_elements:
            lub_xy = join_op(x_lattice, y_lattice)
            glb_xy = meet_op(x_lattice, y_lattice)

            assertions.append(Or([Equals(lub_xy, elem) for elem in s_ord_elements]))
            assertions.append(Or([Equals(glb_xy, elem) for elem in s_ord_elements]))

            assertions.append(le(x_lattice, lub_xy))
            assertions.append(le(y_lattice, lub_xy))
            for z_lub in s_ord_elements:
                assertions.append(Implies(And(le(x_lattice, z_lub), le(y_lattice, z_lub)), le(lub_xy, z_lub)))
            
            assertions.append(le(glb_xy, x_lattice))
            assertions.append(le(glb_xy, y_lattice))
            for z_glb in s_ord_elements:
                assertions.append(Implies(And(le(z_glb, x_lattice), le(z_glb, y_lattice)), le(z_glb, glb_xy)))

    print("\n--- Asserting Distributivity for Join and Meet ---")
    for x_dist in s_ord_elements:
        for y_dist in s_ord_elements:
            for z_dist in s_ord_elements:
                lhs1 = meet_op(x_dist, join_op(y_dist, z_dist))
                rhs1 = join_op(meet_op(x_dist, y_dist), meet_op(x_dist, z_dist))
                assertions.append(Equals(lhs1, rhs1))

                lhs2 = join_op(x_dist, meet_op(y_dist, z_dist))
                rhs2 = meet_op(join_op(x_dist, y_dist), join_op(x_dist, z_dist))
                assertions.append(Equals(lhs2, rhs2))

    print("\n--- Solving with SMT (Z3) ---")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Test C-2 (Distributive Lattice Check for Candidate PO): {'SAT' if result else 'UNSAT'}")

        if result:
            print("  INTERPRETATION: SAT means the candidate PO CAN form a distributive lattice.")
            model = s.get_model()
            print("  Distributive lattice structure found. Join (LUB) and Meet (GLB) tables from model:")
            
            print("\n  JOIN (LUB) Table (⊕̄):")
            print(op_table_to_str_c2(join_op, model, "∨")) # Pass the function symbol
            print("\n  MEET (GLB) Table (⊗̄):")
            print(op_table_to_str_c2(meet_op, model, "∧")) # Pass the function symbol
            print("\n  This supports C-2. Next: Verify homomorphism to AVCA-Ω including aspects.")
        else: # UNSAT
            print("  INTERPRETATION: UNSAT means the specific candidate PO CANNOT form a distributive lattice,")
            print("                  or the PO definition was inconsistent with lattice/distributivity axioms.")
            print("                  This specific candidate PO for C-2 is falsified.")

    print("\n====== Test_C2_Candidate_PO_Lattice_Check_Omega3.py Finished ======")

if __name__ == "__main__":
    run_C2_lattice_distributive_test_omega3()