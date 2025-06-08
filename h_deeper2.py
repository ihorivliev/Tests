# Test_C2_SplitUnioLattice_Omega3.py
from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                             ForAll, Exists, Solver, TRUE, FALSE)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import List, Dict, Tuple, Callable
import itertools # Corrected: Added import

# Define S_ord elements for Omega=3 (DFI1, DFI2, ZU, AU)
# Using integers 0, 1, 2, 3 for SMT representation
DFI1_sord, DFI2_sord, ZU_sord, AU_sord = Int(0), Int(1), Int(2), Int(3)
s_ord_elements = [DFI1_sord, DFI2_sord, ZU_sord, AU_sord]
s_ord_py_map = {0: "DFI1s", 1: "DFI2s", 2: "ZUs", 3: "AUs"} # Map Int to string name

def op_to_str_c2(op_table: Dict[Tuple[int,int],int], elements_map: Dict[int,str], op_char: str = "?") -> str:
    s = f"   {op_char} "
    py_keys = sorted(elements_map.keys()) # Use sorted keys for consistent table output
    for k_col in py_keys: s += f"| {elements_map[k_col]:^5} "
    s += "\n---" + "".join(["|-------" for _ in py_keys]) + "\n"
    for r_key in py_keys:
        s += f"{elements_map[r_key]:<5}" # Adjusted spacing for alignment
        for c_key in py_keys:
            val_int = op_table.get((r_key,c_key), -999) 
            s += f"| {elements_map.get(val_int, 'UND'):^5} "
        s += "\n"
    return s

def run_C2_lattice_test_omega3():
    print("====== SCRIPT: Test_C2_SplitUnioLattice_Omega3.py ======")
    print("Purpose: Test if a candidate common monotonic Partial Order on S_ord (for Ω=3)")
    print("         can form a lattice (LUBs & GLBs exist for all pairs).")
    print("Candidate PO: DFI1s ≤ DFI2s, DFI2s ≤ AUs, ZUs ≤ AUs, (and DFI1s ≤ AUs by transitivity) & reflexive.")
    print("Expected: SAT if a lattice structure is possible under this PO.\n")

    le_vars: Dict[Tuple[FNode, FNode], FNode] = {}
    for x in s_ord_elements:
        for y in s_ord_elements:
            le_vars[(x,y)] = Symbol(f"le_{x.constant_value()}_{y.constant_value()}", SMT_BOOL_TYPE)

    assertions = []
    
    print("--- Defining Candidate Partial Order ---")
    # Hasse diagram: DFI1 -> DFI2 -> AU and ZU -> AU. (Implies DFI1 -> AU)
    # True non-reflexive relations: (DFI1,DFI2), (DFI2,AU), (ZU,AU), (DFI1,AU)
    complete_specific_po_true_fnode_pairs = [
        (DFI1_sord, DFI1_sord), (DFI2_sord, DFI2_sord), (ZU_sord, ZU_sord), (AU_sord, AU_sord), # Reflexive
        (DFI1_sord, DFI2_sord), 
        (DFI2_sord, AU_sord),   
        (ZU_sord, AU_sord),     
        (DFI1_sord, AU_sord)  # By transitivity DFI1<=DFI2 & DFI2<=AU, or directly if preferred.
    ]
    
    for x_smt_po in s_ord_elements:
        for y_smt_po in s_ord_elements:
            if (x_smt_po, y_smt_po) in complete_specific_po_true_fnode_pairs:
                assertions.append(le_vars[(x_smt_po, y_smt_po)]) 
            else:
                assertions.append(Not(le_vars[(x_smt_po, y_smt_po)]))

    # Assert PO Axioms for the fixed le_vars table
    print("--- Asserting PO Axioms for the fixed 'le_vars' relation ---")
    # Reflexivity (already ensured by how specific_po_true_fnodes defines le_vars)
    # Antisymmetry: (x <= y and y <= x) => x = y
    for x in s_ord_elements:
        for y in s_ord_elements:
            if x.constant_value() != y.constant_value(): # Only for distinct elements
                 assertions.append(Implies(And(le_vars[(x,y)], le_vars[(y,x)]), Equals(x,y)))
    
    # Transitivity: (x <= y and y <= z) => x <= z
    for x_trans in s_ord_elements:
        for y_trans in s_ord_elements:
            for z_trans in s_ord_elements:
                assertions.append(Implies(And(le_vars[(x_trans,y_trans)], le_vars[(y_trans,z_trans)]), le_vars[(x_trans,z_trans)]))
    
    join_table_vars: Dict[Tuple[int,int], FNode] = {}
    meet_table_vars: Dict[Tuple[int,int], FNode] = {}
    py_keys_sord = [e.constant_value() for e in s_ord_elements]

    for x_py_key in py_keys_sord:
        for y_py_key in py_keys_sord:
            join_table_vars[(x_py_key, y_py_key)] = Symbol(f"join_{x_py_key}_{y_py_key}", SMT_INT_TYPE)
            meet_table_vars[(x_py_key, y_py_key)] = Symbol(f"meet_{x_py_key}_{y_py_key}", SMT_INT_TYPE)

    print("\n--- Asserting Lattice Properties (LUB & GLB for all pairs under the fixed PO) ---")
    for x_smt_lattice in s_ord_elements:
        x_py_lattice = x_smt_lattice.constant_value()
        for y_smt_lattice in s_ord_elements:
            y_py_lattice = y_smt_lattice.constant_value()
            
            lub_val_sym = join_table_vars[(x_py_lattice, y_py_lattice)]
            glb_val_sym = meet_table_vars[(x_py_lattice, y_py_lattice)]

            assertions.append(Or([Equals(lub_val_sym, elem) for elem in s_ord_elements]))
            assertions.append(Or([Equals(glb_val_sym, elem) for elem in s_ord_elements]))

            # LUB properties: x <= LUB(x,y) and y <= LUB(x,y)
            # x <= lub_val_sym
            assertions.append(Or([And(Equals(lub_val_sym, s_elem_target), le_vars[(x_smt_lattice, s_elem_target)]) for s_elem_target in s_ord_elements]))
            # y <= lub_val_sym
            assertions.append(Or([And(Equals(lub_val_sym, s_elem_target), le_vars[(y_smt_lattice, s_elem_target)]) for s_elem_target in s_ord_elements]))

            # LUB is least: for any z_lub, if x <= z_lub and y <= z_lub, then LUB(x,y) <= z_lub
            for z_smt_lub in s_ord_elements:
                lub_le_z_lub_consequent = Or([And(Equals(lub_val_sym, s_elem_source), le_vars[(s_elem_source, z_smt_lub)]) for s_elem_source in s_ord_elements])
                assertions.append(Implies(And(le_vars[(x_smt_lattice, z_smt_lub)], le_vars[(y_smt_lattice, z_smt_lub)]),
                                          lub_le_z_lub_consequent))

            # GLB properties: GLB(x,y) <= x and GLB(x,y) <= y
            # glb_val_sym <= x
            assertions.append(Or([And(Equals(glb_val_sym, s_elem_source), le_vars[(s_elem_source, x_smt_lattice)]) for s_elem_source in s_ord_elements]))
            # glb_val_sym <= y
            assertions.append(Or([And(Equals(glb_val_sym, s_elem_source), le_vars[(s_elem_source, y_smt_lattice)]) for s_elem_source in s_ord_elements]))
            
            # GLB is greatest: for any z_glb, if z_glb <= x and z_glb <= y, then z_glb <= GLB(x,y)
            for z_smt_glb in s_ord_elements:
                z_glb_le_glb_consequent = Or([And(Equals(glb_val_sym, s_elem_target), le_vars[(z_smt_glb, s_elem_target)]) for s_elem_target in s_ord_elements])
                assertions.append(Implies(And(le_vars[(z_smt_glb, x_smt_lattice)], le_vars[(z_smt_glb, y_smt_lattice)]),
                                          z_glb_le_glb_consequent))

    print("\n--- Solving with SMT (Z3) for existence of Lattice with this PO ---")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()
        print(f"\nSMT Result for Test C-2 (Ω=3, Specific PO Lattice Check): {'SAT' if result else 'UNSAT'}")

        if result:
            print("  INTERPRETATION: SAT means the specific candidate PO CAN form a lattice")
            print("                  (i.e., LUBs/GLBs exist for all pairs satisfying the PO axioms).")
            model = s.get_model()
            print("  Lattice structure found. Join (LUB) and Meet (GLB) tables from model:")
            
            join_table_model: Dict[Tuple[int,int],int] = {}
            meet_table_model: Dict[Tuple[int,int],int] = {}
            for rk_py in py_keys_sord:
                for ck_py in py_keys_sord:
                    join_table_model[(rk_py,ck_py)] = model.get_value(join_table_vars[(rk_py,ck_py)]).constant_value()
                    meet_table_model[(rk_py,ck_py)] = model.get_value(meet_table_vars[(rk_py,ck_py)]).constant_value()
            
            print("\n  JOIN (LUB) Table (⊕̄):")
            print(op_to_str_c2(join_table_model, s_ord_py_map, "∨"))
            print("\n  MEET (GLB) Table (⊗̄):")
            print(op_to_str_c2(meet_table_model, s_ord_py_map, "∧"))
            print("\n  NOTE: Distributivity of these LUB/GLB operations is NOT YET CHECKED by this script.")
            print("        Further checks for distributivity and homomorphism to AVCA aspects would be needed.")

        else: # UNSAT
            print("  INTERPRETATION: UNSAT means the specific candidate PO CANNOT form a lattice under the given constraints,")
            print("                  or the PO definition itself was inconsistent with lattice axioms.")
            print("                  This would challenge C-2 if this was the only promising common monotonic PO.")

    print("\n====== Test_C2_SplitUnioLattice_Omega3.py Finished ======")
    print("NOTE: This script primarily tests LUB/GLB existence for a FIXED PO.")
    print("      A full test of C-2 needs robust distributivity checks and homomorphism to AVCA aspects.")

if __name__ == "__main__":
    run_C2_lattice_test_omega3()