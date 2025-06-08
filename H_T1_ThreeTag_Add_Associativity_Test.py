# H_T1_ThreeTag_Add_Associativity_Test_V3.py
# SMT PoC for H-T1: Define and Test associativity of a 3-tag AVCA addition
# where ZU is identity, DFI overflows yield MU, and other Unio-Unio
# additions resulting in Unio use a "lattice-max" rule for aspect.

from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff, Ite,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Union, Callable, List, Dict, Any, Tuple, Literal

# --- Global Omega ---
_Omega_py_H_T1_V3: int = 0 # Renamed for V3

# --- Symbolic AVCA Value Representation with 3 Unio Aspects ---
def create_symbolic_3tag_avc_val_V3(name_prefix: str) -> Dict[str, FNode]: # Renamed
    return {
        "is_finite": Symbol(f"{name_prefix}_is_finite_T1v3", SMT_BOOL_TYPE),
        "is_zu": Symbol(f"{name_prefix}_is_zu_T1v3", SMT_BOOL_TYPE), 
        "is_mu": Symbol(f"{name_prefix}_is_mu_T1v3", SMT_BOOL_TYPE), 
        "is_au": Symbol(f"{name_prefix}_is_au_T1v3", SMT_BOOL_TYPE), 
        "val": Symbol(f"{name_prefix}_val_T1v3", SMT_INT_TYPE), 
        "name": name_prefix
    }

def get_base_3tag_avc_constraints_V3(s: Dict[str, FNode], omega_smt: FNode, omega_py: int) -> List[FNode]: # Renamed
    constraints = [
        ExactlyOne(s["is_finite"], s["is_zu"], s["is_mu"], s["is_au"]),
        Implies(s["is_finite"], And(s["val"] >= Int(1), s["val"] < omega_smt)),
        Implies(Or(s["is_zu"], s["is_mu"], s["is_au"]), Equals(s["val"], Int(0)))
    ]
    if omega_py > 0 and omega_py == 1:
        constraints.append(Not(s["is_finite"]))
    return constraints

def avc_deep_equals_3tag_smt_V3(s1: Dict[str, FNode], s2: Dict[str, FNode]) -> FNode: # Renamed
    return And(Iff(s1["is_finite"], s2["is_finite"]),
               Iff(s1["is_zu"], s2["is_zu"]),
               Iff(s1["is_mu"], s2["is_mu"]),
               Iff(s1["is_au"], s2["is_au"]),
               Equals(s1["val"], s2["val"]))

def IsUnioSMT_3tag_V3(s: Dict[str, FNode]) -> FNode: # Renamed
    return Or(s["is_zu"], s["is_mu"], s["is_au"])

# Aspect Integer Mapping for Lattice-Max Rule (ZU < MU < AU)
ZERO_ASPECT_INT_T1_V3  = Int(0)
MIDDLE_ASPECT_INT_T1_V3 = Int(1)
AREO_ASPECT_INT_T1_V3  = Int(2)
DFI_EFFECTIVE_ASPECT_INT_T1_V3 = ZERO_ASPECT_INT_T1_V3 

def get_effective_aspect_int_3tag_V3(s: Dict[str, FNode]) -> FNode: # Renamed
    return Ite(s["is_finite"], DFI_EFFECTIVE_ASPECT_INT_T1_V3,
           Ite(s["is_zu"], ZERO_ASPECT_INT_T1_V3,
           Ite(s["is_mu"], MIDDLE_ASPECT_INT_T1_V3,
               AREO_ASPECT_INT_T1_V3)))

def MaxSMT_V3(val1: FNode, val2: FNode) -> FNode: # Renamed
    return Ite(val1 >= val2, val1, val2)

# --- 3-Tag AVCA Addition Logic Builder (⊕₃) ---
def avc_add_3tag_smt_logic_V3(a: Dict[str, FNode], b: Dict[str, FNode],
                              res: Dict[str, FNode], omega_smt: FNode) -> FNode: # Renamed
    
    res_is_zu_state = And(res["is_zu"], Not(res["is_mu"]), Not(res["is_au"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    res_is_mu_state = And(res["is_mu"], Not(res["is_zu"]), Not(res["is_au"]), Not(res["is_finite"]), Equals(res["val"], Int(0)))
    
    cond_a_is_zu = a["is_zu"]
    cond_b_is_zu = b["is_zu"]
    cond_a_is_mu = a["is_mu"]
    # cond_b_is_mu = b["is_mu"] # Not directly used in final logic structure this way
    cond_a_is_au = a["is_au"]
    # cond_b_is_au = b["is_au"] # Not directly used 
    cond_a_is_dfi = a["is_finite"]
    cond_b_is_dfi = b["is_finite"]

    cond_both_dfi = And(cond_a_is_dfi, cond_b_is_dfi) # DEFINED HERE

    sum_val_dfi_dfi = Plus(a["val"], b["val"])
    res_is_dfi_sum_val_state_with_val = And(res["is_finite"], Not(res["is_zu"]), Not(res["is_mu"]), Not(res["is_au"]),
                                   Equals(res["val"], sum_val_dfi_dfi))

    eff_aspect_a_int = get_effective_aspect_int_3tag_V3(a)
    eff_aspect_b_int = get_effective_aspect_int_3tag_V3(b)
    max_input_aspect_int = MaxSMT_V3(eff_aspect_a_int, eff_aspect_b_int)

    res_is_unio_with_max_aspect_state = And(
        IsUnioSMT_3tag_V3(res), Equals(res["val"], Int(0)), 
        Iff(res["is_zu"], Equals(max_input_aspect_int, ZERO_ASPECT_INT_T1_V3)),
        Iff(res["is_mu"], Equals(max_input_aspect_int, MIDDLE_ASPECT_INT_T1_V3)),
        Iff(res["is_au"], Equals(max_input_aspect_int, AREO_ASPECT_INT_T1_V3))
    )

    final_add_definition = \
    Ite(cond_a_is_zu, avc_deep_equals_3tag_smt_V3(res, b),                 
    Ite(cond_b_is_zu, avc_deep_equals_3tag_smt_V3(res, a),                 
    Ite(cond_both_dfi, 
        Ite(sum_val_dfi_dfi < omega_smt, 
            res_is_dfi_sum_val_state_with_val,                            
            res_is_mu_state),                                             
        Ite(And(Or(cond_a_is_mu, cond_a_is_au), cond_b_is_dfi), 
            avc_deep_equals_3tag_smt_V3(res,b),                           
        Ite(And(cond_a_is_dfi, Or(b["is_mu"], b["is_au"])),  # Corrected to b["is_mu"], b["is_au"]
            avc_deep_equals_3tag_smt_V3(res,a),                           
            res_is_unio_with_max_aspect_state                             
           )
          )
       )
      )
     )
    return final_add_definition

# --- SMT Test Function for H-T1 (Associativity of 3-tag Add) ---
def test_H_T1_3tag_add_associativity_V3(omega_py: int): # Renamed
    global _Omega_py_H_T1_V3 # Renamed
    _Omega_py_H_T1_V3 = omega_py
    omega_smt = Int(omega_py)

    print(f"\n--- Testing H-T1 (V3): Associativity of 3-Tag Addition for Omega={omega_py} ---")
    print(f"    Definition: ZU=id, DFI-Overflow=MU, U(nonZU)+U(nonZU)=U_MaxAspect")
    
    x = create_symbolic_3tag_avc_val_V3("x_T1v3") # Renamed
    y = create_symbolic_3tag_avc_val_V3("y_T1v3") # Renamed
    z = create_symbolic_3tag_avc_val_V3("z_T1v3") # Renamed

    solver = Solver(name="z3")
    for c in get_base_3tag_avc_constraints_V3(x, omega_smt, omega_py): solver.add_assertion(c)
    for c in get_base_3tag_avc_constraints_V3(y, omega_smt, omega_py): solver.add_assertion(c)
    for c in get_base_3tag_avc_constraints_V3(z, omega_smt, omega_py): solver.add_assertion(c)

    xy_add_3tag = create_symbolic_3tag_avc_val_V3("xy_add_T1v3") # Renamed
    for c in get_base_3tag_avc_constraints_V3(xy_add_3tag, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_add_3tag_smt_logic_V3(x, y, xy_add_3tag, omega_smt))
    
    lhs_3tag = create_symbolic_3tag_avc_val_V3("lhs_T1v3") # Renamed
    for c in get_base_3tag_avc_constraints_V3(lhs_3tag, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_add_3tag_smt_logic_V3(xy_add_3tag, z, lhs_3tag, omega_smt))

    yz_add_3tag = create_symbolic_3tag_avc_val_V3("yz_add_T1v3") # Renamed
    for c in get_base_3tag_avc_constraints_V3(yz_add_3tag, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_add_3tag_smt_logic_V3(y, z, yz_add_3tag, omega_smt))

    rhs_3tag = create_symbolic_3tag_avc_val_V3("rhs_T1v3") # Renamed
    for c in get_base_3tag_avc_constraints_V3(rhs_3tag, omega_smt, omega_py): solver.add_assertion(c)
    solver.add_assertion(avc_add_3tag_smt_logic_V3(x, yz_add_3tag, rhs_3tag, omega_smt))

    associativity_property = avc_deep_equals_3tag_smt_V3(lhs_3tag, rhs_3tag)

    solver.add_assertion(Not(associativity_property))

    print("  Solving for a counterexample to associativity of this 3-tag addition...")
    property_holds = False
    if not solver.solve():
        print("  RESULT: UNSAT. The defined 3-tag addition IS associative for this Omega.")
        property_holds = True
    else:
        print("  RESULT: SAT. The defined 3-tag addition is NOT associative. Counterexample:")
        model = solver.get_model()
        def pval_t1_V3(s_sym): # Renamed
            val_py = model.get_value(s_sym["val"]).constant_value()
            if model.get_value(s_sym["is_finite"]).is_true(): return f"Fp({val_py})"
            if model.get_value(s_sym["is_zu"]).is_true(): return "ZUo"
            if model.get_value(s_sym["is_mu"]).is_true(): return "MUo"
            if model.get_value(s_sym["is_au"]).is_true(): return "AUo"
            return f"Unknown({val_py})"

        print(f"    x = {pval_t1_V3(x)}")
        print(f"    y = {pval_t1_V3(y)}")
        print(f"    z = {pval_t1_V3(z)}")
        print(f"    (x⊕₃y) = {pval_t1_V3(xy_add_3tag)}")
        print(f"    (x⊕₃y)⊕₃z (LHS) = {pval_t1_V3(lhs_3tag)}")
        print(f"    (y⊕₃z) = {pval_t1_V3(yz_add_3tag)}")
        print(f"    x⊕₃(y⊕₃z) (RHS) = {pval_t1_V3(rhs_3tag)}")
        property_holds = False
    return property_holds

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script H_T1_ThreeTag_Add_Associativity_Test_V3: ======") # Renamed
    
    omega_to_test = 3 
    if omega_to_test <= 1:
        print(f"Omega={omega_to_test} is too small for interesting DFI interactions in this 3-tag test. Skipping.")
    else:
        print(f"\nSetting Python-side _Omega_py_H_T1_V3 = {omega_to_test}") # Renamed global
        add_3tag_is_associative = test_H_T1_3tag_add_associativity_V3(omega_to_test) # Renamed

        print("\n--- Summary of H-T1 (3-Tag Add Associativity Test V3) ---") # Renamed
        print(f"For Omega = {omega_to_test}:")
        if add_3tag_is_associative:
            print("  The defined 3-tag addition (ZU=id, DFI-overflow=MU, U(nonZU)+U(nonZU)=U_MaxAspect) IS associative.")
            print("  This is a POSITIVE step for H-T1, suggesting the 'lattice-max rule' with a middle tag might lead to well-behaved ops.")
        else:
            print("  The defined 3-tag addition IS NOT associative.")
            print("  This PoC indicates that this specific combination of ZU-identity, DFI-overflow-to-MU, and Max-aspect for other Unio sums")
            print("  does not automatically yield associativity for ⊕₃.")

    print("\n====== H_T1_ThreeTag_Add_Associativity_Test_V3 Script Finished ======") # Renamed