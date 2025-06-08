# Script R5.2: SMT Confirmation of DFI Additive Inverse Multiplicity - Corrected Call
# Mathematical Obligation: R5 from math LLM's refined deliverables.
# This SMT script aims to show:
# 1. Existence of multiple distinct DFI inverses for DFI a (a_val >= 2) when Ω >= 3.
# 2. Absence of multiple distinct DFI inverses for DFI a (a_val = 1) when Ω = 2.

from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, ForAll, Exists, Plus, Ite)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Literal

# --- Global Python Omega for SMT Context (used by get_base_avc_constraints_r5_2) ---
_Omega_py_r5_2: int = 0

# --- Symbolic Core AVCA Definitions (adapted from AVCA Core DraftV4 Appendix B) ---
def create_symbolic_avc_val_r5_2(name_prefix: str) -> Dict[str, Any]:
    """Creates symbolic components for an AVCVal."""
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints_r5_2(avc_repr: Dict[str, FNode], omega_smt_node: FNode) -> List[FNode]:
    """Basic constraints for a well-formed symbolic AVCVal for a given Omega."""
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))), 
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], omega_smt_node)) 
    ]
    global _Omega_py_r5_2
    if _Omega_py_r5_2 == 1: 
        constraints.append(Not(avc_repr["is_finite"])) 
    return constraints

def avc_add_smt_logic_r5_2(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    """
    SMT Logic for Core AVCA-Ω avc_add (⊕_v1.1: DFI overflow to AREO_UNIO object).
    """
    a_is_unio = Or(a["is_zero"], a["is_areo"])
    b_is_unio = Or(b["is_zero"], b["is_areo"])

    res_becomes_a_state = And(Iff(res["is_zero"], a["is_zero"]),
                              Iff(res["is_areo"], a["is_areo"]),
                              Iff(res["is_finite"], a["is_finite"]),
                              Equals(res["val"], a["val"]))
    
    res_becomes_b_state = And(Iff(res["is_zero"], b["is_zero"]),
                              Iff(res["is_areo"], b["is_areo"]),
                              Iff(res["is_finite"], b["is_finite"]),
                              Equals(res["val"], b["val"]))

    case1_a_is_unio = Implies(a_is_unio, res_becomes_b_state)
    case2_b_is_unio_a_is_dfi = Implies(And(Not(a_is_unio), b_is_unio), res_becomes_a_state)
    
    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    symbolic_sum_val = Plus(a["val"], b["val"]) 

    res_is_dfi_sum_state = And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                               Equals(res["val"], symbolic_sum_val))
    
    res_is_areo_unio_state = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]),
                                 Equals(res["val"], omega_smt_node))

    case3_dfi_dfi_logic = Implies(
        cond_both_are_dfi,
        Ite(symbolic_sum_val < omega_smt_node,   
            res_is_dfi_sum_state,                
            res_is_areo_unio_state               
        )
    )
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi_logic)

# --- SMT Test Function for Inverse Multiplicity ---
def test_dfi_inverse_multiplicity_smt(omega_val_py: int,
                                      condition_on_a_val_str: str,
                                      # Pass the SMT formula for the condition directly
                                      condition_on_a_val_formula: FNode, 
                                      expect_sat: bool): 
    """
    Tests for DFI inverse multiplicity using SMT.
    Asserts: exists DFI a, DFI x, DFI x_prime such that:
             x.val != x_prime.val (their DFI values are different)
             condition_on_a_val_formula holds for 'a'
             a + x ~ Unio
             a + x_prime ~ Unio
    """
    global _Omega_py_r5_2
    _Omega_py_r5_2 = omega_val_py

    print(f"\n--- SMT DFI Inverse Multiplicity Test for Ω = {omega_val_py} ---")
    print(f"Condition on a.val: {condition_on_a_val_str}")
    print(f"Expecting SAT (multiplicity exists): {expect_sat}")

    omega_smt_node = Int(omega_val_py)

    a = create_symbolic_avc_val_r5_2("a_cond") # Changed name to match usage in main
    x = create_symbolic_avc_val_r5_2("x")
    x_prime = create_symbolic_avc_val_r5_2("x_prime")
    res1 = create_symbolic_avc_val_r5_2("res1")
    res2 = create_symbolic_avc_val_r5_2("res2")

    assertions = []
    assertions.extend(get_base_avc_constraints_r5_2(a, omega_smt_node))
    assertions.extend(get_base_avc_constraints_r5_2(x, omega_smt_node))
    assertions.extend(get_base_avc_constraints_r5_2(x_prime, omega_smt_node))
    assertions.extend(get_base_avc_constraints_r5_2(res1, omega_smt_node))
    assertions.extend(get_base_avc_constraints_r5_2(res2, omega_smt_node))

    assertions.append(a["is_finite"])
    assertions.append(x["is_finite"])
    assertions.append(x_prime["is_finite"])
    
    # The condition_on_a_val_formula is now directly used.
    # It should be constructed using a['val'] from the 'a' defined in this function.
    assertions.append(condition_on_a_val_formula) 
    
    assertions.append(Not(Equals(x["val"], x_prime["val"]))) 
    assertions.append(avc_add_smt_logic_r5_2(a, x, res1, omega_smt_node))
    assertions.append(Or(res1["is_zero"], res1["is_areo"])) 
    assertions.append(avc_add_smt_logic_r5_2(a, x_prime, res2, omega_smt_node))
    assertions.append(Or(res2["is_zero"], res2["is_areo"])) 

    print("\nSolving with Z3...")
    with Solver(name="z3") as s:
        for an_assertion in assertions:
            s.add_assertion(an_assertion)
        
        result = s.solve()

        if result:
            print("Status: SAT")
            if expect_sat:
                print("  This is EXPECTED. Multiple distinct DFI inverses found for 'a' under the conditions.")
                model = s.get_model()
                print("  Witness (example):")
                # Use the correct 'a' symbol name used when creating the condition
                print(f"    a.val (for {a['name']}) = {model.get_value(a['val'])}") 
                print(f"    x.val = {model.get_value(x['val'])}")
                print(f"    x_prime.val = {model.get_value(x_prime['val'])}")
            else:
                print("  This is UNEXPECTED. Found multiple inverses where uniqueness was expected.")
                model = s.get_model()
                print("  Erroneous Witness (example):")
                print(f"    a.val (for {a['name']}) = {model.get_value(a['val'])}")
                print(f"    x.val = {model.get_value(x['val'])}")
                print(f"    x_prime.val = {model.get_value(x_prime['val'])}")
        else:
            print("Status: UNSAT")
            if not expect_sat:
                print("  This is EXPECTED. No multiple distinct DFI inverses found under these conditions (implies uniqueness).")
            else:
                print("  This is UNEXPECTED. Expected to find multiple inverses but found none (implies no such 'a' exists or problem with logic).")
    print("-" * 70)

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script R5.2: SMT Confirmation of DFI Additive Inverse Multiplicity (for ⊕_v1.1) ======")
    print("\n--- Testing Scenarios for Inverse Multiplicity ---")

    # Define the symbolic 'a' once for use in lambdas, or pass the name and reconstruct.
    # Simpler: Create the condition formula using the name that will be used inside the test function.
    # The 'a' inside test_dfi_inverse_multiplicity_smt is created with name "a_cond".
    
    # Case 1: Ω = 2 (DFI = {1})
    print("\nTesting Ω = 2")
    # For Omega=2, DFI is {1}. It's impossible to find two *distinct* DFI x and x_prime.
    # The constraints x["is_finite"], x_prime["is_finite"], Not(Equals(x["val"], x_prime["val"])),
    # plus DFI range constraints (1 <= val < 2), will make the problem UNSAT.
    # So, expect_sat should be False, indicating multiplicity is not found.
    a_for_cond_o2 = create_symbolic_avc_val_r5_2("a_cond") # Name matches internal 'a'
    test_dfi_inverse_multiplicity_smt(
        omega_val_py=2,
        condition_on_a_val_str="a.val = 1",
        condition_on_a_val_formula=Equals(a_for_cond_o2["val"], Int(1)),
        expect_sat=False 
    )

    # Case 2: Ω = 3 (DFI = {1, 2})
    # For a.val = 2, expect multiplicity (SAT).
    a_for_cond_o3 = create_symbolic_avc_val_r5_2("a_cond")
    test_dfi_inverse_multiplicity_smt(
        omega_val_py=3,
        condition_on_a_val_str="a.val = 2",
        condition_on_a_val_formula=Equals(a_for_cond_o3["val"], Int(2)),
        expect_sat=True
    )

    # Case 3: Ω = 4 (DFI = {1, 2, 3})
    a_for_cond_o4_val2 = create_symbolic_avc_val_r5_2("a_cond")
    test_dfi_inverse_multiplicity_smt(
        omega_val_py=4,
        condition_on_a_val_str="a.val = 2",
        condition_on_a_val_formula=Equals(a_for_cond_o4_val2["val"], Int(2)),
        expect_sat=True
    )
    a_for_cond_o4_val3 = create_symbolic_avc_val_r5_2("a_cond")
    test_dfi_inverse_multiplicity_smt(
        omega_val_py=4,
        condition_on_a_val_str="a.val = 3",
        condition_on_a_val_formula=Equals(a_for_cond_o4_val3["val"], Int(3)),
        expect_sat=True
    )
    
    # Case 4: Ω = 5 (DFI = {1, 2, 3, 4})
    a_for_cond_o5_val1 = create_symbolic_avc_val_r5_2("a_cond")
    test_dfi_inverse_multiplicity_smt(
        omega_val_py=5,
        condition_on_a_val_str="a.val = 1",
        condition_on_a_val_formula=Equals(a_for_cond_o5_val1["val"], Int(1)),
        expect_sat=False
    )
    a_for_cond_o5_val2 = create_symbolic_avc_val_r5_2("a_cond")
    test_dfi_inverse_multiplicity_smt(
        omega_val_py=5,
        condition_on_a_val_str="a.val = 2",
        condition_on_a_val_formula=Equals(a_for_cond_o5_val2["val"], Int(2)),
        expect_sat=True
    )

    print("\n====== R5.2 Script Finished ======")