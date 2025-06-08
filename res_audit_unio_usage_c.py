import re
import itertools
import math
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- PySMT Imports ---
try:
    from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                                 ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals)
    from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
    from pysmt.fnode import FNode
    SMT_MODE_AVAILABLE = True
except ImportError:
    SMT_MODE_AVAILABLE = False
    # Print warning during SMT test execution

# --- Configuration ---
SMT_SOLVER_NAME = "z3"

# --- Suite 1.C.ii: New Unio Class Definition (Collapsed, No Aspect Information) ---
class Unio_Collapsed:
    """
    Represents the unified Unio pole for Suite 1.C.ii.
    A single, undifferentiated Unio object with no readable aspect.
    All instances (though we only use one canonical) are algebraically equivalent.
    """
    __slots__ = () # No aspect attribute

    def __eq__(self, other: object) -> bool:
        """All Unio_Collapsed instances are algebraically equivalent."""
        return isinstance(other, Unio_Collapsed)

    def __hash__(self) -> int:
        """All Unio_Collapsed instances hash to the same value."""
        return hash(type(self))

    def __repr__(self) -> str:
        return "U_SINGLE"

# Canonical single instance for Suite 1.C.ii
U_SINGLE = Unio_Collapsed()

# Type Alias for this variant
AVCVal_1Cii = Union[int, Unio_Collapsed]

# --- AVCA Core Logic Adapted for Suite 1.C.ii (using Unio_Collapsed) ---
Omega_1Cii: int = 0

def set_avca_omega_1Cii(omega_value: int, verbose=False):
    global Omega_1Cii
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_1Cii parameter must be an integer >= 1.")
    Omega_1Cii = omega_value
    if verbose:
        print(f"Suite 1.C.ii: Omega_1Cii set to {Omega_1Cii}")

def _check_val_1Cii(x: AVCVal_1Cii, current_omega: int, op_name: str = "operation"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega_1Cii parameter for {op_name} must be an integer >= 1. Got: {current_omega!r}")
    if isinstance(x, Unio_Collapsed):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value in {op_name}: {x!r}. Expected int (for DFI) or Unio_Collapsed. Got type: {type(x)}.")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI Value for {op_name} with Omega_1Cii=1: {x}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value for {op_name}: {x}. For Omega_1Cii={current_omega}, DFI integers must be in range [1, {current_omega - 1}].")

def avc_add_1Cii(a: AVCVal_1Cii, b: AVCVal_1Cii) -> AVCVal_1Cii:
    global Omega_1Cii
    if Omega_1Cii == 0: raise ValueError("Global Omega_1Cii not set for avc_add_1Cii.")
    _check_val_1Cii(a, Omega_1Cii, "avc_add_1Cii(a)")
    _check_val_1Cii(b, Omega_1Cii, "avc_add_1Cii(b)")
    if isinstance(a, Unio_Collapsed): return b
    if isinstance(b, Unio_Collapsed): return a
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < Omega_1Cii else U_SINGLE # Output is U_SINGLE

def avc_sub_1Cii(a: AVCVal_1Cii, b: AVCVal_1Cii) -> AVCVal_1Cii:
    global Omega_1Cii
    if Omega_1Cii == 0: raise ValueError("Global Omega_1Cii not set for avc_sub_1Cii.")
    _check_val_1Cii(a, Omega_1Cii, "avc_sub_1Cii(a)")
    _check_val_1Cii(b, Omega_1Cii, "avc_sub_1Cii(b)")
    if isinstance(b, Unio_Collapsed): return a
    if isinstance(a, Unio_Collapsed): return U_SINGLE # Output is U_SINGLE
    if a > b: return a - b # type: ignore
    else: return U_SINGLE # Output is U_SINGLE

def avc_mul_1Cii(a: AVCVal_1Cii, b: AVCVal_1Cii) -> AVCVal_1Cii:
    global Omega_1Cii
    if Omega_1Cii == 0: raise ValueError("Global Omega_1Cii not set for avc_mul_1Cii.")
    _check_val_1Cii(a, Omega_1Cii, "avc_mul_1Cii(a)")
    _check_val_1Cii(b, Omega_1Cii, "avc_mul_1Cii(b)")
    a_is_unio = isinstance(a, Unio_Collapsed)
    b_is_unio = isinstance(b, Unio_Collapsed)
    if a_is_unio or b_is_unio:
        # Aspect reading logic is removed/bypassed. If algebraic result is Unio, it's U_SINGLE.
        # The v1.2 logic: "AREO_UNIO if any Unio operand is Areo-aspected, else ZERO_UNIO"
        # Since aspects are collapsed, this distinction for output is lost.
        # If any input is U_SINGLE, the result is U_SINGLE (as Unio is absorbing/annihilating in mul).
        return U_SINGLE
    else: # Both DFI
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < Omega_1Cii else U_SINGLE # Output is U_SINGLE

def avc_div_1Cii(a: AVCVal_1Cii, b: AVCVal_1Cii) -> AVCVal_1Cii:
    global Omega_1Cii
    if Omega_1Cii == 0: raise ValueError("Global Omega_1Cii not set for avc_div_1Cii.")
    _check_val_1Cii(a, Omega_1Cii, "avc_div_1Cii(a)")
    _check_val_1Cii(b, Omega_1Cii, "avc_div_1Cii(b)")
    if isinstance(b, Unio_Collapsed): return U_SINGLE # Divisor Unio -> U_SINGLE
    if isinstance(a, Unio_Collapsed): # Dividend Unio, Divisor DFI
        # Aspect preservation logic is removed. Result is U_SINGLE.
        return U_SINGLE
    # Both DFI
    a_val: int = a # type: ignore
    b_val: int = b # type: ignore
    if b_val == 0:
         raise ValueError("Division by DFI zero attempted in avc_div_1Cii logic - should not happen.")
    quotient, remainder = divmod(a_val, b_val)
    return quotient if remainder == 0 and (1 <= quotient < Omega_1Cii) else U_SINGLE # Output is U_SINGLE

# --- Native Python Test Harness ---
native_test_summary_1Cii = {}

def run_native_test_1Cii(test_name: str, omega_val: int, test_func: Callable, expect_fail: bool = False, failure_is_skip: bool = False):
    global native_test_summary_1Cii
    set_avca_omega_1Cii(omega_val)
    if omega_val not in native_test_summary_1Cii:
        native_test_summary_1Cii[omega_val] = {"passed": 0, "failed": 0, "skipped": 0}
    
    print(f"  NATIVE Test (1Cii): '{test_name}' for Ω={omega_val} (Expect: {'Fails' if expect_fail else 'Holds'})", end=" ... ")
    try:
        result, counterexample = test_func(omega_val)
        passes = (result and not expect_fail) or (not result and expect_fail)
        
        if passes:
            print("PASS")
            native_test_summary_1Cii[omega_val]["passed"] += 1
        else:
            print(f"FAIL (Observed: {'Holds' if result else 'Fails'})")
            if counterexample:
                print(f"    Counterexample: {counterexample}")
            native_test_summary_1Cii[omega_val]["failed"] += 1
    except Exception as e:
        if failure_is_skip:
            print(f"SKIPPED ({e})")
            native_test_summary_1Cii[omega_val]["skipped"] +=1
        else:
            print(f"ERROR ({e})")
            native_test_summary_1Cii[omega_val]["failed"] += 1

def get_s_omega_1Cii(current_omega: int) -> List[AVCVal_1Cii]:
    if current_omega == 1: return [U_SINGLE]
    return [U_SINGLE] + list(range(1, current_omega))

# Native Test Functions (using _1Cii operations)
def native_test_totality_op_1Cii(omega_val: int, op_func: Callable) -> Tuple[bool, Any]:
    elements = get_s_omega_1Cii(omega_val)
    for a in elements:
        for b in elements:
            try:
                res = op_func(a,b)
                _check_val_1Cii(res, omega_val)
            except Exception as e:
                return False, f"Error for {a!r} op {b!r}: {e}"
    return True, None

def native_test_commutativity_add_1Cii(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Cii(omega_val)
    for a in elements:
        for b in elements:
            if avc_add_1Cii(a,b) != avc_add_1Cii(b,a):
                return False, f"a={a!r}, b={b!r}"
    return True, None

def native_test_associativity_add_1Cii(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Cii(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                lhs = avc_add_1Cii(avc_add_1Cii(a,b),c)
                rhs = avc_add_1Cii(a,avc_add_1Cii(b,c))
                if lhs != rhs:
                    return False, f"a={a!r}, b={b!r}, c={c!r} -> LHS={lhs!r}, RHS={rhs!r}"
    return True, None

def native_test_commutativity_mul_1Cii(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Cii(omega_val)
    for a in elements:
        for b in elements:
            if avc_mul_1Cii(a,b) != avc_mul_1Cii(b,a):
                return False, f"a={a!r}, b={b!r}"
    return True, None

def native_test_associativity_mul_1Cii(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Cii(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                lhs = avc_mul_1Cii(avc_mul_1Cii(a,b),c)
                rhs = avc_mul_1Cii(a,avc_mul_1Cii(b,c))
                if lhs != rhs:
                    return False, f"a={a!r}, b={b!r}, c={c!r} -> LHS={lhs!r}, RHS={rhs!r}"
    return True, None
    
def native_test_distributivity_mul_over_add_1Cii(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Cii(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                b_plus_c = avc_add_1Cii(b, c)
                lhs = avc_mul_1Cii(a, b_plus_c)
                a_mul_b = avc_mul_1Cii(a, b)
                a_mul_c = avc_mul_1Cii(a, c)
                rhs = avc_add_1Cii(a_mul_b, a_mul_c)
                if lhs != rhs:
                    return False, f"a={a!r}, b={b!r}, c={c!r} -> a(b+c)={lhs!r}, (ab)+(ac)={rhs!r}"
    return True, None

# --- SMT Harness Components (Embedded) ---
smt_test_summary_1Cii = {}

# Symbolic representation for Unio_Collapsed (no distinct aspects)
def create_symbolic_avc_val_1Cii(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_unio": Symbol(f"{name_prefix}_is_U", SMT_BOOL_TYPE), # True if U_SINGLE
        "is_finite": Symbol(f"{name_prefix}_is_F", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE), # DFI value, or convention for U_SINGLE (e.g., 0)
        "name": name_prefix
    }

def get_base_avc_constraints_1Cii(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    constraints = [
        Iff(avc_repr["is_unio"], Not(avc_repr["is_finite"])),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_unio"], Equals(avc_repr["val"], Int(0))) # U_SINGLE convention value = 0
    ]
    if current_omega_py == 1:
        constraints.append(avc_repr["is_unio"]) # Must be Unio if Omega=1
    return constraints

def avc_equiv_smt_1Cii(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    both_unio = And(avc1["is_unio"], avc2["is_unio"])
    both_dfi_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_dfi_equal_val)

# SMT Logic Builders (Modeling the _1Cii operations)
def avc_add_smt_logic_1Cii(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> FNode:
    res_becomes_a_state = And(Iff(res["is_unio"], a["is_unio"]), Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"]))
    res_becomes_b_state = And(Iff(res["is_unio"], b["is_unio"]), Iff(res["is_finite"], b["is_finite"]), Equals(res["val"], b["val"]))
    
    case1_a_is_unio = Implies(a["is_unio"], res_becomes_b_state)
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b["is_unio"]), res_becomes_a_state)
    
    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    symbolic_sum_val = Plus(a["val"], b["val"])
    
    res_is_dfi_sum_state = And(res["is_finite"], Not(res["is_unio"]), Equals(res["val"], symbolic_sum_val))
    res_is_U_SINGLE_state = And(res["is_unio"], Not(res["is_finite"]), Equals(res["val"], Int(0))) # U_SINGLE val = 0
    
    case3_dfi_dfi_logic = Implies(cond_both_are_dfi, 
                                  Ite(symbolic_sum_val < omega_smt_node,
                                      res_is_dfi_sum_state,
                                      res_is_U_SINGLE_state))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi_logic)

def avc_mul_smt_logic_1Cii(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> FNode:
    # With U_SINGLE, if any input is Unio, or DFI*DFI overflows, result is U_SINGLE.
    res_is_U_SINGLE_state = And(res["is_unio"], Not(res["is_finite"]), Equals(res["val"], Int(0)))
    
    unio_case_behavior = res_is_U_SINGLE_state # Simpler: if unio involved, result is U_SINGLE

    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    prod_val = a["val"] * b["val"]
    res_is_FP_prod_formula = And(res["is_finite"], Not(res["is_unio"]), Equals(res["val"], prod_val))
    dfi_case_behavior = Ite(And(prod_val >= Int(1), prod_val < omega_smt_node),
                            res_is_FP_prod_formula,
                            res_is_U_SINGLE_state) # DFI overflow to U_SINGLE
    
    return Ite(Or(a["is_unio"], b["is_unio"]), unio_case_behavior, dfi_case_behavior)

def prove_or_find_counterexample_smt_1Cii( # Copied and renamed from Suite 1.B
    property_name: str, omega_py_val: int, setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    
    global smt_test_summary_1Cii
    
    if not SMT_MODE_AVAILABLE:
        print(f"SKIPPED (SMT Mode Unavailable) for {property_name} Ω={omega_py_val}")
        if omega_py_val not in smt_test_summary_1Cii:
            smt_test_summary_1Cii[omega_py_val] = {"passed": 0, "failed": 0, "skipped": 0}
        smt_test_summary_1Cii[omega_py_val]["skipped"] += 1
        return

    if omega_py_val not in smt_test_summary_1Cii:
        smt_test_summary_1Cii[omega_py_val] = {"passed": 0, "failed": 0, "skipped": 0}

    print(f"  SMT Test (1Cii): '{property_name}' for Ω={omega_py_val} (Expect: {'Hold/Exist' if expect_property_to_hold else 'Fail/Not Exist'})", end=" ... ")
    
    property_holds_observed = False; counterexample_witness_str = None
    try:
        with Solver(name=SMT_SOLVER_NAME, logic="LIA") as s:
            for f_setup in setup_formulas: s.add_assertion(f_setup)
            formula_to_check = Not(property_to_verify) if not is_existential else property_to_verify
            if s.solve([formula_to_check]):
                if is_existential: property_holds_observed = True
                else: property_holds_observed = False # Counterexample found
                model = s.get_model(); ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_u = model.get_value(repr_dict['is_unio']).is_true()
                        val_smt = model.get_value(repr_dict['val'])
                        state_str = "U_S" if is_u else f"Fp({val_smt})"
                        ce_parts.append(f"{name}={state_str}")
                    except Exception: ce_parts.append(f"{name}=?")
                counterexample_witness_str = "; ".join(ce_parts)
            else: # UNSAT
                if is_existential: property_holds_observed = False
                else: property_holds_observed = True # Property holds universally
        
        success_for_summary = (property_holds_observed == expect_property_to_hold)
        if success_for_summary:
            print("PASS")
            smt_test_summary_1Cii[omega_py_val]["passed"] += 1
            if counterexample_witness_str and is_existential and expect_property_to_hold: print(f"    Witness (as expected): {counterexample_witness_str}")
            elif counterexample_witness_str and not is_existential and not expect_property_to_hold: print(f"    Counterexample (as expected for failure): {counterexample_witness_str}")
        else:
            print(f"FAIL (Observed: {'Holds/Exists' if property_holds_observed else 'Fails/Not Exist'})")
            smt_test_summary_1Cii[omega_py_val]["failed"] += 1
            if counterexample_witness_str:
                 label = "Unexpected Witness" if is_existential and property_holds_observed else \
                         "Counterexample (property unexpectedly failed)" if not is_existential and not property_holds_observed else \
                         "Witness NOT Found (but was expected)" if is_existential and not property_holds_observed else \
                         "No Counterexample Found (property unexpectedly held)"
                 print(f"    {label}: {counterexample_witness_str if counterexample_witness_str else '(No model value for fail condition)'}")
            elif not property_holds_observed and expect_property_to_hold and is_existential: # No witness, but expected one
                 print(f"    Witness NOT Found (but was expected)")
            elif property_holds_observed and not expect_property_to_hold and not is_existential: # Held, but expected fail (no CE)
                 print(f"    No Counterexample Found (property unexpectedly held)")

    except Exception as e:
        print(f"ERROR ({e})")
        smt_test_summary_1Cii[omega_py_val]["failed"] += 1

# SMT Test Functions (adapted for _1Cii)
def smt_test_A1_totality_add_1Cii(omega_val_py: int):
    property_name = "SMT A.1: Totality for avc_add_1Cii"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val_1Cii("a_totA"); b = create_symbolic_avc_val_1Cii("b_totA"); res = create_symbolic_avc_val_1Cii("res_totA")
    setup = get_base_avc_constraints_1Cii(a, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints_1Cii(b, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints_1Cii(res, omega_smt_node, omega_val_py)
    setup.append(avc_add_smt_logic_1Cii(a,b,res,omega_smt_node, omega_val_py))
    prove_or_find_counterexample_smt_1Cii(property_name, omega_val_py, setup, TRUE(), [a,b,res], True)

def smt_test_A2_well_definedness_add_1Cii(omega_val_py: int): # Unio_Collapsed has only one representation, so this is simpler
    property_name = "SMT A.2: Well-Definedness for avc_add_1Cii"
    # This test is somewhat trivial now as there's only U_SINGLE, but it checks consistency.
    # If we were to make U_SINGLE by different paths, they should still be equiv.
    # The original well-definedness was about Unio("zero") vs Unio("areo") as inputs.
    # Here, any two Unio_Collapsed objects are equal.
    # Let's reuse the structure but it should trivially pass.
    omega_smt_node = Int(omega_val_py)
    a1 = create_symbolic_avc_val_1Cii("a1_wdA"); a2 = create_symbolic_avc_val_1Cii("a2_wdA")
    b1 = create_symbolic_avc_val_1Cii("b1_wdA"); b2 = create_symbolic_avc_val_1Cii("b2_wdA")
    res1 = create_symbolic_avc_val_1Cii("res1_wdA"); res2 = create_symbolic_avc_val_1Cii("res2_wdA")
    setup = get_base_avc_constraints_1Cii(a1, omega_smt_node, omega_val_py) + get_base_avc_constraints_1Cii(a2, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints_1Cii(b1, omega_smt_node, omega_val_py) + get_base_avc_constraints_1Cii(b2, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints_1Cii(res1, omega_smt_node, omega_val_py) + get_base_avc_constraints_1Cii(res2, omega_smt_node, omega_val_py)
    premises = And(avc_equiv_smt_1Cii(a1,a2), avc_equiv_smt_1Cii(b1,b2)) # if inputs are algebraically same
    setup.append(avc_add_smt_logic_1Cii(a1,b1,res1,omega_smt_node, omega_val_py))
    setup.append(avc_add_smt_logic_1Cii(a2,b2,res2,omega_smt_node, omega_val_py))
    property_formula = Implies(premises, avc_equiv_smt_1Cii(res1, res2)) # then outputs must be
    prove_or_find_counterexample_smt_1Cii(property_name, omega_val_py, setup, property_formula, [a1,a2,b1,b2], True)


def smt_test_associativity_add_1Cii(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Associativity of avc_add_1Cii (Expect: {'Holds' if expected_to_hold else 'Fails'})"
    omega_smt_node = Int(omega_val_py)
    a=create_symbolic_avc_val_1Cii("aA");b=create_symbolic_avc_val_1Cii("bA");c=create_symbolic_avc_val_1Cii("cA")
    ab=create_symbolic_avc_val_1Cii("abA");lhs=create_symbolic_avc_val_1Cii("lhsA")
    bc=create_symbolic_avc_val_1Cii("bcA");rhs=create_symbolic_avc_val_1Cii("rhsA")
    setup = get_base_avc_constraints_1Cii(a,omega_smt_node,omega_val_py) + get_base_avc_constraints_1Cii(b,omega_smt_node,omega_val_py) + \
            get_base_avc_constraints_1Cii(c,omega_smt_node,omega_val_py) + get_base_avc_constraints_1Cii(ab,omega_smt_node,omega_val_py) + \
            get_base_avc_constraints_1Cii(lhs,omega_smt_node,omega_val_py) + get_base_avc_constraints_1Cii(bc,omega_smt_node,omega_val_py) + \
            get_base_avc_constraints_1Cii(rhs,omega_smt_node,omega_val_py)
    setup.append(avc_add_smt_logic_1Cii(a,b,ab,omega_smt_node,omega_val_py))
    setup.append(avc_add_smt_logic_1Cii(ab,c,lhs,omega_smt_node,omega_val_py))
    setup.append(avc_add_smt_logic_1Cii(b,c,bc,omega_smt_node,omega_val_py))
    setup.append(avc_add_smt_logic_1Cii(a,bc,rhs,omega_smt_node,omega_val_py))
    property_formula = avc_equiv_smt_1Cii(lhs,rhs)
    prove_or_find_counterexample_smt_1Cii(property_name, omega_val_py, setup, property_formula, [a,b,c], expected_to_hold)

def smt_test_distributivity_mul_over_add_1Cii(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Left Distributivity (avc_mul_1Cii over avc_add_1Cii) (Expect: {'Holds' if expected_to_hold else 'Fails'})"
    omega_smt_node = Int(omega_val_py)
    a=create_symbolic_avc_val_1Cii("aD"); b=create_symbolic_avc_val_1Cii("bD"); c=create_symbolic_avc_val_1Cii("cD")
    bpc=create_symbolic_avc_val_1Cii("bpcD"); lhs=create_symbolic_avc_val_1Cii("lhsD")
    ab=create_symbolic_avc_val_1Cii("abD"); ac=create_symbolic_avc_val_1Cii("acD"); rhs=create_symbolic_avc_val_1Cii("rhsD")
    setup = get_base_avc_constraints_1Cii(a,omega_smt_node,omega_val_py) + get_base_avc_constraints_1Cii(b,omega_smt_node,omega_val_py) + \
            get_base_avc_constraints_1Cii(c,omega_smt_node,omega_val_py) + get_base_avc_constraints_1Cii(bpc,omega_smt_node,omega_val_py) + \
            get_base_avc_constraints_1Cii(lhs,omega_smt_node,omega_val_py) + get_base_avc_constraints_1Cii(ab,omega_smt_node,omega_val_py) + \
            get_base_avc_constraints_1Cii(ac,omega_smt_node,omega_val_py) + get_base_avc_constraints_1Cii(rhs,omega_smt_node,omega_val_py)
    setup.append(avc_add_smt_logic_1Cii(b,c,bpc,omega_smt_node,omega_val_py))
    setup.append(avc_mul_smt_logic_1Cii(a,bpc,lhs,omega_smt_node,omega_val_py))
    setup.append(avc_mul_smt_logic_1Cii(a,b,ab,omega_smt_node,omega_val_py))
    setup.append(avc_mul_smt_logic_1Cii(a,c,ac,omega_smt_node,omega_val_py))
    setup.append(avc_add_smt_logic_1Cii(ab,ac,rhs,omega_smt_node,omega_val_py))
    property_formula = avc_equiv_smt_1Cii(lhs,rhs)
    prove_or_find_counterexample_smt_1Cii(property_name, omega_val_py, setup, property_formula, [a,b,c], expected_to_hold)

# Specific SMT test for aspect behavior (expected to change/fail)
def smt_test_mul_aspect_1Cii(omega_val_py: int):
    # Original test was: U_AREO_REP * DFI_k = U_AREO_REP
    # In 1Cii, all Unio results are U_SINGLE. So, U_SINGLE * DFI_k = U_SINGLE.
    # This property holds by definition of avc_mul_1Cii.
    # The *failure* will be seen if we compare against a specific *aspect* expectation.
    # Let's test if (Symbolic U_SINGLE from Areo-context-input) * DFI_k == (Symbolic U_SINGLE defined as Areo-aspect)
    # This is tricky because U_SINGLE has no aspect.
    # Instead, let's test if the system can still *distinguish* an Areo-like mul outcome from a Zero-like one.
    # Test: (Symbolic Unio that *would have been* Areo) * DFI == U_SINGLE
    # Test: (Symbolic Unio that *would have been* Zero) * DFI == U_SINGLE
    # This doesn't show much new.
    # The key is that the previous test "SMT Mul Aspect: U_AREO_REP * DFI_k = U_AREO_REP"
    # from Suite 1.B *cannot be meaningfully formulated* here if U_AREO_REP is just U_SINGLE.
    # If we formulate it as: (Symbolic U_SINGLE) * DFI_k = (Symbolic U_SINGLE representing original AREO),
    # it will pass if results are U_SINGLE.
    # What fails is the ability to say the result is *specifically AREO-aspected*.

    # For this suite, let's just confirm a Unio * DFI results in Unio.
    property_name = f"SMT Mul U_SINGLE * DFI_k = U_SINGLE"
    omega_smt = Int(omega_val_py)
    u_single_sym = create_symbolic_avc_val_1Cii("uS") # Represents U_SINGLE input
    dfi_k_sym = create_symbolic_avc_val_1Cii("dfiK")
    res_mul_sym = create_symbolic_avc_val_1Cii("resMul")
    
    setup = get_base_avc_constraints_1Cii(u_single_sym, omega_smt, omega_val_py) + \
            get_base_avc_constraints_1Cii(dfi_k_sym, omega_smt, omega_val_py) + \
            get_base_avc_constraints_1Cii(res_mul_sym, omega_smt, omega_val_py)
    setup.extend([
        u_single_sym["is_unio"],   # u_single_sym is U_SINGLE
        dfi_k_sym["is_finite"] # dfi_k_sym is DFI
    ])
    if omega_val_py == 1:
         prove_or_find_counterexample_smt_1Cii(property_name + " (SKIPPED DFI N/A)", omega_val_py, [], TRUE(), [], True)
    else:
        setup.append(avc_mul_smt_logic_1Cii(u_single_sym, dfi_k_sym, res_mul_sym, omega_smt, omega_val_py))
        # Property: result must be U_SINGLE (i.e., is_unio and val=0 by convention)
        property_formula = res_mul_sym["is_unio"]
        prove_or_find_counterexample_smt_1Cii(property_name, omega_val_py, setup, property_formula, [u_single_sym, dfi_k_sym], True)


# Main execution block
if __name__ == "__main__":
    print("====== AVCA Suite 1.C.ii: Unio_Collapsed (Uniform Output Aspect) ======")
    omegas_for_native = [1, 2, 3, 4]
    omegas_for_smt = [1, 2, 3, 5]

    print("\n--- Running Native Python Tests for Suite 1.C.ii ---")
    for omega_test in omegas_for_native:
        print(f"\n-- Native Tests for Ω = {omega_test} --")
        run_native_test_1Cii(f"Operational Totality for avc_add_1Cii", omega_test, lambda o: native_test_totality_op_1Cii(o, avc_add_1Cii))
        run_native_test_1Cii(f"Operational Totality for avc_sub_1Cii", omega_test, lambda o: native_test_totality_op_1Cii(o, avc_sub_1Cii))
        run_native_test_1Cii(f"Operational Totality for avc_mul_1Cii", omega_test, lambda o: native_test_totality_op_1Cii(o, avc_mul_1Cii))
        run_native_test_1Cii(f"Operational Totality for avc_div_1Cii", omega_test, lambda o: native_test_totality_op_1Cii(o, avc_div_1Cii))
        
        run_native_test_1Cii("Commutativity of avc_add_1Cii", omega_test, native_test_commutativity_add_1Cii)
        run_native_test_1Cii("Associativity of avc_add_1Cii", omega_test, native_test_associativity_add_1Cii, expect_fail=(omega_test > 2))
        
        run_native_test_1Cii("Commutativity of avc_mul_1Cii", omega_test, native_test_commutativity_mul_1Cii)
        run_native_test_1Cii("Associativity of avc_mul_1Cii", omega_test, native_test_associativity_mul_1Cii, expect_fail=False)
        
        run_native_test_1Cii("Left Distributivity (avc_mul_1Cii over avc_add_1Cii)", omega_test, native_test_distributivity_mul_over_add_1Cii, expect_fail=(omega_test > 2))

    print("\n--- Native Python Test Summary (Suite 1.C.ii) ---")
    for o, res in sorted(native_test_summary_1Cii.items()):
        print(f"  Ω={o}: Passed={res['passed']}, Failed={res['failed']}, Skipped={res['skipped']}")
    
    if SMT_MODE_AVAILABLE:
        print("\n\n--- Running SMT-based Tests for Suite 1.C.ii ---")
        for omega_test in omegas_for_smt:
            print(f"\n-- SMT Tests for Ω = {omega_test} --")
            smt_test_A1_totality_add_1Cii(omega_test)
            smt_test_A2_well_definedness_add_1Cii(omega_test) # Should be trivial now
            smt_test_associativity_add_1Cii(omega_test)
            smt_test_distributivity_mul_over_add_1Cii(omega_test)
            smt_test_mul_aspect_1Cii(omega_test) # This test now just checks U*DFI=U
            
            # Example of a test that *would have passed* in 1.B but *should fail* here
            # if "failure" means not matching the specific aspect outcome of v1.2b.
            # Let's test: Does (Symbolic AREO input `sa`) * (DFI `sb`) result in symbolic AREO output?
            # In this 1Cii system, it should result in U_SINGLE (val=0), not AREO (val=Omega).
            if omega_test > 1: # Need DFI
                prop_name_areo_mul_fail = f"SMT v1.2b Areo-Mul output check (Expect Fail)"
                omega_smt_node = Int(omega_test)
                sa = create_symbolic_avc_val_1Cii("sa_amf") # represents an input that would have been AREO_UNIO
                sb = create_symbolic_avc_val_1Cii("sb_amf") # represents a DFI
                res = create_symbolic_avc_val_1Cii("res_amf")
                
                setup = get_base_avc_constraints_1Cii(sa, omega_smt_node, omega_test) + \
                        get_base_avc_constraints_1Cii(sb, omega_smt_node, omega_test) + \
                        get_base_avc_constraints_1Cii(res, omega_smt_node, omega_test)
                setup.extend([
                    sa["is_unio"], # sa is Unio
                    # In 1Cii, we can't say sa "is Areo aspect". It's just U_SINGLE.
                    # The SMT model of avc_mul_1Cii also doesn't read input aspects.
                    # So this test needs rethinking for 1Cii.
                    # The SMT builder for avc_mul_1Cii does not differentiate input Unio aspects.
                    # What we can test is if the *original* aspect-dependent logic would still hold
                    # if it were applied to the output.
                    # For avc_mul_1Cii, U_SINGLE * DFI -> U_SINGLE (val=0).
                    # The original v1.2b AREO_UNIO * DFI -> AREO_UNIO (val=Omega).
                    # So, we test if U_SINGLE * DFI (which is U_SINGLE, val=0) equals a symbolic AREO (val=Omega).
                    # This should FAIL.
                    sb["is_finite"] 
                ])
                setup.append(avc_mul_smt_logic_1Cii(sa, sb, res, omega_smt_node, omega_test))
                
                # Property: Does res (which should be U_SINGLE, val=0) equal a symbolic AREO_UNIO (val=Omega)?
                symbolic_areo_output = create_symbolic_avc_val_1Cii("areo_out_target")
                setup.extend(get_base_avc_constraints_1Cii(symbolic_areo_output, omega_smt_node, omega_test))
                setup.append(symbolic_areo_output["is_unio"]) 
                # Forcing the target to be AREO like (val=Omega)
                # For 1Cii, U_SINGLE is val=0. AREO_UNIO for comparison needs val=Omega_smt_node if we had aspects.
                # Since we don't have aspects in 1Cii for the output U_SINGLE, this comparison is hard.
                # The most direct is: output of mul_1Cii should be U_SINGLE.
                # The v1.2b test (AREO_UNIO * DFI -> AREO_UNIO) is now (U_SINGLE * DFI -> U_SINGLE).
                # So, the test that U_SINGLE * DFI -> U_SINGLE (val=0) would pass.
                # The test that U_SINGLE * DFI -> an "AREO-like" Unio (val=Omega) would fail.
                # The test "smt_test_mul_aspect_1Cii" already covers U*DFI=U.
                # This demonstrates that the specific aspect information in output is lost.
                # Let's keep the existing "smt_test_mul_aspect_1Cii". The failure of previous, more specific
                # aspect tests from Suite 1.B if run here would be the actual demonstration of change.
                # We can state this in analysis rather than adding a confusing SMT test here.
                pass # Covered by analysis of 'smt_test_mul_aspect_1Cii' changing meaning.


        print("\n--- SMT Test Summary (Suite 1.C.ii) ---")
        for o, res in sorted(smt_test_summary_1Cii.items()):
            print(f"  Ω={o}: Passed={res['passed']}, Failed={res['failed']}, Skipped={res['skipped']}")
    else:
        print("\nSMT-based tests for Suite 1.C.ii were skipped as PySMT is not available.")

    print("\n====== Suite 1.C.ii Finished ======")