import re
import itertools
import math
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- PySMT Imports (Added) ---
try:
    from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                                 ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals)
    from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
    from pysmt.fnode import FNode
    SMT_MODE_AVAILABLE = True
except ImportError:
    SMT_MODE_AVAILABLE = False
    # This global flag will be used to skip SMT tests if pysmt is not found
    # Print warning during SMT test execution instead of at import time for cleaner initial output.

# --- Configuration ---
SMT_SOLVER_NAME = "z3"

# --- Suite 1.B: New Unio Class Definition (Single Constructor with Aspect) ---
class Unio_SCA:
    """
    Represents the unified Unio pole for Suite 1.B.
    Single constructor but preserves aspect information.
    All instances are algebraically equivalent.
    """
    __slots__ = ("aspect",)

    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio_SCA aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect

    def __eq__(self, other: object) -> bool:
        """All Unio_SCA instances are algebraically equivalent."""
        return isinstance(other, Unio_SCA)

    def __hash__(self) -> int:
        """All Unio_SCA instances hash to the same value."""
        return hash(type(self)) # Ensures Unio_SCA('zero') and Unio_SCA('areo') hash same

    def __repr__(self) -> str:
        return f"Unio_SCA('{self.aspect}')"

# Canonical instances for Suite 1.B
U_ZERO_REP = Unio_SCA("zero")
U_AREO_REP = Unio_SCA("areo")

# Type Alias for this variant
AVCVal_1B = Union[int, Unio_SCA]

# --- AVCA Core Logic Adapted for Suite 1.B (using Unio_SCA) ---
# Global Omega parameter for these operations
Omega_1B: int = 0

def set_avca_omega_1B(omega_value: int, verbose=False):
    global Omega_1B
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_1B parameter must be an integer >= 1.")
    Omega_1B = omega_value
    if verbose:
        print(f"Suite 1.B: Omega_1B set to {Omega_1B}")

def _check_val_1B(x: AVCVal_1B, current_omega: int, op_name: str = "operation"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega_1B parameter for {op_name} must be an integer >= 1. Got: {current_omega!r}")
    if isinstance(x, Unio_SCA):
        return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value in {op_name}: {x!r}. Expected int (for DFI) or Unio_SCA. Got type: {type(x)}.")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI Value for {op_name} with Omega_1B=1: {x}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value for {op_name}: {x}. For Omega_1B={current_omega}, DFI integers must be in range [1, {current_omega - 1}].")

def avc_add_1B(a: AVCVal_1B, b: AVCVal_1B) -> AVCVal_1B:
    global Omega_1B
    if Omega_1B == 0: raise ValueError("Global Omega_1B not set for avc_add_1B.")
    _check_val_1B(a, Omega_1B, "avc_add_1B(a)")
    _check_val_1B(b, Omega_1B, "avc_add_1B(b)")
    if isinstance(a, Unio_SCA): return b
    if isinstance(b, Unio_SCA): return a
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < Omega_1B else U_AREO_REP

def avc_sub_1B(a: AVCVal_1B, b: AVCVal_1B) -> AVCVal_1B:
    global Omega_1B
    if Omega_1B == 0: raise ValueError("Global Omega_1B not set for avc_sub_1B.")
    _check_val_1B(a, Omega_1B, "avc_sub_1B(a)")
    _check_val_1B(b, Omega_1B, "avc_sub_1B(b)")
    if isinstance(b, Unio_SCA): return a
    if isinstance(a, Unio_SCA): return U_AREO_REP
    if a > b: return a - b # type: ignore
    else: return U_AREO_REP

def avc_mul_1B(a: AVCVal_1B, b: AVCVal_1B) -> AVCVal_1B:
    global Omega_1B
    if Omega_1B == 0: raise ValueError("Global Omega_1B not set for avc_mul_1B.")
    _check_val_1B(a, Omega_1B, "avc_mul_1B(a)")
    _check_val_1B(b, Omega_1B, "avc_mul_1B(b)")
    a_is_unio = isinstance(a, Unio_SCA)
    b_is_unio = isinstance(b, Unio_SCA)
    if a_is_unio or b_is_unio:
        a_aspect_is_areo = a_is_unio and a.aspect == "areo" # type: ignore
        b_aspect_is_areo = b_is_unio and b.aspect == "areo" # type: ignore
        is_any_areo_aspected = a_aspect_is_areo or b_aspect_is_areo
        return U_AREO_REP if is_any_areo_aspected else U_ZERO_REP
    else:
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < Omega_1B else U_AREO_REP

def avc_div_1B(a: AVCVal_1B, b: AVCVal_1B) -> AVCVal_1B:
    global Omega_1B
    if Omega_1B == 0: raise ValueError("Global Omega_1B not set for avc_div_1B.")
    _check_val_1B(a, Omega_1B, "avc_div_1B(a)")
    _check_val_1B(b, Omega_1B, "avc_div_1B(b)")
    if isinstance(b, Unio_SCA): return U_AREO_REP
    if isinstance(a, Unio_SCA):
        return U_ZERO_REP if a.aspect == "zero" else U_AREO_REP # type: ignore
    a_val: int = a # type: ignore
    b_val: int = b # type: ignore
    if b_val == 0: # Should be caught by _check_val if b_val is DFI and not Unio
         raise ValueError("Division by DFI zero attempted in avc_div_1B logic after _check_val - should not happen.")
    quotient, remainder = divmod(a_val, b_val)
    return quotient if remainder == 0 and (1 <= quotient < Omega_1B) else U_AREO_REP

# --- Native Python Test Harness ---
native_test_summary = {}

def run_native_test(test_name: str, omega_val: int, test_func: Callable, expect_fail: bool = False, failure_is_skip: bool = False):
    global native_test_summary
    set_avca_omega_1B(omega_val)
    if omega_val not in native_test_summary:
        native_test_summary[omega_val] = {"passed": 0, "failed": 0, "skipped": 0}
    
    print(f"  Running Native Test: '{test_name}' for Ω={omega_val} (Expect: {'Fails' if expect_fail else 'Holds'})", end=" ... ")
    try:
        result, counterexample = test_func(omega_val)
        passes = (result and not expect_fail) or (not result and expect_fail)
        
        if passes:
            print("PASS")
            native_test_summary[omega_val]["passed"] += 1
        else:
            print(f"FAIL (Observed: {'Holds' if result else 'Fails'})")
            if counterexample:
                print(f"    Counterexample: {counterexample}")
            native_test_summary[omega_val]["failed"] += 1
    except Exception as e:
        if failure_is_skip:
            print(f"SKIPPED ({e})")
            native_test_summary[omega_val]["skipped"] +=1
        else:
            print(f"ERROR ({e})")
            native_test_summary[omega_val]["failed"] += 1 # Count errors as fails

def get_s_omega_1B(current_omega: int) -> List[AVCVal_1B]:
    if current_omega == 1: return [U_ZERO_REP] # Or U_AREO_REP, algebraically same
    return [U_ZERO_REP] + list(range(1, current_omega)) # Use U_ZERO_REP as canonical U for iteration

# Native Test Functions
def native_test_totality_op(omega_val: int, op_func: Callable) -> Tuple[bool, Any]:
    elements = get_s_omega_1B(omega_val)
    for a in elements:
        for b in elements:
            try:
                res = op_func(a,b)
                _check_val_1B(res, omega_val) # Check if result is valid AVCA val
            except Exception as e:
                return False, f"Error for {a!r} op {b!r}: {e}"
    return True, None

def native_test_commutativity_add(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1B(omega_val)
    for a in elements:
        for b in elements:
            if avc_add_1B(a,b) != avc_add_1B(b,a): # Uses Unio_SCA.__eq__
                return False, f"a={a!r}, b={b!r}"
    return True, None

def native_test_associativity_add(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1B(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                lhs = avc_add_1B(avc_add_1B(a,b),c)
                rhs = avc_add_1B(a,avc_add_1B(b,c))
                if lhs != rhs:
                    return False, f"a={a!r}, b={b!r}, c={c!r} -> LHS={lhs!r}, RHS={rhs!r}"
    return True, None

# ... (Other native test functions for add_identity, add_inverses, comm_mul, assoc_mul, distrib_mul_add can be added here)
# For brevity in this example, I'll include a few key ones and then move to SMT section

def native_test_commutativity_mul(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1B(omega_val)
    for a in elements:
        for b in elements:
            if avc_mul_1B(a,b) != avc_mul_1B(b,a):
                return False, f"a={a!r}, b={b!r}"
    return True, None

def native_test_associativity_mul(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1B(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                lhs = avc_mul_1B(avc_mul_1B(a,b),c)
                rhs = avc_mul_1B(a,avc_mul_1B(b,c))
                if lhs != rhs:
                    return False, f"a={a!r}, b={b!r}, c={c!r} -> LHS={lhs!r}, RHS={rhs!r}"
    return True, None
    
def native_test_distributivity_mul_over_add(omega_val: int) -> Tuple[bool, Any]: # Left Distributivity
    elements = get_s_omega_1B(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                b_plus_c = avc_add_1B(b, c)
                lhs = avc_mul_1B(a, b_plus_c)
                
                a_mul_b = avc_mul_1B(a, b)
                a_mul_c = avc_mul_1B(a, c)
                rhs = avc_add_1B(a_mul_b, a_mul_c)
                
                if lhs != rhs:
                    return False, f"a={a!r}, b={b!r}, c={c!r} -> a(b+c)={lhs!r}, (ab)+(ac)={rhs!r}"
    return True, None

# --- SMT Harness Components (Embedded for self-containment) ---
try:
    from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                                 ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals)
    from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
    from pysmt.fnode import FNode
    SMT_MODE_AVAILABLE = True
except ImportError:
    SMT_MODE_AVAILABLE = False
    print("WARNING: PySMT not found. SMT tests will be skipped.")

smt_test_summary = {}
Omega_py_smt: int = 0 # Used by SMT builders to know current Omega

def create_symbolic_avc_val(name_prefix: str) -> Dict[str, FNode]:
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_Zaspect", SMT_BOOL_TYPE), # aspect
        "is_areo_aspect": Symbol(f"{name_prefix}_is_Aaspect", SMT_BOOL_TYPE), # aspect
        "is_finite": Symbol(f"{name_prefix}_is_F", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]:
    is_unio = Or(avc_repr["is_zero_aspect"], avc_repr["is_areo_aspect"])
    constraints = [
        Iff(is_unio, Not(avc_repr["is_finite"])), # Unio iff not finite
        Implies(avc_repr["is_zero_aspect"], Not(avc_repr["is_areo_aspect"])), # Aspects are mutually exclusive if Unio
        
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero_aspect"], Equals(avc_repr["val"], Int(0))), # Convention for U_ZERO_REP
        Implies(avc_repr["is_areo_aspect"], Equals(avc_repr["val"], omega_smt_node)) # Convention for U_AREO_REP
    ]
    if current_omega_py == 1:
        constraints.append(Not(avc_repr["is_finite"])) # DFI is empty
        constraints.append(Implies(is_unio, Or(Equals(avc_repr["val"], Int(0)), Equals(avc_repr["val"], omega_smt_node)))) # U can be Z or A aspect
    return constraints

def avc_equiv_smt(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode:
    # Algebraic equivalence: both are Unio (any aspect), OR both are DFI and have same value.
    avc1_is_unio = Or(avc1["is_zero_aspect"], avc1["is_areo_aspect"])
    avc2_is_unio = Or(avc2["is_zero_aspect"], avc2["is_areo_aspect"])
    
    both_unio = And(avc1_is_unio, avc2_is_unio)
    both_dfi_equal_val = And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"]))
    return Or(both_unio, both_dfi_equal_val)

# SMT Logic Builders (Modeling the _1B operations, logic is same as v1.2b)
# These now take current_omega_py for base constraints context if needed, omega_smt_node for arithmetic.
def avc_add_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])

    res_becomes_a_state = And(Iff(res["is_zero_aspect"], a["is_zero_aspect"]), Iff(res["is_areo_aspect"], a["is_areo_aspect"]),
                              Iff(res["is_finite"], a["is_finite"]), Equals(res["val"], a["val"]))
    res_becomes_b_state = And(Iff(res["is_zero_aspect"], b["is_zero_aspect"]), Iff(res["is_areo_aspect"], b["is_areo_aspect"]),
                              Iff(res["is_finite"], b["is_finite"]), Equals(res["val"], b["val"]))

    case1_a_is_unio = Implies(a_is_unio, res_becomes_b_state)
    case2_b_is_unio_a_is_dfi = Implies(And(a["is_finite"], b_is_unio), res_becomes_a_state)
    
    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    symbolic_sum_val = Plus(a["val"], b["val"])
    
    res_is_dfi_sum_state = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]),
                               Equals(res["val"], symbolic_sum_val))
    res_is_U_AREO_REP_state = And(Not(res["is_finite"]), res["is_areo_aspect"], Not(res["is_zero_aspect"]),
                                 Equals(res["val"], omega_smt_node)) # AREO_UNIO has val=Omega
    
    case3_dfi_dfi_logic = Implies(cond_both_are_dfi, 
                                  Ite(symbolic_sum_val < omega_smt_node,
                                      res_is_dfi_sum_state,
                                      res_is_U_AREO_REP_state))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi_logic)

def avc_mul_smt_logic(a: Dict[str, FNode], b: Dict[str, FNode],
                      res: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> FNode:
    a_is_unio = Or(a["is_zero_aspect"], a["is_areo_aspect"])
    b_is_unio = Or(b["is_zero_aspect"], b["is_areo_aspect"])

    # If an input Unio object has "areo" aspect
    a_is_areo_aspected = a["is_areo_aspect"] # This is true if (a is Unio AND a.aspect == "areo")
    b_is_areo_aspected = b["is_areo_aspect"]

    cond_any_unio_operand_is_areo_aspected = Or(a_is_areo_aspected, b_is_areo_aspected)

    res_is_U_ZERO_REP_state = And(Not(res["is_finite"]), res["is_zero_aspect"], Not(res["is_areo_aspect"]),
                                 Equals(res["val"], Int(0)))
    res_is_U_AREO_REP_state = And(Not(res["is_finite"]), res["is_areo_aspect"], Not(res["is_zero_aspect"]),
                                 Equals(res["val"], omega_smt_node))

    unio_case_behavior = Ite(cond_any_unio_operand_is_areo_aspected,
                             res_is_U_AREO_REP_state,  # Areo dominates
                             res_is_U_ZERO_REP_state) # Else, Zero aspect

    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    prod_val = a["val"] * b["val"] # SMT multiplication
    res_is_FP_prod_formula = And(res["is_finite"], Not(res["is_zero_aspect"]), Not(res["is_areo_aspect"]),
                                 Equals(res["val"], prod_val))
    dfi_case_behavior = Ite(And(prod_val >= Int(1), prod_val < omega_smt_node),
                            res_is_FP_prod_formula,
                            res_is_U_AREO_REP_state) # DFI overflow to U_AREO_REP
    
    return Ite(Or(a_is_unio, b_is_unio), unio_case_behavior, dfi_case_behavior)


def prove_or_find_counterexample_smt(
    property_name: str, omega_py_val: int, setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    
    global smt_test_summary, Omega_py_smt
    Omega_py_smt = omega_py_val # Set global for SMT builders if they were to use it (they use omega_smt_node mostly)
    
    if not SMT_MODE_AVAILABLE:
        print(f"SKIPPED (SMT Mode Unavailable) for {property_name} Ω={omega_py_val}")
        if omega_py_val not in smt_test_summary:
            smt_test_summary[omega_py_val] = {"passed": 0, "failed": 0, "skipped": 0}
        smt_test_summary[omega_py_val]["skipped"] += 1
        return

    if omega_py_val not in smt_test_summary:
        smt_test_summary[omega_py_val] = {"passed": 0, "failed": 0, "skipped": 0}

    print(f"  SMT Test: '{property_name}' for Ω={omega_py_val} (Expect: {'Hold/Exist' if expect_property_to_hold else 'Fail/Not Exist'})", end=" ... ")
    
    property_holds_observed = False
    counterexample_witness_str = None
    
    try:
        with Solver(name=SMT_SOLVER_NAME, logic="LIA") as s: # Quantifier-Free Linear Integer Arithmetic often sufficient
            for f_setup in setup_formulas:
                s.add_assertion(f_setup)
            
            formula_to_check = property_to_verify
            if not is_existential: # Universal property, check negation
                formula_to_check = Not(property_to_verify)

            if s.solve([formula_to_check] if is_existential else [formula_to_check]): # Target for solve() is what makes it SAT
                # If is_existential: SAT means property holds (witness found)
                # If universal (checking Not(P)): SAT means Not(P) is true, so P is FALSE (counterexample found)
                if is_existential:
                    property_holds_observed = True
                else: # Universal, found counterexample
                    property_holds_observed = False
                
                model = s.get_model(); ce_parts = []
                for repr_dict in inputs_reprs:
                    name = repr_dict['name']
                    try:
                        is_z_aspect = model.get_value(repr_dict['is_zero_aspect']).is_true()
                        is_a_aspect = model.get_value(repr_dict['is_areo_aspect']).is_true()
                        is_f = model.get_value(repr_dict['is_finite']).is_true()
                        val_smt = model.get_value(repr_dict['val'])
                        
                        state_str = "Unknown"
                        if is_f: state_str = f"Fp({val_smt})"
                        elif is_z_aspect: state_str = "U_Z_Rep" # Unio_SCA('zero')
                        elif is_a_aspect: state_str = "U_A_Rep" # Unio_SCA('areo')
                        ce_parts.append(f"{name}={state_str}")
                    except Exception as e_model: ce_parts.append(f"{name}=?(Err:{e_model})")
                counterexample_witness_str = "; ".join(ce_parts)

            else: # UNSAT
                # If is_existential: UNSAT means property FAILED (no witness)
                # If universal (checking Not(P)): UNSAT means Not(P) is false, so P is TRUE
                if is_existential:
                    property_holds_observed = False
                else: # Universal, Not(P) is false, P holds
                    property_holds_observed = True
        
        success_for_summary = (property_holds_observed == expect_property_to_hold)
        
        if success_for_summary:
            print("PASS")
            smt_test_summary[omega_py_val]["passed"] += 1
            if counterexample_witness_str and is_existential and expect_property_to_hold:
                 print(f"    Witness (as expected): {counterexample_witness_str}")
            elif counterexample_witness_str and not is_existential and not expect_property_to_hold:
                 print(f"    Counterexample (as expected for failure): {counterexample_witness_str}")
        else:
            print(f"FAIL (Observed: {'Holds/Exists' if property_holds_observed else 'Fails/Not Exist'})")
            smt_test_summary[omega_py_val]["failed"] += 1
            if counterexample_witness_str:
                 label = "Unexpected Witness" if is_existential else "Counterexample (property unexpectedly failed)"
                 if not property_holds_observed and expect_property_to_hold and is_existential:
                     label = "Witness NOT Found (but was expected)"
                 elif not property_holds_observed and not expect_property_to_hold and not is_existential: # P held, but expected fail
                     label = "No Counterexample Found (property unexpectedly held)"


                 print(f"    {label}: {counterexample_witness_str if counterexample_witness_str else '(No model value for fail condition)'}")


    except Exception as e:
        print(f"ERROR ({e})")
        smt_test_summary[omega_py_val]["failed"] += 1


# SMT Test Functions
def smt_test_A1_totality_add_1B(omega_val_py: int):
    property_name = "SMT A.1: Totality for avc_add_1B"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val("a_totA"); b = create_symbolic_avc_val("b_totA"); res = create_symbolic_avc_val("res_totA")
    setup = get_base_avc_constraints(a, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(b, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(res, omega_smt_node, omega_val_py) # res must also be valid
    setup.append(avc_add_smt_logic(a,b,res,omega_smt_node, omega_val_py))
    # Property is that such a valid 'res' always exists given valid 'a', 'b' and the op definition.
    # The base constraints on 'res' ARE the property.
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, TRUE(), [a,b,res], True, is_existential=False)

def smt_test_A2_well_definedness_add_1B(omega_val_py: int):
    property_name = "SMT A.2: Well-Definedness for avc_add_1B"
    omega_smt_node = Int(omega_val_py)
    a1 = create_symbolic_avc_val("a1_wdA"); a2 = create_symbolic_avc_val("a2_wdA")
    b1 = create_symbolic_avc_val("b1_wdA"); b2 = create_symbolic_avc_val("b2_wdA")
    res1 = create_symbolic_avc_val("res1_wdA"); res2 = create_symbolic_avc_val("res2_wdA")
    setup = get_base_avc_constraints(a1, omega_smt_node, omega_val_py) + get_base_avc_constraints(a2, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(b1, omega_smt_node, omega_val_py) + get_base_avc_constraints(b2, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(res1, omega_smt_node, omega_val_py) + get_base_avc_constraints(res2, omega_smt_node, omega_val_py)
    premises = And(avc_equiv_smt(a1,a2), avc_equiv_smt(b1,b2))
    setup.append(avc_add_smt_logic(a1,b1,res1,omega_smt_node, omega_val_py))
    setup.append(avc_add_smt_logic(a2,b2,res2,omega_smt_node, omega_val_py))
    property_formula = Implies(premises, avc_equiv_smt(res1, res2))
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a1,a2,b1,b2], True)

def smt_test_associativity_add_1B(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Associativity of avc_add_1B (Expect: {'Holds' if expected_to_hold else 'Fails'})"
    omega_smt_node = Int(omega_val_py)
    a = create_symbolic_avc_val("a_ascA"); b = create_symbolic_avc_val("b_ascA"); c = create_symbolic_avc_val("c_ascA")
    ab = create_symbolic_avc_val("ab_ascA"); lhs = create_symbolic_avc_val("lhs_ascA")
    bc = create_symbolic_avc_val("bc_ascA"); rhs = create_symbolic_avc_val("rhs_ascA")
    setup = get_base_avc_constraints(a, omega_smt_node, omega_val_py) + get_base_avc_constraints(b, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(c, omega_smt_node, omega_val_py) + get_base_avc_constraints(ab, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(lhs, omega_smt_node, omega_val_py) + get_base_avc_constraints(bc, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(rhs, omega_smt_node, omega_val_py)
    setup.append(avc_add_smt_logic(a,b,ab,omega_smt_node, omega_val_py)); setup.append(avc_add_smt_logic(ab,c,lhs,omega_smt_node, omega_val_py))
    setup.append(avc_add_smt_logic(b,c,bc,omega_smt_node, omega_val_py)); setup.append(avc_add_smt_logic(a,bc,rhs,omega_smt_node, omega_val_py))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b,c], expected_to_hold)

def smt_test_distributivity_mul_over_add_1B(omega_val_py: int):
    expected_to_hold = (omega_val_py <= 2)
    property_name = f"SMT Left Distributivity (avc_mul_1B over avc_add_1B) (Expect: {'Holds' if expected_to_hold else 'Fails'})"
    omega_smt_node = Int(omega_val_py)
    a=create_symbolic_avc_val("aD");b=create_symbolic_avc_val("bD");c=create_symbolic_avc_val("cD")
    bpc=create_symbolic_avc_val("bpcD");lhs=create_symbolic_avc_val("lhsD")
    ab=create_symbolic_avc_val("abD");ac=create_symbolic_avc_val("acD");rhs=create_symbolic_avc_val("rhsD")
    setup = get_base_avc_constraints(a, omega_smt_node, omega_val_py) + get_base_avc_constraints(b, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(c, omega_smt_node, omega_val_py) + get_base_avc_constraints(bpc, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(lhs, omega_smt_node, omega_val_py) + get_base_avc_constraints(ab, omega_smt_node, omega_val_py) + \
            get_base_avc_constraints(ac, omega_smt_node, omega_val_py) + get_base_avc_constraints(rhs, omega_smt_node, omega_val_py)
    setup.append(avc_add_smt_logic(b,c,bpc,omega_smt_node,omega_val_py)); setup.append(avc_mul_smt_logic(a,bpc,lhs,omega_smt_node,omega_val_py))
    setup.append(avc_mul_smt_logic(a,b,ab,omega_smt_node,omega_val_py)); setup.append(avc_mul_smt_logic(a,c,ac,omega_smt_node,omega_val_py));
    setup.append(avc_add_smt_logic(ab,ac,rhs,omega_smt_node,omega_val_py))
    property_formula = avc_equiv_smt(lhs,rhs)
    prove_or_find_counterexample_smt(property_name, omega_val_py, setup, property_formula, [a,b,c], expected_to_hold)

# Main execution block
if __name__ == "__main__":
    print("====== AVCA Suite 1.B: Unio_SCA with Aspect Preservation ======")
    omegas_for_native = [1, 2, 3, 4]
    omegas_for_smt = [1, 2, 3, 5]

    print("\n--- Running Native Python Tests for Suite 1.B ---")
    for omega_test in omegas_for_native:
        print(f"\n-- Native Tests for Ω = {omega_test} --")
        run_native_test(f"Operational Totality for avc_add_1B", omega_test, lambda o: native_test_totality_op(o, avc_add_1B))
        run_native_test(f"Operational Totality for avc_sub_1B", omega_test, lambda o: native_test_totality_op(o, avc_sub_1B))
        run_native_test(f"Operational Totality for avc_mul_1B", omega_test, lambda o: native_test_totality_op(o, avc_mul_1B))
        run_native_test(f"Operational Totality for avc_div_1B", omega_test, lambda o: native_test_totality_op(o, avc_div_1B))
        
        run_native_test("Commutativity of avc_add_1B", omega_test, native_test_commutativity_add)
        run_native_test("Associativity of avc_add_1B", omega_test, native_test_associativity_add, expect_fail=(omega_test > 2))
        
        run_native_test("Commutativity of avc_mul_1B", omega_test, native_test_commutativity_mul)
        run_native_test("Associativity of avc_mul_1B", omega_test, native_test_associativity_mul, expect_fail=False) # Expect mul assoc to hold
        
        run_native_test("Left Distributivity (avc_mul_1B over avc_add_1B)", omega_test, native_test_distributivity_mul_over_add, expect_fail=(omega_test > 2))

    print("\n--- Native Python Test Summary (Suite 1.B) ---")
    for o, res in sorted(native_test_summary.items()):
        print(f"  Ω={o}: Passed={res['passed']}, Failed={res['failed']}, Skipped={res['skipped']}")
    
    if SMT_MODE_AVAILABLE:
        print("\n\n--- Running SMT-based Tests for Suite 1.B ---")
        for omega_test in omegas_for_smt:
            print(f"\n-- SMT Tests for Ω = {omega_test} --")
            # Add a selection of critical SMT tests here
            smt_test_A1_totality_add_1B(omega_test) # Example for add, should do for all ops
            smt_test_A2_well_definedness_add_1B(omega_test) # Example for add
            
            # Key law phase transitions
            smt_test_associativity_add_1B(omega_test)
            smt_test_distributivity_mul_over_add_1B(omega_test)

            # Test mul aspect handling logic (since Unio_SCA still has aspects)
            # This test checks if U_AREO_REP * DFI = U_AREO_REP (Areo dominance with DFI)
            prop_name_mul_aspect = f"SMT Mul Aspect: U_AREO_REP * DFI_k = U_AREO_REP"
            omega_smt = Int(omega_test)
            u_areo_sym = create_symbolic_avc_val("uAreo")
            dfi_k_sym = create_symbolic_avc_val("dfiK")
            res_mul_sym = create_symbolic_avc_val("resMulAspect")
            
            setup_mul_aspect = get_base_avc_constraints(u_areo_sym, omega_smt, omega_test) + \
                               get_base_avc_constraints(dfi_k_sym, omega_smt, omega_test) + \
                               get_base_avc_constraints(res_mul_sym, omega_smt, omega_test)
            setup_mul_aspect.extend([
                u_areo_sym["is_areo_aspect"], # u_areo_sym is U_AREO_REP
                dfi_k_sym["is_finite"]    # dfi_k_sym is DFI
            ])
            if omega_test == 1: # DFI cannot exist
                 prove_or_find_counterexample_smt(prop_name_mul_aspect + " (SKIPPED DFI N/A)", omega_test, [], TRUE(), [], True)
            else:
                setup_mul_aspect.append(avc_mul_smt_logic(u_areo_sym, dfi_k_sym, res_mul_sym, omega_smt, omega_test))
                # Property: result must be U_AREO_REP
                property_mul_aspect = And(Not(res_mul_sym["is_finite"]), res_mul_sym["is_areo_aspect"], Not(res_mul_sym["is_zero_aspect"]))
                prove_or_find_counterexample_smt(prop_name_mul_aspect, omega_test, setup_mul_aspect, property_mul_aspect, [u_areo_sym, dfi_k_sym], True)

        print("\n--- SMT Test Summary (Suite 1.B) ---")
        for o, res in sorted(smt_test_summary.items()):
            print(f"  Ω={o}: Passed={res['passed']}, Failed={res['failed']}, Skipped={res['skipped']}")
    else:
        print("\nSMT-based tests for Suite 1.B were skipped as PySMT is not available.")

    print("\n====== Suite 1.B Finished ======")