# avca_max_brutality_harness.py
# Single-file harness for AVCA Max-Brutality Stress-Testing & Research Programme
#
# Target: Core AVCA-Ω v1.2 Variant B
#
# Python Environment Dependencies:
# - pysmt
# - z3-solver (or other SMT solver compatible with PySMT)
# - pytest (optional, for potentially structuring tests if this file grows too large
#           and we decide to split parts into callable modules later, but for now,
#           all in one)

import math
import itertools # For brute-force test generation
from typing import Literal, Union, Any, Tuple, List, Dict, Callable, Set, FrozenSet

# --- Part 0.5: Resource Management (Initial Placeholders) ---
# These can be configured at the start of a testing session
OMEGA_NATIVE_MAX_DEFAULT = 4  # Max Omega for exhaustive native tests (e.g., up to Ω^3 or Ω^4 complexity)
SMT_TIMEOUT_DEFAULT_MS = 30000 # Default SMT solver timeout in milliseconds (30 seconds)
RANDOM_SAMPLE_SIZE_DEFAULT = 10000 # For tests on very large domains

# --- Part 1: Core AVCA-Ω v1.2b Implementation ---
# (Adapted from AVCA Core DraftV4 Appendix A)

# Global Omega Parameter for Core AVCA operations
# This will be set by test runners or specific test functions.
_CORE_AVCA_OMEGA: int = 0

class Unio:
    """
    Represents the unified Unio pole in AVCA-Ω, embodying conceptual Zero 
    and Areo aspects. All Unio instances are algebraically equivalent.
    """
    __slots__ = ("aspect",) # Memory optimization

    def __init__(self, aspect: Literal["zero", "areo"]):
        if aspect not in ("zero", "areo"):
            raise ValueError("Unio aspect must be 'zero' or 'areo'.")
        self.aspect: Literal["zero", "areo"] = aspect

    def __eq__(self, other: object) -> bool:
        """
        Defines algebraic equivalence: all Unio instances are considered equal
        if the 'other' object is also an instance of Unio, regardless of aspect.
        """
        return isinstance(other, Unio)

    def __hash__(self) -> int:
        """
        Ensures all Unio instances hash to the same value, consistent with
        their algebraic equivalence.
        """
        return hash(f"AVCA_Algebraic_Unio_Singleton") # Unique hash for the Unio type

    def __repr__(self) -> str:
        return f"Unio('{self.aspect}')"

    # Added for consistent sorting in test outputs/sets if needed
    def __lt__(self, other: Any) -> bool: 
        if isinstance(other, Unio):
            return self.aspect < other.aspect # Arbitrary but consistent for Unio-Unio
        if isinstance(other, int):
            return True # Unio considered "less than" DFI for sorting
        return NotImplemented

# Canonical Unio Instances
ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")

# Type Alias for AVCA Values
AVCVal = Union[int, Unio]

def set_core_avca_omega(omega_value: int):
    """Sets the global Omega for Core AVCA operations within this module."""
    global _CORE_AVCA_OMEGA
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError(f"Core AVCA Omega parameter must be an integer >= 1. Got: {omega_value}")
    _CORE_AVCA_OMEGA = omega_value

def _check_val(x: AVCVal, current_omega: int, var_name: str = "input"):
    """
    Validates if x is a proper element of S_Ω for the given current_omega.
    Called at the beginning of each Core AVCA operation.
    """
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega ({current_omega}) for {var_name} validation must be an integer >= 1.")

    if isinstance(x, Unio):
        return  # Unio objects are always valid elements of S_Omega.

    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value for {var_name}: {x!r}. Expected int (for DFI) or Unio instance. Omega={current_omega}, Type={type(x)}.")

    if current_omega == 1:
        raise ValueError(f"Invalid DFI Value for {var_name}: {x}. DFI is empty when Omega=1.")
    
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value for {var_name}: {x}. For Omega={current_omega}, DFI integers must be in range [1, {current_omega - 1}].")

# --- Core AVCA Operations (v1.2b logic from Appendix A) ---

def avc_add(a: AVCVal, b: AVCVal) -> AVCVal:  # ⊕_v1.1 logic 
    # Uses global _CORE_AVCA_OMEGA set by set_core_avca_omega()
    if _CORE_AVCA_OMEGA == 0: 
        raise ValueError("Global _CORE_AVCA_OMEGA not set. Call set_core_avca_omega(value) first.")
    _check_val(a, _CORE_AVCA_OMEGA, "add_a")
    _check_val(b, _CORE_AVCA_OMEGA, "add_b")

    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    
    standard_sum = a + b # type: ignore 
    return standard_sum if standard_sum < _CORE_AVCA_OMEGA else AREO_UNIO

def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal:  # ⊖_v1.0 logic 
    if _CORE_AVCA_OMEGA == 0: raise ValueError("_CORE_AVCA_OMEGA not set.")
    _check_val(a, _CORE_AVCA_OMEGA, "sub_a"); _check_val(b, _CORE_AVCA_OMEGA, "sub_b")

    if isinstance(b, Unio): return a
    if isinstance(a, Unio): return AREO_UNIO # b is DFI here
    
    # Both DFI
    return (a - b) if a > b else AREO_UNIO # type: ignore

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal:  # ⊗_v1.2 logic 
    if _CORE_AVCA_OMEGA == 0: raise ValueError("_CORE_AVCA_OMEGA not set.")
    _check_val(a, _CORE_AVCA_OMEGA, "mul_a"); _check_val(b, _CORE_AVCA_OMEGA, "mul_b")

    a_is_unio = isinstance(a, Unio)
    b_is_unio = isinstance(b, Unio)

    if a_is_unio or b_is_unio:
        a_is_areo = a_is_unio and a.aspect == "areo" # type: ignore
        b_is_areo = b_is_unio and b.aspect == "areo" # type: ignore
        return AREO_UNIO if (a_is_areo or b_is_areo) else ZERO_UNIO
    else: # Both DFI
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < _CORE_AVCA_OMEGA else AREO_UNIO

def avc_div(a: AVCVal, b: AVCVal) -> AVCVal:  # ⊘_v1.2B logic 
    if _CORE_AVCA_OMEGA == 0: raise ValueError("_CORE_AVCA_OMEGA not set.")
    _check_val(a, _CORE_AVCA_OMEGA, "div_a"); _check_val(b, _CORE_AVCA_OMEGA, "div_b")

    if isinstance(b, Unio): return AREO_UNIO # Rule B1
    
    # b is DFI here
    if isinstance(a, Unio): # Rule B2
        return ZERO_UNIO if a.aspect == "zero" else AREO_UNIO # type: ignore
    
    # Both DFI (Rule B3)
    a_val: int = a # type: ignore 
    b_val: int = b # type: ignore
    if b_val == 0: # Should be caught by _check_val if DFI rules are 1 <= b_val < Omega
        # This case should ideally not be reached if _check_val is correct
        # for DFI elements (which cannot be 0).
        # If somehow b_val is 0 and not Unio, it's an issue upstream or with Omega=1 context.
        # For DFI/DFI, b_val is guaranteed >= 1.
        return AREO_UNIO # Fallback, though _check_val should prevent DFI b_val=0

    quotient, remainder = divmod(a_val, b_val)
    return quotient if remainder == 0 and (1 <= quotient < _CORE_AVCA_OMEGA) else AREO_UNIO

# --- End of Part 1: Core AVCA-Ω v1.2b Implementation ---

# --- Part 2: SMT Harness Core (Builders & Helpers) ---
import typing
from typing import Dict, List, Union, Any, Literal, Callable # Keep other necessary typing imports

# --- Define Type Aliases for Static Type Hinting ---
# These names suffixed with _Hint will be used in all function signatures.

if typing.TYPE_CHECKING:
    # This block is ONLY for static type checkers (Pylance, MyPy).
    # It allows them to know the actual types if pysmt is installed in the dev/linting environment.
    from pysmt.fnode import FNode as _PysmtFNode_Internal # Internal alias for real FNode
    from pysmt.typing import PySMTType as _PysmtPySMTType_Internal # Base for INT, BOOL instances
    
    FNode_Hint: typing.TypeAlias = _PysmtFNode_Internal
    # For Symbol(name, type_instance), type_instance is an object, often of PySMTType
    SMTTypeInstance_Hint: typing.TypeAlias = _PysmtPySMTType_Internal
    SMTSymbolicAVCVal_Hint: typing.TypeAlias = Dict[str, FNode_Hint]

    # For SMT functions (can be more specific if needed, but Callable works)
    _SMTFunc_ReturnsFNode_Hint = Callable[..., FNode_Hint]
    _SMTFunc_ReturnsPySMTType_Hint = Callable[..., SMTTypeInstance_Hint] # e.g. for pysmt.shortcuts.BOOL()
    _SMTFunc_ReturnsBool_Hint = Callable[..., bool]
    _SolverClass_Hint = typing.Type[Any] # Type of the Solver class itself
else:
    # This block is effective if typing.TYPE_CHECKING is False (i.e., at runtime before imports)
    # OR if pysmt is NOT found by the linter when it processes the TYPE_CHECKING block.
    # These serve as fallbacks for the _Hint types.
    FNode_Hint = Any
    SMTTypeInstance_Hint = Any
    SMTSymbolicAVCVal_Hint = Dict[str, Any] # Use Any if FNode_Hint is Any

    _SMTFunc_ReturnsFNode_Hint = Callable[..., Any]
    _SMTFunc_ReturnsPySMTType_Hint = Callable[..., Any]
    _SMTFunc_ReturnsBool_Hint = Callable[..., bool] # solve() returns bool
    _SolverClass_Hint = Any


# --- Runtime SMT Setup & Variables ---
SMT_MODE_AVAILABLE = False

# Runtime variables for SMT objects/functions.
# Initialize with dummies. These will be overwritten by real pysmt objects/functions if the import succeeds.
# The type hints for these runtime variables themselves can use the _Hint types for clarity.
FNode_RT: FNode_Hint = None # Runtime variable for the FNode class/type (will hold real or Any)
SMTIntType_RT: SMTTypeInstance_Hint = None # Runtime variable for pysmt.typing.INT (instance)
SMTBoolType_RT: SMTTypeInstance_Hint = None # Runtime variable for pysmt.typing.BOOL (instance)

# SMT function placeholders (runtime variables)
_dummy_runtime_func = lambda *args, **kwargs: None
Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver_RT, TRUE, FALSE, Iff, ForAll, Exists, Plus, Minus, Times, Div = (_dummy_runtime_func,) * 20 # type: ignore
# Note: Solver_RT is the variable for the class, _SolverClass_Hint is for type hints of the class type

try:
    from pysmt.shortcuts import (Symbol as PysmtSymbol_Import, Int as PysmtInt_Import, BOOL as PysmtBOOL_Func_Import, 
                                 Equals as PysmtEquals_Import, And as PysmtAnd_Import, Or as PysmtOr_Import, Not as PysmtNot_Import, 
                                 Implies as PysmtImplies_Import, ExactlyOne as PysmtExactlyOne_Import, Ite as PysmtIte_Import, 
                                 Solver as PysmtSolver_Import, TRUE as PysmtTRUE_Import, FALSE as PysmtFALSE_Import, 
                                 Iff as PysmtIff_Import, ForAll as PysmtForAll_Import, Exists as PysmtExists_Import, 
                                 Plus as PysmtPlus_Import, Minus as PysmtMinus_Import, Times as PysmtTimes_Import, 
                                 Div as PysmtDiv_Import)
    from pysmt.typing import INT as SMT_INT_TYPE_RUNTIME_INSTANCE_IMPORT
    from pysmt.typing import BOOL as SMT_BOOL_TYPE_RUNTIME_INSTANCE_IMPORT
    from pysmt.fnode import FNode as FNode_RUNTIME_CLASS_IMPORT
    
    SMT_MODE_AVAILABLE = True
    
    # Assign actual runtime types/values to our runtime variables
    FNode_RT = FNode_RUNTIME_CLASS_IMPORT
    SMTIntType_RT = SMT_INT_TYPE_RUNTIME_INSTANCE_IMPORT
    SMTBoolType_RT = SMT_BOOL_TYPE_RUNTIME_INSTANCE_IMPORT
    
    # Assign real SMT functions to runtime variables
    Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver_RT, TRUE, FALSE, Iff, ForAll, Exists, Plus, Minus, Times, Div = \
    PysmtSymbol_Import, PysmtInt_Import, PysmtBOOL_Func_Import, PysmtEquals_Import, PysmtAnd_Import, PysmtOr_Import, PysmtNot_Import, PysmtImplies_Import, PysmtExactlyOne_Import, PysmtIte_Import, PysmtSolver_Import, PysmtTRUE_Import, PysmtFALSE_Import, PysmtIff_Import, PysmtForAll_Import, PysmtExists_Import, PysmtPlus_Import, PysmtMinus_Import, PysmtTimes_Import, PysmtDiv_Import

except ImportError:
    SMT_MODE_AVAILABLE = False
    print("WARNING: PySMT library not found. SMT-based tests will be skipped.")
    FNode_RT = Any
    SMTIntType_RT = Any
    SMTBoolType_RT = Any
    
    class _DummySolverRuntime:
        def __init__(self, name: str = "", logic: str = ""): pass
        def add_assertion(self, f: Any): pass 
        def solve(self, options: Dict[str, Any] = {}): return False
        def get_model(self): return None
        def __enter__(self): return self
        def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any): pass
    if not SMT_MODE_AVAILABLE:
        Solver_RT = _DummySolverRuntime # type: ignore

# Global SMT Omega (symbolic representation)
_SMT_OMEGA_NODE: Union[FNode_Hint, None] = None

# create_symbolic_avc_val now uses the runtime SMTIntType_RT and SMTBoolType_RT for Symbol()
# but its return type hint uses SMTSymbolicAVCVal_Hint
def create_symbolic_avc_val(name_prefix: str) -> Union[SMTSymbolicAVCVal_Hint, None]:
    if not SMT_MODE_AVAILABLE: return None
    # At runtime, SMTIntType_RT and SMTBoolType_RT hold the pysmt.typing.INT/BOOL instances
    # These are passed to the runtime Symbol function.
    return {                                                 # This dict is runtime Dict[str, FNode_RT]
        "is_zero": Symbol(f"{name_prefix}_is_zero", SMTBoolType_RT), 
        "is_areo": Symbol(f"{name_prefix}_is_areo", SMTBoolType_RT),
        "is_finite": Symbol(f"{name_prefix}_is_finite", SMTBoolType_RT),
        "val": Symbol(f"{name_prefix}_val", SMTIntType_RT), 
        "name_prefix_debug": name_prefix 
    } # type: ignore 
    # Add type: ignore if checker complains about Dict[str, FNode_RT] vs Dict[str, FNode_Hint]
    # if FNode_RT and FNode_Hint are not seen as compatible by the linter in this return context.
    # Ideally, if FNode_Hint is PysmtFNodeReal and FNode_RT is also PysmtFNodeReal at runtime, it's fine.
    # The issue is the Any fallback.

def get_base_avc_constraints(avc_sym: SMTSymbolicAVCVal_Hint, 
                             omega_smt_node: FNode_Hint,
                             current_omega_py: int) -> List[FNode_Hint]:
    """Basic SMT constraints for a well-formed symbolic AVCVal."""
    if not SMT_MODE_AVAILABLE or avc_sym is None or omega_smt_node is None: return []
    
    resolved_FNode = FNode_RT if SMT_MODE_AVAILABLE else Any 

    # The elements of the list are runtime FNode objects (or Any if SMT not available)
    # The type hint List[FNode_Hint] guides the static checker.
    # If resolved_FNode is FNode_RT (actual FNode class) and FNode_Hint is the same class,
    # this should be compatible. If one is Any, it's also generally fine.
    constraints: List[resolved_FNode] = [ # type: ignore[valid-type]
        ExactlyOne(avc_sym["is_zero"], avc_sym["is_areo"], avc_sym["is_finite"]),
        Implies(avc_sym["is_zero"], Equals(avc_sym["val"], Int(0))),
        Implies(avc_sym["is_areo"], Equals(avc_sym["val"], omega_smt_node)),
    ]
    if current_omega_py == 1:
        constraints.append(Not(avc_sym["is_finite"])) # DFI is empty
    else: # current_omega_py > 1
        constraints.append(
            Implies(avc_sym["is_finite"], 
                    And(avc_sym["val"] >= Int(1), avc_sym["val"] < omega_smt_node))
        )
    return constraints # type: ignore[return-value] # If static checker has issues with List[resolved_FNode] vs List[FNode_Hint]

def avc_equiv_smt(avc1_sym: SMTSymbolicAVCVal_Hint, 
                  avc2_sym: SMTSymbolicAVCVal_Hint) -> Union[FNode_Hint, None]:
    """SMT formula for algebraic equivalence of two symbolic AVCVals."""
    if not SMT_MODE_AVAILABLE or avc1_sym is None or avc2_sym is None: return None
    
    cond_both_unio = And(Or(avc1_sym["is_zero"], avc1_sym["is_areo"]), 
                         Or(avc2_sym["is_zero"], avc2_sym["is_areo"]))
    
    cond_both_dfi_equal_val = And(avc1_sym["is_finite"], 
                                  avc2_sym["is_finite"], 
                                  Equals(avc1_sym["val"], avc2_sym["val"]))
    
    return Or(cond_both_unio, cond_both_dfi_equal_val)

# SMT Logic Builders (Faithful translation of Python ops in Appendix A)
def avc_add_smt_logic(a_sym: SMTSymbolicAVCVal_Hint, b_sym: SMTSymbolicAVCVal_Hint, 
                      res_sym: SMTSymbolicAVCVal_Hint, 
                      omega_smt_node: FNode_Hint) -> Union[FNode_Hint, None]:
    if not SMT_MODE_AVAILABLE: return None
    
    a_is_unio = Or(a_sym["is_zero"], a_sym["is_areo"])
    b_is_unio = Or(b_sym["is_zero"], b_sym["is_areo"])

    res_becomes_a_state = avc_equiv_smt(res_sym, a_sym)
    res_becomes_b_state = avc_equiv_smt(res_sym, b_sym)
    
    case1_a_is_unio = Implies(a_is_unio, res_becomes_b_state)
    case2_b_is_unio_a_is_dfi = Implies(And(Not(a_is_unio), b_is_unio), res_becomes_a_state)

    cond_both_dfi = And(a_sym["is_finite"], b_sym["is_finite"])
    symbolic_sum_val = Plus(a_sym["val"], b_sym["val"])
    
    res_is_dfi_sum_state = And(res_sym["is_finite"], Equals(res_sym["val"], symbolic_sum_val))
    res_is_areo_unio_state = And(res_sym["is_areo"], Equals(res_sym["val"], omega_smt_node)) 

    case3_dfi_dfi_logic = Implies(
        cond_both_dfi,
        Ite(symbolic_sum_val < omega_smt_node,
            res_is_dfi_sum_state,
            res_is_areo_unio_state
        )
    )
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi_logic)

def avc_sub_smt_logic(a_sym: SMTSymbolicAVCVal_Hint, b_sym: SMTSymbolicAVCVal_Hint, 
                      res_sym: SMTSymbolicAVCVal_Hint, omega_smt_node: FNode_Hint) -> Union[FNode_Hint, None]:
    if not SMT_MODE_AVAILABLE: return None

    b_is_unio = Or(b_sym["is_zero"], b_sym["is_areo"])
    a_is_unio = Or(a_sym["is_zero"], a_sym["is_areo"])
    
    res_becomes_a_state = avc_equiv_smt(res_sym, a_sym)
    res_is_areo_unio_state = And(res_sym["is_areo"], Equals(res_sym["val"], omega_smt_node))

    case1_b_is_unio = Implies(b_is_unio, res_becomes_a_state)
    case2_a_is_unio_b_is_dfi = Implies(And(a_is_unio, b_sym["is_finite"]), res_is_areo_unio_state)
    
    cond_both_dfi = And(a_sym["is_finite"], b_sym["is_finite"])
    symbolic_diff_val = Minus(a_sym["val"], b_sym["val"])
    res_is_dfi_diff_state = And(res_sym["is_finite"], Equals(res_sym["val"], symbolic_diff_val))

    case3_dfi_dfi_logic = Implies(
        cond_both_dfi,
        Ite(a_sym["val"] > b_sym["val"], 
            res_is_dfi_diff_state,
            res_is_areo_unio_state
        )
    )
    return And(case1_b_is_unio, case2_a_is_unio_b_is_dfi, case3_dfi_dfi_logic)

def avc_mul_smt_logic(a_sym: SMTSymbolicAVCVal_Hint, b_sym: SMTSymbolicAVCVal_Hint, 
                      res_sym: SMTSymbolicAVCVal_Hint, omega_smt_node: FNode_Hint) -> Union[FNode_Hint, None]:
    if not SMT_MODE_AVAILABLE: return None

    a_is_unio = Or(a_sym["is_zero"], a_sym["is_areo"])
    b_is_unio = Or(b_sym["is_zero"], b_sym["is_areo"])
    
    cond_any_unio_operand_is_areo_aspect = Or(a_sym["is_areo"], b_sym["is_areo"])
    
    res_is_zero_unio_state = And(res_sym["is_zero"], Equals(res_sym["val"], Int(0)))
    res_is_areo_unio_state = And(res_sym["is_areo"], Equals(res_sym["val"], omega_smt_node))

    case1_unio_involved_logic = Implies(
        Or(a_is_unio, b_is_unio),
        Ite(cond_any_unio_operand_is_areo_aspect,
            res_is_areo_unio_state,
            res_is_zero_unio_state
        )
    )
    
    cond_both_dfi = And(a_sym["is_finite"], b_sym["is_finite"])
    symbolic_prod_val = Times(a_sym["val"], b_sym["val"])
    res_is_dfi_prod_state = And(res_sym["is_finite"], Equals(res_sym["val"], symbolic_prod_val))
    
    cond_dfi_prod_valid = And(symbolic_prod_val >= Int(1), symbolic_prod_val < omega_smt_node)

    case2_dfi_dfi_logic = Implies(
        cond_both_dfi,
        Ite(cond_dfi_prod_valid,
            res_is_dfi_prod_state,
            res_is_areo_unio_state 
        )
    )
    return And(case1_unio_involved_logic, case2_dfi_dfi_logic)

def avc_div_smt_logic(a_sym: SMTSymbolicAVCVal_Hint, b_sym: SMTSymbolicAVCVal_Hint, 
                      res_sym: SMTSymbolicAVCVal_Hint, omega_smt_node: FNode_Hint) -> Union[FNode_Hint, None]:
    if not SMT_MODE_AVAILABLE: return None

    b_is_unio = Or(b_sym["is_zero"], b_sym["is_areo"])
    a_is_unio = Or(a_sym["is_zero"], a_sym["is_areo"])
    
    res_is_zero_unio_state = And(res_sym["is_zero"], Equals(res_sym["val"], Int(0)))
    res_is_areo_unio_state = And(res_sym["is_areo"], Equals(res_sym["val"], omega_smt_node))

    rule_b1_consequent = res_is_areo_unio_state
    
    rule_b2_consequent = Ite(a_sym["is_zero"], 
                             res_is_zero_unio_state,
                             res_is_areo_unio_state
                            )

    q_val_smt = Div(a_sym["val"], b_sym["val"])
# Calculate remainder as: a - (b * (a div b))
# Ensure Minus, Times, Div are correctly imported and assigned runtime functions.
# These are PysmtMinus_Import, PysmtTimes_Import, PysmtDiv_Import
    r_val_smt = Minus(a_sym["val"], Times(b_sym["val"], q_val_smt))

    cond_exact_and_valid_dfi_quotient = And(Equals(r_val_smt, Int(0)),
                                            q_val_smt >= Int(1),
                                            q_val_smt < omega_smt_node)
                                            
    res_is_dfi_quotient_state = And(res_sym["is_finite"], Equals(res_sym["val"], q_val_smt))

    rule_b3_consequent = Ite(cond_exact_and_valid_dfi_quotient,
                             res_is_dfi_quotient_state,
                             res_is_areo_unio_state
                            )

    div_logic = Ite(b_is_unio, 
                    rule_b1_consequent,
                    Ite(a_is_unio, 
                        rule_b2_consequent,
                        rule_b3_consequent 
                    )
                   )
    return div_logic

# SMT Prover Function (adapted from Appendix B)
smt_test_results_summary: Dict[int, Dict[str, int]] = {} 
smt_test_failures_details: List[Dict[str, Any]] = []

def _initialize_smt_omega_results(omega_py_val: int):
    if omega_py_val not in smt_test_results_summary:
        smt_test_results_summary[omega_py_val] = {"passed": 0, "failed": 0, "skipped": 0}

def prove_or_find_counterexample_smt(
    property_name: str, 
    current_omega_py: int, 
    setup_formulas: List[FNode_Hint], 
    property_to_verify: FNode_Hint, 
    symbolic_inputs_for_model: List[SMTSymbolicAVCVal_Hint], 
    expect_property_to_hold: bool, 
    is_existential: bool = False,
    timeout_ms: int = SMT_TIMEOUT_DEFAULT_MS):
    
    global _SMT_OMEGA_NODE
    if not SMT_MODE_AVAILABLE:
        _initialize_smt_omega_results(current_omega_py)
        print(f"SKIPPING SMT Property '{property_name}' for Ω={current_omega_py} (SMT_MODE_AVAILABLE=False)")
        smt_test_results_summary[current_omega_py]["skipped"] += 1
        return

    _SMT_OMEGA_NODE = Int(current_omega_py) 
    _initialize_smt_omega_results(current_omega_py)

    property_holds_observed = False
    counterexample_witness_str = "N/A"
    solver_name = "z3" 
    
    final_setup = list(setup_formulas) 
    for sym_val_dict in symbolic_inputs_for_model:
        if sym_val_dict: 
            # get_base_avc_constraints expects SMTSymbolicAVCVal_Hint and FNode_Hint
            # _SMT_OMEGA_NODE is FNode_RT at runtime. If FNode_Hint and FNode_RT are compatible, it's fine.
            # Type checker might need an assert or cast if strictly checking _SMT_OMEGA_NODE's type here.
            # For now, assume runtime types align or are handled by Any fallbacks.
            constraints_for_sym = get_base_avc_constraints(sym_val_dict, _SMT_OMEGA_NODE, current_omega_py) # type: ignore[arg-type]
            final_setup.extend(constraints_for_sym)


    print(f"  Attempting to verify: '{property_name}' for Ω={current_omega_py} (Expect: {'Hold' if expect_property_to_hold else 'Fail/Not Hold'})")

    solve_result = None
    try:
        with Solver_RT(name=solver_name, logic="QF_LIA") as s: 
            for f_setup in final_setup:
                if f_setup is not None: s.add_assertion(f_setup)
            
            formula_to_check = property_to_verify
            if not is_existential: 
                formula_to_check = Not(property_to_verify)
            
            if formula_to_check is not None: s.add_assertion(formula_to_check)
            else: 
                raise ValueError("Formula to check is None in SMT solver.")

            solve_result = s.solve(options={'timeout': timeout_ms})

            if is_existential:
                if solve_result: 
                    property_holds_observed = True
                    model = s.get_model()
                    ce_parts = []
                    for avc_sym_dict in symbolic_inputs_for_model:
                        if not avc_sym_dict: continue
                        name = avc_sym_dict.get("name_prefix_debug", "var")
                        try:
                            is_z = model.get_value(avc_sym_dict['is_zero']).is_true()
                            is_a = model.get_value(avc_sym_dict['is_areo']).is_true()
                            is_f = model.get_value(avc_sym_dict['is_finite']).is_true()
                            val = model.get_value(avc_sym_dict['val']).constant_value()
                            state_str = "Unio('zero')" if is_z else ("Unio('areo')" if is_a else (str(val) if is_f else "UnknownState"))
                            ce_parts.append(f"{name}={state_str}")
                        except Exception as e_model:
                            ce_parts.append(f"{name}=?(err:{e_model})")
                    counterexample_witness_str = "; ".join(ce_parts)
                else: 
                    property_holds_observed = False
                    counterexample_witness_str = "No witness found or timeout." if solve_result is False else "Timeout/Unknown"

            else: # Universal property
                if not solve_result: 
                    property_holds_observed = True
                else: 
                    property_holds_observed = False
                    if solve_result: 
                        model = s.get_model()
                        ce_parts = []
                        for avc_sym_dict in symbolic_inputs_for_model:
                            if not avc_sym_dict: continue
                            name = avc_sym_dict.get("name_prefix_debug", "var")
                            try:
                                is_z = model.get_value(avc_sym_dict['is_zero']).is_true()
                                is_a = model.get_value(avc_sym_dict['is_areo']).is_true()
                                is_f = model.get_value(avc_sym_dict['is_finite']).is_true()
                                val = model.get_value(avc_sym_dict['val']).constant_value()
                                state_str = "Unio('zero')" if is_z else ("Unio('areo')" if is_a else (str(val) if is_f else "UnknownState"))
                                ce_parts.append(f"{name}={state_str}")
                            except Exception as e_model:
                                ce_parts.append(f"{name}=?(err:{e_model})")
                        counterexample_witness_str = "; ".join(ce_parts)
                    else: 
                        counterexample_witness_str = "Timeout/Unknown for Not(Property)."
                        
    except Exception as e_smt:
        print(f"    SMT SOLVER ERROR for '{property_name}' Ω={current_omega_py}: {e_smt}")
        property_holds_observed = False 
        counterexample_witness_str = f"SMT Solver Exception: {e_smt}"


    success_for_summary = (property_holds_observed == expect_property_to_hold)
    status_emoji = "✅" if success_for_summary else "❌"
    final_message_parts = [status_emoji]
    
    if is_existential:
        if property_holds_observed: 
            final_message_parts.append("Witness FOUND." + (" As expected." if expect_property_to_hold else " UNEXPECTEDLY!"))
        else: 
            final_message_parts.append("No witness found." + (" As expected (non-existence confirmed)." if not expect_property_to_hold else " UNEXPECTEDLY (existence claim FAILED)."))
    else: # Universal
        if property_holds_observed: 
            final_message_parts.append("Property HOLDS universally." + (" As expected." if expect_property_to_hold else " UNEXPECTEDLY!"))
        else: 
            final_message_parts.append("Property FAILED universally." + (" As expected (non-universality confirmed)." if not expect_property_to_hold else " UNEXPECTEDLY (counterexample found)."))

    if success_for_summary:
        smt_test_results_summary[current_omega_py]["passed"] += 1
    else:
        smt_test_results_summary[current_omega_py]["failed"] += 1
        smt_test_failures_details.append({
            "property": property_name, "omega": current_omega_py,
            "expected_to_hold": expect_property_to_hold,
            "observed_holds": property_holds_observed,
            "message": " ".join(final_message_parts),
            "witness_ce": counterexample_witness_str,
            "is_existential": is_existential
        })
    
    print(f"    {' '.join(final_message_parts)}")
    if not property_holds_observed and not is_existential and solve_result : 
        print(f"      Counterexample: {counterexample_witness_str}")
    elif property_holds_observed and is_existential and solve_result: 
        print(f"      Witness: {counterexample_witness_str}")
    elif not success_for_summary: 
        print(f"      Details: {counterexample_witness_str}")


# --- End of Part 2: SMT Harness Core ---


# --- Part 3: Native Python Brute-Force Harness (Initial Tests) ---
# Test results storage for native tests
native_test_results_summary: Dict[int, Dict[str, int]] = {} # {omega: {"passed": x, "failed": y}}
native_test_failures_details: List[Dict[str, Any]] = []

def _initialize_native_omega_results(omega_py_val: int):
    if omega_py_val not in native_test_results_summary:
        native_test_results_summary[omega_py_val] = {"passed": 0, "failed": 0}

def _report_native_test_result(property_name: str, current_omega_py: int, passed: bool, failure_info: str = ""):
    _initialize_native_omega_results(current_omega_py)
    status_emoji = "✅" if passed else "❌"
    print(f"  {status_emoji} Native Test: '{property_name}' for Ω={current_omega_py} ... {'PASS' if passed else 'FAIL'}")
    if passed:
        native_test_results_summary[current_omega_py]["passed"] += 1
    else:
        native_test_results_summary[current_omega_py]["failed"] += 1
        details = {
            "property": property_name, "omega": current_omega_py,
            "info": failure_info
        }
        native_test_failures_details.append(details)
        print(f"    Failure Info: {failure_info}")

def get_s_omega_for_native_tests(current_omega: int) -> List[AVCVal]:
    """Helper to get all elements in S_Omega for native tests."""
    if current_omega == 1:
        return [ZERO_UNIO, AREO_UNIO] # Test with both canonical Unio objects
    else:
        # Include both Unio objects and DFI elements
        elements: List[AVCVal] = [ZERO_UNIO, AREO_UNIO]
        elements.extend(list(range(1, current_omega)))
        return elements

# --- Native Test Function Definitions ---

def native_test_operational_totality(current_omega_py: int, omega_native_max: int):
    """Native test for operational totality (closure) of all 4 ops."""
    if current_omega_py > omega_native_max : 
        print(f"  SKIPPING Native Test: 'Operational Totality' for Ω={current_omega_py} (>{omega_native_max})")
        _initialize_native_omega_results(current_omega_py) 
        # Increment skip count for each operation that would have been tested
        native_test_results_summary[current_omega_py]["skipped"] = native_test_results_summary[current_omega_py].get("skipped",0) + 4 
        return False # Return False as not all tests ran as intended for this Omega

    set_core_avca_omega(current_omega_py)
    s_omega = get_s_omega_for_native_tests(current_omega_py)
    operations = {
        "add": avc_add, "sub": avc_sub,
        "mul": avc_mul, "div": avc_div
    }
    overall_all_ops_passed = True
    
    for op_name, op_func in operations.items():
        current_op_suite_passed = True # Tracks if all pairs for *this* op passed
        first_failure_info_for_op = ""

        # Outer try for issues with iterating or op_func itself not being callable
        try: 
            for a in s_omega:
                for b in s_omega:
                    try:
                        result = op_func(a, b)
                        _check_val(result, current_omega_py, f"{op_name}_result({prettify_element_git1(a)},{prettify_element_git1(b)})")
                    except (ValueError, TypeError) as e:
                        current_op_suite_passed = False
                        overall_all_ops_passed = False
                        first_failure_info_for_op = (
                            f"Operation {op_name}(a={prettify_element_git1(a)}, b={prettify_element_git1(b)}) "
                            f"raised error: {e}"
                        )
                        break # Stop testing pairs for this op_name on first error
                if not current_op_suite_passed:
                    break # Stop testing this op_name
            
            # Report result for the current operation suite
            if current_op_suite_passed:
                _report_native_test_result(f"Operational Totality for {op_name}", current_omega_py, True)
            else:
                # This report will only happen if the loop completed but current_op_suite_passed is false,
                # or if it broke and we need to report the first failure.
                _report_native_test_result(f"Operational Totality for {op_name}", current_omega_py, False, first_failure_info_for_op)

        except Exception as outer_e: # Catch any unexpected errors in the looping/setup itself
            current_op_suite_passed = False # Mark this op as failed
            overall_all_ops_passed = False
            failure_info = f"Outer error during {op_name} test for Ω={current_omega_py}: {outer_e}"
            _report_native_test_result(f"Operational Totality for {op_name}", current_omega_py, False, failure_info)
            # No need to break here, loop will go to next op_name

    return overall_all_ops_passed


def native_test_commutativity_add(current_omega_py: int, omega_native_max: int):
    if current_omega_py > omega_native_max:
        print(f"  SKIPPING Native Test: 'Commutativity of Add' for Ω={current_omega_py} (>{omega_native_max})")
        _initialize_native_omega_results(current_omega_py)
        native_test_results_summary[current_omega_py]["skipped"] = native_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    set_core_avca_omega(current_omega_py)
    s_omega = get_s_omega_for_native_tests(current_omega_py)
    passed = True
    failure_info = ""
    for a in s_omega:
        for b in s_omega:
            try:
                res1 = avc_add(a, b)
                res2 = avc_add(b, a)
                if res1 != res2: # Uses Unio.__eq__ for algebraic equivalence
                    passed = False
                    failure_info = f"Add: {prettify_element_git1(a)}⊕{prettify_element_git1(b)} ({prettify_element_git1(res1)}) != {prettify_element_git1(b)}⊕{prettify_element_git1(a)} ({prettify_element_git1(res2)})"
                    break
            except (ValueError, TypeError) as e:
                passed = False
                failure_info = f"Add({prettify_element_git1(a)},{prettify_element_git1(b)}) error: {e}"
                break
        if not passed: break
    _report_native_test_result("Commutativity of Addition (⊕_v1.1)", current_omega_py, passed, failure_info)
    return passed

def native_test_commutativity_mul(current_omega_py: int, omega_native_max: int):
    if current_omega_py > omega_native_max:
        print(f"  SKIPPING Native Test: 'Commutativity of Mul' for Ω={current_omega_py} (>{omega_native_max})")
        _initialize_native_omega_results(current_omega_py)
        native_test_results_summary[current_omega_py]["skipped"] = native_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    set_core_avca_omega(current_omega_py)
    s_omega = get_s_omega_for_native_tests(current_omega_py)
    passed = True
    failure_info = ""
    for a in s_omega:
        for b in s_omega:
            try:
                res1 = avc_mul(a, b)
                res2 = avc_mul(b, a)
                if res1 != res2: # Uses Unio.__eq__
                    passed = False
                    failure_info = f"Mul: {prettify_element_git1(a)}⊗{prettify_element_git1(b)} ({prettify_element_git1(res1)}) != {prettify_element_git1(b)}⊗{prettify_element_git1(a)} ({prettify_element_git1(res2)})"
                    break
            except (ValueError, TypeError) as e:
                passed = False
                failure_info = f"Mul({prettify_element_git1(a)},{prettify_element_git1(b)}) error: {e}"
                break
        if not passed: break
    _report_native_test_result("Commutativity of Multiplication (⊗_v1.2)", current_omega_py, passed, failure_info)
    return passed
def native_test_associativity_add(current_omega_py: int, omega_native_max: int):
    property_name = "Associativity of Addition (⊕_v1.1)"
    if current_omega_py > omega_native_max:
        print(f"  SKIPPING Native Test: '{property_name}' for Ω={current_omega_py} (>{omega_native_max})")
        _initialize_native_omega_results(current_omega_py)
        native_test_results_summary[current_omega_py]["skipped"] = native_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    set_core_avca_omega(current_omega_py)
    s_omega = get_s_omega_for_native_tests(current_omega_py)
    passed = True
    failure_info = ""
    
    # Expected behavior: Holds iff Ω <= 2
    expected_to_hold = (current_omega_py <= 2)

    for a in s_omega:
        for b in s_omega:
            for c in s_omega:
                try:
                    lhs = avc_add(avc_add(a, b), c)
                    rhs = avc_add(a, avc_add(b, c))
                    current_holds = (lhs == rhs) # Algebraic equivalence via Unio.__eq__
                    
                    if not current_holds and expected_to_hold:
                        passed = False
                        failure_info = (f"Add Assoc ERRONEOUSLY FAILED for Ω={current_omega_py} (expected to hold): "
                                        f"a={prettify_element_git1(a)}, b={prettify_element_git1(b)}, c={prettify_element_git1(c)} -> "
                                        f"LHS=({prettify_element_git1(a)}⊕{prettify_element_git1(b)})⊕{prettify_element_git1(c)} = {prettify_element_git1(avc_add(a,b))}⊕{prettify_element_git1(c)} = {prettify_element_git1(lhs)}, "
                                        f"RHS={prettify_element_git1(a)}⊕({prettify_element_git1(b)}⊕{prettify_element_git1(c)}) = {prettify_element_git1(a)}⊕{prettify_element_git1(avc_add(b,c))} = {prettify_element_git1(rhs)}")
                        break
                    if current_holds and not expected_to_hold:
                        passed = False
                        failure_info = (f"Add Assoc ERRONEOUSLY PASSED for Ω={current_omega_py} (expected to fail): "
                                        f"a={prettify_element_git1(a)}, b={prettify_element_git1(b)}, c={prettify_element_git1(c)} -> "
                                        f"LHS={prettify_element_git1(lhs)}, RHS={prettify_element_git1(rhs)}")
                        # We don't break here; we want to see if it holds for ALL. If it does, it's a failure against expectation.
                        # Instead, we should note this specific pass as unexpected. For simplicity, we'll just flag the first.
                        # A more sophisticated test would count unexpected passes.
                        # For now, one unexpected pass means the overall "passed" (matching expectation) is false.
                        break 
                except (ValueError, TypeError) as e:
                    passed = False
                    failure_info = f"Add Assoc error: a={prettify_element_git1(a)},b={prettify_element_git1(b)},c={prettify_element_git1(c)} -> {e}"
                    break
            if not passed: break
        if not passed: break
    
    # Final check: if expected_to_hold is False, then `passed` should be False (meaning at least one counterexample was found as expected)
    # or rather, the test passes if the observed behavior matches the expectation.
    final_test_passed_status = (passed == expected_to_hold) if not expected_to_hold else passed

    _report_native_test_result(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                               current_omega_py, final_test_passed_status, failure_info if not final_test_passed_status else "")
    return final_test_passed_status

def native_test_associativity_mul(current_omega_py: int, omega_native_max: int):
    property_name = "Associativity of Multiplication (⊗_v1.2)"
    if current_omega_py > omega_native_max:
        print(f"  SKIPPING Native Test: '{property_name}' for Ω={current_omega_py} (>{omega_native_max})")
        _initialize_native_omega_results(current_omega_py)
        native_test_results_summary[current_omega_py]["skipped"] = native_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    set_core_avca_omega(current_omega_py)
    s_omega = get_s_omega_for_native_tests(current_omega_py)
    passed = True
    failure_info = ""
    
    # Expected behavior: Holds for all Ω
    expected_to_hold = True

    for a in s_omega:
        for b in s_omega:
            for c in s_omega:
                try:
                    lhs = avc_mul(avc_mul(a, b), c)
                    rhs = avc_mul(a, avc_mul(b, c))
                    if lhs != rhs:
                        passed = False
                        failure_info = (f"Mul Assoc FAILED: a={prettify_element_git1(a)}, b={prettify_element_git1(b)}, c={prettify_element_git1(c)} -> "
                                        f"LHS={prettify_element_git1(lhs)}, RHS={prettify_element_git1(rhs)}")
                        break
                except (ValueError, TypeError) as e:
                    passed = False
                    failure_info = f"Mul Assoc error: a={prettify_element_git1(a)},b={prettify_element_git1(b)},c={prettify_element_git1(c)} -> {e}"
                    break
            if not passed: break
        if not passed: break
    _report_native_test_result(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                               current_omega_py, passed, failure_info)
    return passed

def native_test_distributivity_mul_over_add(current_omega_py: int, omega_native_max: int):
    # Left Distributivity: a ⊗ (b ⊕ c) == (a ⊗ b) ⊕ (a ⊗ c)
    property_name = "Left Distributivity (⊗_v1.2 over ⊕_v1.1)"
    if current_omega_py > omega_native_max: # O(N^3)
        print(f"  SKIPPING Native Test: '{property_name}' for Ω={current_omega_py} (>{omega_native_max})")
        _initialize_native_omega_results(current_omega_py)
        native_test_results_summary[current_omega_py]["skipped"] = native_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    set_core_avca_omega(current_omega_py)
    s_omega = get_s_omega_for_native_tests(current_omega_py)
    passed = True
    failure_info = ""

    # Expected behavior: Holds iff Ω <= 2
    expected_to_hold = (current_omega_py <= 2)
    
    # Temp flag to see if any case matches expectation when failure is expected
    found_expected_failure = False 

    for a in s_omega:
        for b in s_omega:
            for c in s_omega:
                try:
                    # LHS: a ⊗ (b ⊕ c)
                    b_plus_c = avc_add(b, c)
                    lhs = avc_mul(a, b_plus_c)

                    # RHS: (a ⊗ b) ⊕ (a ⊗ c)
                    a_mul_b = avc_mul(a, b)
                    a_mul_c = avc_mul(a, c)
                    rhs = avc_add(a_mul_b, a_mul_c)

                    current_holds = (lhs == rhs)

                    if not current_holds:
                        found_expected_failure = True # A counterexample was found
                        if expected_to_hold: # If it was expected to hold, this is a failure
                            passed = False
                            failure_info = (f"Distributivity ERRONEOUSLY FAILED for Ω={current_omega_py} (expected to hold): "
                                            f"a={prettify_element_git1(a)},b={prettify_element_git1(b)},c={prettify_element_git1(c)} -> "
                                            f"LHS={prettify_element_git1(lhs)} (a⊗(b⊕{prettify_element_git1(b_plus_c)})), "
                                            f"RHS={prettify_element_git1(rhs)} ((a⊗b)⊕(a⊗c) = {prettify_element_git1(a_mul_b)}⊕{prettify_element_git1(a_mul_c)})")
                            break
                    elif current_holds and not expected_to_hold:
                        # If it holds but was expected to fail, we need to continue to see if it holds FOR ALL cases.
                        # If it holds for ALL cases, then `passed` (which means matching expectation) becomes False.
                        pass # Continue checking; if all hold, then it's an unexpected pass.

                except (ValueError, TypeError) as e:
                    passed = False # Test expectation matching failed due to error
                    failure_info = f"Distributivity error: a={prettify_element_git1(a)},b={prettify_element_git1(b)},c={prettify_element_git1(c)} -> {e}"
                    break
            if not passed : break # An error occurred or an unexpected failure
        if not passed : break

    # Final status determination
    if not expected_to_hold: # We expected failures
        final_test_passed_status = found_expected_failure # Test passes if we found at least one failure
        if not found_expected_failure: # It held universally but was expected to fail
             failure_info = f"Distributivity ERRONEOUSLY PASSED for Ω={current_omega_py} (expected to fail for at least one case)"
    else: # We expected it to hold universally
        final_test_passed_status = passed # `passed` is still True if no unexpected failures
    
    _report_native_test_result(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                               current_omega_py, final_test_passed_status, failure_info if not final_test_passed_status else "")
    return final_test_passed_status

def native_test_additive_identity(current_omega_py: int, omega_native_max: int):
    property_name = "Additive Identity (Unio for ⊕_v1.1)"
    if current_omega_py > omega_native_max: # O(N)
        print(f"  SKIPPING Native Test: '{property_name}' for Ω={current_omega_py} (>{omega_native_max})")
        _initialize_native_omega_results(current_omega_py)
        native_test_results_summary[current_omega_py]["skipped"] = native_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    set_core_avca_omega(current_omega_py)
    s_omega = get_s_omega_for_native_tests(current_omega_py)
    passed = True
    failure_info = ""

    # Test with both ZERO_UNIO and AREO_UNIO as identity candidates
    identity_candidates = [ZERO_UNIO, AREO_UNIO]
    
    for identity_candidate in identity_candidates:
        # Check if it's a valid element for the current Omega first
        # (though canonicals should always be fine conceptually)
        try:
            _check_val(identity_candidate, current_omega_py, "identity_candidate")
        except: # Should not happen for ZU/AU
            passed = False
            failure_info = f"Identity candidate {prettify_element_git1(identity_candidate)} is not valid for Ω={current_omega_py}"
            break

        for a in s_omega:
            try:
                res_left = avc_add(identity_candidate, a)
                res_right = avc_add(a, identity_candidate)
                if res_left != a or res_right != a: # Algebraic equivalence
                    passed = False
                    failure_info = (f"Identity check FAILED for candidate {prettify_element_git1(identity_candidate)} with a={prettify_element_git1(a)}: "
                                    f"{prettify_element_git1(identity_candidate)}⊕a = {prettify_element_git1(res_left)}; "
                                    f"a⊕{prettify_element_git1(identity_candidate)} = {prettify_element_git1(res_right)}")
                    break
            except (ValueError, TypeError) as e:
                passed = False
                failure_info = f"Identity check error with {prettify_element_git1(identity_candidate)}, a={prettify_element_git1(a)} -> {e}"
                break
        if not passed: break
        
    _report_native_test_result(property_name, current_omega_py, passed, failure_info)
    return passed

def native_test_additive_inverses(current_omega_py: int, omega_native_max: int):
    property_name = "Additive Inverses (⊕_v1.1)"
    if current_omega_py > omega_native_max: # O(N^2) for existence, more for uniqueness patterns
        print(f"  SKIPPING Native Test: '{property_name}' for Ω={current_omega_py} (>{omega_native_max})")
        _initialize_native_omega_results(current_omega_py)
        native_test_results_summary[current_omega_py]["skipped"] = native_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    set_core_avca_omega(current_omega_py)
    s_omega = get_s_omega_for_native_tests(current_omega_py)
    all_elements_have_inverse = True
    uniqueness_holds_as_expected = True
    failure_info = ""

    # Expected uniqueness: True if Ω <= 2, False if Ω >= 3
    expected_universal_uniqueness = (current_omega_py <= 2)

    for a in s_omega:
        inverses_found_for_a = []
        try:
            for x in s_omega:
                if avc_add(a, x) == ZERO_UNIO: # Check against algebraic Unio (ZERO_UNIO is fine as representative)
                    # Store the actual x object found, not just its value if DFI
                    inverses_found_for_a.append(x)
            
            if not inverses_found_for_a:
                all_elements_have_inverse = False
                failure_info = f"Existence FAILED: No inverse found for a={prettify_element_git1(a)}."
                break

            # Check uniqueness based on algebraic distinctness
            algebraically_distinct_inverses = []
            for inv in inverses_found_for_a:
                is_present = any(inv == dist_inv for dist_inv in algebraically_distinct_inverses)
                if not is_present:
                    algebraically_distinct_inverses.append(inv)
            
            num_distinct_inverses = len(algebraically_distinct_inverses)

            if isinstance(a, Unio):
                if num_distinct_inverses != 1 or not (algebraically_distinct_inverses[0] == ZERO_UNIO):
                    uniqueness_holds_as_expected = False
                    failure_info = f"Uniqueness for Unio FAILED: Expected 1 inverse (Unio), found {num_distinct_inverses} for a={prettify_element_git1(a)}. Inverses: {[prettify_element_git1(i) for i in algebraically_distinct_inverses]}"
                    break
            elif isinstance(a, int): # DFI element
                expected_num_dfi_inverses = a # DFI value `a` has `a` DFI inverses
                
                # Count only DFI inverses among those found
                actual_dfi_inverses_found = [inv for inv in algebraically_distinct_inverses if isinstance(inv, int)]
                num_actual_dfi_inverses = len(actual_dfi_inverses_found)

                if current_omega_py == 2: # DFI a=1 should have 1 DFI inverse (itself)
                    if num_distinct_inverses != 1:
                        uniqueness_holds_as_expected = False
                        failure_info = f"Uniqueness for DFI a={a} (Ω=2) FAILED: Expected 1 unique inverse, found {num_distinct_inverses}. Inverses: {[prettify_element_git1(i) for i in algebraically_distinct_inverses]}"
                        break
                elif current_omega_py >= 3:
                    if num_actual_dfi_inverses != a: # Check |inv_DFI(a)| = a_val
                        uniqueness_holds_as_expected = False
                        failure_info = (f"Inverse count for DFI a={a} (Ω={current_omega_py}) FAILED: "
                                        f"Expected {a} DFI inverses, found {num_actual_dfi_inverses}. "
                                        f"Found DFI inverses: {[prettify_element_git1(i) for i in actual_dfi_inverses_found]}")
                        break
                    if a == 1 and num_distinct_inverses != 1: # DFI a=1 should be unique
                        uniqueness_holds_as_expected = False
                        failure_info = f"Uniqueness for DFI a=1 (Ω={current_omega_py}) FAILED: Expected 1 unique inverse, found {num_distinct_inverses}. Inverses: {[prettify_element_git1(i) for i in algebraically_distinct_inverses]}"
                        break
                    if a > 1 and num_distinct_inverses == 1: # DFI a>1 should NOT be unique
                         uniqueness_holds_as_expected = False
                         failure_info = f"Uniqueness for DFI a={a} (Ω={current_omega_py}) ERRONEOUSLY OBSERVED: Expected multiple inverses, found 1. Inverses: {[prettify_element_git1(i) for i in algebraically_distinct_inverses]}"
                         break

        except (ValueError, TypeError) as e:
            all_elements_have_inverse = False # Consider it a failure if an error occurs during test
            uniqueness_holds_as_expected = False # Cannot confirm uniqueness
            failure_info = f"Additive inverse check error for a={prettify_element_git1(a)} -> {e}"
            break
        if not all_elements_have_inverse or not uniqueness_holds_as_expected:
            break 
            
    final_status = all_elements_have_inverse and uniqueness_holds_as_expected
    _report_native_test_result(property_name + f" (Existence & Uniqueness Pattern)", 
                               current_omega_py, final_status, failure_info if not final_status else "")
    return final_status    
# (Helper for prettifying output, can use the one from GIT.1 or define here)
def prettify_element_git1(e: AVCVal) -> str: # From GIT.1 for consistency
    if isinstance(e, Unio):
        # For native tests, good to see the actual object if they differ
        return repr(e) 
    return str(e)

# --- End of Part 3: Native Python Brute-Force Harness ---


# --- Part 4: Test Runner & Reporting (Basic Structure for Native Tests) ---
def run_native_foundational_tests(omega_values_to_test: List[int], omega_native_max_val: int):
    print("\n====== Running Native Foundational Stress Tests ======")
    for omega_val in omega_values_to_test:
        print(f"\n--- Native Tests for Ω = {omega_val} ---")
        if omega_val == 0: # Should be caught by set_core_avca_omega, but good to check
            print(f"  SKIPPING Native Tests for invalid Ω = {omega_val}")
            continue
        if omega_val > omega_native_max_val and omega_native_max_val > 0 : # omega_native_max_val=0 could mean no limit
            print(f"  Note: Exhaustive tests for Ω={omega_val} may be skipped or run with sampling if > OMEGA_NATIVE_MAX ({omega_native_max_val}).")

        native_test_operational_totality(omega_val, omega_native_max_val)
        native_test_commutativity_add(omega_val, omega_native_max_val)
        native_test_associativity_add(omega_val, omega_native_max_val) # New
        native_test_additive_identity(omega_val, omega_native_max_val) # New
        native_test_additive_inverses(omega_val, omega_native_max_val) # New
        
        native_test_commutativity_mul(omega_val, omega_native_max_val)
        native_test_associativity_mul(omega_val, omega_native_max_val) # New
        
        native_test_distributivity_mul_over_add(omega_val, omega_native_max_val) # New
        # Add more native test calls here as they are developed

    print("\n--- Native Test Summary ---")
    total_passed_native = 0
    total_failed_native = 0
    total_skipped_native = 0
    # Ensure summary is initialized if no tests ran for some omegas (e.g. if omega_values_to_test is empty)
    for omega_val_summary in omega_values_to_test:
        if omega_val_summary not in native_test_results_summary:
            _initialize_native_omega_results(omega_val_summary) # Ensure entry exists

    for omega_val, results in sorted(native_test_results_summary.items()): # Sort by Omega for consistent output
        passed = results.get("passed", 0)
        failed = results.get("failed", 0)
        skipped = results.get("skipped", 0)
        total_passed_native += passed
        total_failed_native += failed
        total_skipped_native += skipped
        print(f"  Ω={omega_val}: Passed={passed}, Failed={failed}, Skipped={skipped}")
    
    if native_test_failures_details:
        print("\n  --- Native Test Failure Details ---")
        for failure in sorted(native_test_failures_details, key=lambda x: x['omega']): # Sort failures by Omega
            print(f"    Ω={failure['omega']}, Property='{failure['property']}': {failure['info']}")
    
    if total_failed_native == 0 and total_passed_native > 0 :
        print("✅ All executed native foundational tests PASSED!")
    elif total_passed_native == 0 and total_failed_native == 0 and total_skipped_native > 0:
        print("⚪ All native foundational tests were SKIPPED (likely due to OMEGA_NATIVE_MAX or empty test list for Omega).")
    elif total_failed_native == 0 and total_passed_native == 0 and total_skipped_native == 0:
        print("⚪ No native foundational tests were executed or recorded.")
    else:
        print("❌ SOME NATIVE FOUNDATIONAL TESTS FAILED!")
    print("==========================================")

# --- Main Execution Block ---
if __name__ == "__main__":
    print("AVCA Max-Brutality Stress-Testing & Research Programme Harness")
    print(f"SMT Mode Available: {SMT_MODE_AVAILABLE}")
    
    # --- Configuration for this run ---
    omegas_for_testing = [1, 2, 3, 4] # Example Omega values to test
    # Max Omega for which *exhaustive native* tests will run fully.
    # Higher Omega values might have their native tests skipped or sampled.
    current_omega_native_max = OMEGA_NATIVE_MAX_DEFAULT 

    # == Run Native Foundational Tests ==
    run_native_foundational_tests(omegas_for_testing, current_omega_native_max)

    # == Placeholder for SMT Test Suite Runner ==
    # def run_smt_tests(omega_values_to_test: List[int]):
    #     print("\n====== Running SMT Stress Tests (Placeholder) ======")
    #     if not SMT_MODE_AVAILABLE:
    #         print("SMT tests cannot run because PySMT/Solver is not available.")
    #         return
    #     # Example: Call SMT test for commutativity of add for Ω=3
    #     # setup_smt_test_commutativity_add(3) # This would internally call prove_or_find_counterexample_smt
    # run_smt_tests(omegas_for_testing)

    print("\nProgramme Finished.")