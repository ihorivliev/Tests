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
# --- SMT Symbolic Unio Constants ---
# These represent specific Unio aspects for property definitions.
# They need base constraints asserted when used in a test.
# Define them here so they are created once if SMT_MODE_AVAILABLE.
# Their constraints will be added within specific test setups.

# Type hints for these global constants
ZU_const_sym: Union[SMTSymbolicAVCVal_Hint, None] = None
AS_const_sym: Union[SMTSymbolicAVCVal_Hint, None] = None

if SMT_MODE_AVAILABLE:
    ZU_const_sym = create_symbolic_avc_val("ZU_const")
    AS_const_sym = create_symbolic_avc_val("AS_const")

def get_smt_unio_constant_constraints( 
    zu_sym: SMTSymbolicAVCVal_Hint, 
    as_sym: SMTSymbolicAVCVal_Hint, 
    omega_smt_node_for_constraints: FNode_Hint
    ) -> List[FNode_Hint]:
    """
    Returns base constraints specifically for ZU_const_sym and AS_const_sym.
    These assert they are Unio('zero') and Unio('areo') respectively.
    """
    if not SMT_MODE_AVAILABLE or zu_sym is None or as_sym is None or omega_smt_node_for_constraints is None:
        return []
    
    # Runtime functions (Equals, Iff, TRUE, FALSE, Int) are already globally defined or dummied
    
    # Constraints for zu_sym to be ZU (Unio('zero'))
    # zu_sym["is_zero"] is an SMT Boolean variable
    # TRUE() and FALSE() are SMT Boolean constants
    # Use Iff for Boolean equivalence
    zu_constraints: List[Any] = [ 
        Iff(zu_sym["is_zero"], TRUE()),   # Changed Equals to Iff
        Iff(zu_sym["is_areo"], FALSE()),  # Changed Equals to Iff
        Iff(zu_sym["is_finite"], FALSE()),# Changed Equals to Iff
        Equals(zu_sym["val"], Int(0))     # Equals is correct for Integers
    ]
    
    # Constraints for as_sym to be AS (Unio('areo'))
    as_constraints: List[Any] = [ 
        Iff(as_sym["is_zero"], FALSE()),  # Changed Equals to Iff
        Iff(as_sym["is_areo"], TRUE()),   # Changed Equals to Iff
        Iff(as_sym["is_finite"], FALSE()),# Changed Equals to Iff
        Equals(as_sym["val"], omega_smt_node_for_constraints) # Equals is correct for Integers
    ]
    return zu_constraints + as_constraints # type: ignore[return-value]
    # The type: ignore[return-value] might be needed if Pylance has trouble reconciling
    # List[Any] (from runtime) with List[FNode_Hint] (static hint) when SMT_MODE_AVAILABLE is true.
    # Ideally, if FNode_Hint is seen as the real FNode by Pylance, this should align.
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
    timeout_ms: int = SMT_TIMEOUT_DEFAULT_MS): # timeout_ms was removed from s.solve(), but kept here for future use if needed
    
    global _SMT_OMEGA_NODE # This is _SMT_OMEGA_NODE: Union[FNode_Hint, None] = None
    if not SMT_MODE_AVAILABLE:
        _initialize_smt_omega_results(current_omega_py) # Make sure an entry exists for skipped count
        # Using _report_native_test_result for skipped SMT tests for unified summary, prefix name
        _report_native_test_result(f"SMT: {property_name} SKIPPED (SMT UNAVAILABLE)", current_omega_py, True, "SMT_UNAVAILABLE") 
        smt_test_results_summary[current_omega_py]["skipped"] +=1 # Ensure this is the SMT summary
        if property_name in smt_test_results_summary[current_omega_py]: # Adjust if native report already incremented passed
             smt_test_results_summary[current_omega_py]["passed"] -=1
        return

    _SMT_OMEGA_NODE = Int(current_omega_py) # type: ignore # Runtime Int function
    _initialize_smt_omega_results(current_omega_py)

    property_holds_observed = False
    model_str = "N/A" # Changed from counterexample_witness_str for clarity
    solver_name = "z3" 
    
    final_setup = list(setup_formulas) 
    for sym_val_dict in symbolic_inputs_for_model:
        if sym_val_dict: 
            # get_base_avc_constraints expects SMTSymbolicAVCVal_Hint and FNode_Hint
            # _SMT_OMEGA_NODE is FNode_RT at runtime.
            # The type hints are for static analysis. Runtime objects are what's passed.
            constraints_for_sym = get_base_avc_constraints(sym_val_dict, _SMT_OMEGA_NODE, current_omega_py) # type: ignore[arg-type]
            final_setup.extend(constraints_for_sym)


    print(f"  Attempting to verify: '{property_name}' for Ω={current_omega_py} (Expect: {'Hold/Exist' if expect_property_to_hold else 'Fail/Not Exist'})")

    solve_result = None
    model_available = False
    try:
        # Solver_RT is the runtime alias for the actual PysmtSolver_Import or DummySolver
        with Solver_RT(name=solver_name, logic="QF_LIA") as s: # type: ignore 
            for f_setup in final_setup:
                if f_setup is not None: s.add_assertion(f_setup) # type: ignore
            
            formula_to_check = property_to_verify
            if not is_existential: 
                formula_to_check = Not(property_to_verify) # type: ignore
            
            if formula_to_check is not None: s.add_assertion(formula_to_check) # type: ignore
            else: 
                raise ValueError("Formula to check is None in SMT solver for a non-skipped SMT test.")

            solve_result = s.solve() # Removed options={'timeout': timeout_ms}

            if solve_result: # Model (witness or counterexample) exists
                model_available = True
                model = s.get_model()
                ce_parts = []
                for avc_sym_dict in symbolic_inputs_for_model:
                    if not avc_sym_dict: continue
                    # Ensure avc_sym_dict is the expected dictionary structure
                    if not isinstance(avc_sym_dict, dict): 
                        ce_parts.append(f"{avc_sym_dict}=?(NotADict)")
                        continue
                    name = avc_sym_dict.get("name_prefix_debug", "var")
                    try:
                        is_z = model.get_value(avc_sym_dict['is_zero']).is_true() # type: ignore
                        is_a = model.get_value(avc_sym_dict['is_areo']).is_true() # type: ignore
                        is_f = model.get_value(avc_sym_dict['is_finite']).is_true() # type: ignore
                        val = model.get_value(avc_sym_dict['val']).constant_value() # type: ignore
                        state_str = "Unio('zero')" if is_z else ("Unio('areo')" if is_a else (str(val) if is_f else "UnknownState"))
                        ce_parts.append(f"{name}={state_str}")
                    except Exception as e_model:
                        ce_parts.append(f"{name}=?(err_model_val:{e_model})")
                model_str = "; ".join(ce_parts)

            if is_existential:
                property_holds_observed = True if solve_result else False # Property (existence) holds if SAT
            else: # Universal property
                property_holds_observed = True if not solve_result else False # Property holds if Not(Property) is UNSAT
                         
    except Exception as e_smt:
        print(f"    SMT SOLVER ERROR for '{property_name}' Ω={current_omega_py}: {e_smt}")
        property_holds_observed = False 
        model_str = f"SMT Solver Exception: {e_smt}"
        model_available = True # Error details are available


    success_for_summary = (property_holds_observed == expect_property_to_hold)
    status_emoji = "✅" if success_for_summary else "❌"
    final_message_parts = [status_emoji]
    
    # Construct detailed message
    if is_existential:
        if property_holds_observed: 
            final_message_parts.append("Witness FOUND.")
            final_message_parts.append("As expected." if expect_property_to_hold else "UNEXPECTEDLY!")
        else: 
            final_message_parts.append("No witness found.")
            final_message_parts.append("As expected (non-existence confirmed)." if not expect_property_to_hold else "UNEXPECTEDLY (existence claim FAILED).")
    else: # Universal
        if property_holds_observed: 
            final_message_parts.append("Property HOLDS universally.")
            final_message_parts.append("As expected." if expect_property_to_hold else "UNEXPECTEDLY!")
        else: 
            final_message_parts.append("Property FAILED universally.")
            final_message_parts.append("As expected (non-universality confirmed)." if not expect_property_to_hold else "UNEXPECTEDLY (counterexample found).")

    if success_for_summary:
        smt_test_results_summary[current_omega_py]["passed"] += 1
    else:
        smt_test_results_summary[current_omega_py]["failed"] += 1
        smt_test_failures_details.append({
            "property": property_name, "omega": current_omega_py,
            "expected_to_hold": expect_property_to_hold,
            "observed_holds": property_holds_observed,
            "message": " ".join(final_message_parts), # Storing the generated message
            "model_str": model_str, # Storing the model string
            "is_existential": is_existential,
            "model_available": model_available
        })
    
    print(f"    {' '.join(final_message_parts)}")
    
    # Always print model_str if it's available and not just "N/A" or an error message we already showed
    if model_available and model_str != "N/A" and not isinstance(model_str, Exception):
        label = "Model (Witness/Counterexample)"
        if is_existential:
            if property_holds_observed: label = "Witness"
            else: label = "Details (No Witness)" # Should be "No witness found or timeout" etc.
        else: # Universal
            if not property_holds_observed: label = "Counterexample"
            else: label = "Details (No Counterexample)" # Should not happen if property_holds_observed is True
        
        # More refined labeling based on success
        if success_for_summary:
            if is_existential and property_holds_observed: label = "Witness (as expected)"
            elif not is_existential and not property_holds_observed: label = "Counterexample (as expected)"
            # else: no specific model detail needed if passed as expected without a model (e.g. universal hold)
        else: # Failed against expectation
            if is_existential and property_holds_observed: label = "Unexpected Witness"
            elif not is_existential and not property_holds_observed: label = "Counterexample (for unexpected failure)"
            elif is_existential and not property_holds_observed: label = "Details (Expected Witness Not Found)"
            elif not is_existential and property_holds_observed: label = "Details (Expected Counterexample Not Found)"


        # Only print if model_str has substantial info
        if not ( (is_existential and not property_holds_observed and "No witness found" in model_str) or \
                 (not is_existential and property_holds_observed) ): # Avoid printing "N/A" or "No witness found" if it's the only info
            print(f"      {label}: {model_str}")

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
# --- Part 5: SMT Property Test Definitions ---

def smt_test_commutativity_add(current_omega_py: int):
    property_name = f"SMT Commutativity of Addition (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True) # Mark as skipped via native report for now
        return

    omega_smt_node = Int(current_omega_py)
    a = create_symbolic_avc_val("a_comm_add")
    b = create_symbolic_avc_val("b_comm_add")
    res1 = create_symbolic_avc_val("res1_comm_add")
    res2 = create_symbolic_avc_val("res2_comm_add")

    if not all([a,b,res1,res2, omega_smt_node]): return # SMT not fully initialized

    setup_formulas = [
        avc_add_smt_logic(a, b, res1, omega_smt_node), # type: ignore
        avc_add_smt_logic(b, a, res2, omega_smt_node)  # type: ignore
    ]
    # Base constraints for res1 and res2 are added by prove_or_find_counterexample_smt
    # when they are included in symbolic_inputs_for_model if we want their values,
    # or they must be constrained if not. Here, their structure is defined by avc_add_smt_logic
    # and then compared. We need their base constraints asserted.
    setup_formulas.extend(get_base_avc_constraints(res1, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res2, omega_smt_node, current_omega_py)) # type: ignore


    property_to_verify = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a,b,res1,res2], expect_property_to_hold=True)

def smt_test_associativity_add(current_omega_py: int):
    property_name = f"SMT Associativity of Addition (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True)
        return
        
    expected_to_hold = (current_omega_py <= 2)
    omega_smt_node = Int(current_omega_py)
    a = create_symbolic_avc_val("a_assoc_add")
    b = create_symbolic_avc_val("b_assoc_add")
    c = create_symbolic_avc_val("c_assoc_add")
    ab = create_symbolic_avc_val("ab_assoc_add") # a+b
    lhs = create_symbolic_avc_val("lhs_assoc_add") # (a+b)+c
    bc = create_symbolic_avc_val("bc_assoc_add") # b+c
    rhs = create_symbolic_avc_val("rhs_assoc_add") # a+(b+c)

    if not all ([a,b,c,ab,lhs,bc,rhs,omega_smt_node]): return

    setup_formulas = [
        avc_add_smt_logic(a, b, ab, omega_smt_node), # type: ignore
        avc_add_smt_logic(ab, c, lhs, omega_smt_node), # type: ignore
        avc_add_smt_logic(b, c, bc, omega_smt_node), # type: ignore
        avc_add_smt_logic(a, bc, rhs, omega_smt_node) # type: ignore
    ]
    # Add base constraints for intermediate results
    setup_formulas.extend(get_base_avc_constraints(ab, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(lhs, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(bc, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(rhs, omega_smt_node, current_omega_py)) # type: ignore
    
    property_to_verify = avc_equiv_smt(lhs, rhs)
    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a,b,c,ab,lhs,bc,rhs], expect_property_to_hold=expected_to_hold)

def smt_test_additive_identity(current_omega_py: int):
    property_name = f"SMT Additive Identity (Unio for ⊕_v1.1)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None or AS_const_sym is None: # Check if constants are initialized
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE or Unio consts not init)", current_omega_py, True)
        return

    omega_smt_node = Int(current_omega_py)
    x = create_symbolic_avc_val("x_add_id")
    res_zu_x = create_symbolic_avc_val("res_zu_x_add_id")
    res_x_zu = create_symbolic_avc_val("res_x_zu_add_id")
    res_as_x = create_symbolic_avc_val("res_as_x_add_id")
    res_x_as = create_symbolic_avc_val("res_x_as_add_id")

    if not all([x, res_zu_x, res_x_zu, res_as_x, res_x_as, omega_smt_node]): return

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    setup_formulas.extend([
        avc_add_smt_logic(ZU_const_sym, x, res_zu_x, omega_smt_node), # type: ignore
        avc_add_smt_logic(x, ZU_const_sym, res_x_zu, omega_smt_node), # type: ignore
        avc_add_smt_logic(AS_const_sym, x, res_as_x, omega_smt_node), # type: ignore
        avc_add_smt_logic(x, AS_const_sym, res_x_as, omega_smt_node)  # type: ignore
    ])
    setup_formulas.extend(get_base_avc_constraints(res_zu_x, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_x_zu, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_as_x, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_x_as, omega_smt_node, current_omega_py)) # type: ignore

    # Property: ZU_const an identity AND AS_const is an identity (algebraically)
    # And since ZU_const ~ AS_const, this means Unio is the identity
    prop_zu_is_id = And(avc_equiv_smt(res_zu_x, x), avc_equiv_smt(res_x_zu, x)) # type: ignore
    prop_as_is_id = And(avc_equiv_smt(res_as_x, x), avc_equiv_smt(res_x_as, x)) # type: ignore
    property_to_verify = And(prop_zu_is_id, prop_as_is_id) # type: ignore
    
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [x, ZU_const_sym, AS_const_sym, res_zu_x, res_x_zu, res_as_x, res_x_as], 
                                     expect_property_to_hold=True)
def smt_test_commutativity_mul(current_omega_py: int):
    property_name = f"SMT Commutativity of Multiplication (⊗_v1.2)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True)
        return

    omega_smt_node = Int(current_omega_py)
    a = create_symbolic_avc_val("a_comm_mul")
    b = create_symbolic_avc_val("b_comm_mul")
    res1 = create_symbolic_avc_val("res1_comm_mul")
    res2 = create_symbolic_avc_val("res2_comm_mul")

    if not all([a,b,res1,res2, omega_smt_node]): return 

    setup_formulas = [
        avc_mul_smt_logic(a, b, res1, omega_smt_node), # type: ignore
        avc_mul_smt_logic(b, a, res2, omega_smt_node)  # type: ignore
    ]
    setup_formulas.extend(get_base_avc_constraints(res1, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res2, omega_smt_node, current_omega_py)) # type: ignore
    
    property_to_verify = avc_equiv_smt(res1, res2)
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a,b,res1,res2], expect_property_to_hold=True) # Multiplication is always commutative

def smt_test_associativity_mul(current_omega_py: int):
    property_name = f"SMT Associativity of Multiplication (⊗_v1.2)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True)
        return
        
    expected_to_hold = True # Multiplication is always associative in AVCA-Ω v1.2b
    omega_smt_node = Int(current_omega_py)
    a = create_symbolic_avc_val("a_assoc_mul")
    b = create_symbolic_avc_val("b_assoc_mul")
    c = create_symbolic_avc_val("c_assoc_mul")
    ab = create_symbolic_avc_val("ab_assoc_mul") # a*b
    lhs = create_symbolic_avc_val("lhs_assoc_mul") # (a*b)*c
    bc = create_symbolic_avc_val("bc_assoc_mul") # b*c
    rhs = create_symbolic_avc_val("rhs_assoc_mul") # a*(b*c)

    if not all ([a,b,c,ab,lhs,bc,rhs,omega_smt_node]): return

    setup_formulas = [
        avc_mul_smt_logic(a, b, ab, omega_smt_node), # type: ignore
        avc_mul_smt_logic(ab, c, lhs, omega_smt_node), # type: ignore
        avc_mul_smt_logic(b, c, bc, omega_smt_node), # type: ignore
        avc_mul_smt_logic(a, bc, rhs, omega_smt_node)  # type: ignore
    ]
    setup_formulas.extend(get_base_avc_constraints(ab, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(lhs, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(bc, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(rhs, omega_smt_node, current_omega_py)) # type: ignore

    property_to_verify = avc_equiv_smt(lhs, rhs)
    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a,b,c,ab,lhs,bc,rhs], expect_property_to_hold=expected_to_hold)

def smt_test_distributivity_mul_over_add(current_omega_py: int):
    # Left Distributivity: a ⊗ (b ⊕ c) == (a ⊗ b) ⊕ (a ⊗ c)
    property_name = f"SMT Left Distributivity (⊗_v1.2 over ⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True)
        return

    expected_to_hold = (current_omega_py <= 2)
    omega_smt_node = Int(current_omega_py)
    a = create_symbolic_avc_val("a_dist")
    b = create_symbolic_avc_val("b_dist")
    c = create_symbolic_avc_val("c_dist")

    # LHS: a ⊗ (b ⊕ c)
    b_plus_c = create_symbolic_avc_val("bpc_dist")
    lhs = create_symbolic_avc_val("lhs_dist")
    
    # RHS: (a ⊗ b) ⊕ (a ⊗ c)
    a_mul_b = create_symbolic_avc_val("amb_dist")
    a_mul_c = create_symbolic_avc_val("amc_dist")
    rhs = create_symbolic_avc_val("rhs_dist")

    if not all([a,b,c,b_plus_c,lhs,a_mul_b,a_mul_c,rhs,omega_smt_node]): return

    setup_formulas = [
        # LHS
        avc_add_smt_logic(b, c, b_plus_c, omega_smt_node), # type: ignore
        avc_mul_smt_logic(a, b_plus_c, lhs, omega_smt_node), # type: ignore
        # RHS
        avc_mul_smt_logic(a, b, a_mul_b, omega_smt_node), # type: ignore
        avc_mul_smt_logic(a, c, a_mul_c, omega_smt_node), # type: ignore
        avc_add_smt_logic(a_mul_b, a_mul_c, rhs, omega_smt_node) # type: ignore
    ]
    # Add base constraints for all intermediate results
    intermediate_results = [b_plus_c, lhs, a_mul_b, a_mul_c, rhs]
    for res_sym in intermediate_results:
        setup_formulas.extend(get_base_avc_constraints(res_sym, omega_smt_node, current_omega_py)) # type: ignore
        
    property_to_verify = avc_equiv_smt(lhs, rhs)
    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a,b,c,b_plus_c,lhs,a_mul_b,a_mul_c,rhs], 
                                     expect_property_to_hold=expected_to_hold)

def smt_test_additive_inverses_existence(current_omega_py: int):
    # ForAll a Exists x such that a + x = U (where U is ZU_const_sym)
    property_name = f"SMT Additive Inverse Existence (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE or ZU_const_sym not init)", current_omega_py, True)
        return

    omega_smt_node = Int(current_omega_py)
    a_inv = create_symbolic_avc_val("a_inv_exist")
    x_inv = create_symbolic_avc_val("x_inv_exist") # The inverse we are looking for
    res_ax_inv = create_symbolic_avc_val("res_ax_inv_exist")

    if not all([a_inv, x_inv, res_ax_inv, omega_smt_node]): return

    # Setup defines ZU_const_sym and the operation a+x=res
    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    setup_formulas.append(avc_add_smt_logic(a_inv, x_inv, res_ax_inv, omega_smt_node)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_ax_inv, omega_smt_node, current_omega_py)) # type: ignore
    
    # Property: res_ax_inv is equivalent to ZU_const_sym (algebraic Unio)
    property_is_inverse = avc_equiv_smt(res_ax_inv, ZU_const_sym) # type: ignore
    
    # We are testing ForAll a, Exists x.
    # prove_or_find_counterexample_smt handles ForAll a implicitly by leaving 'a' unconstrained
    # (beyond base constraints). We assert the existence part.
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, 
                                     property_is_inverse, # type: ignore
                                     [a_inv, x_inv, ZU_const_sym, res_ax_inv], # x_inv will be the witness
                                     expect_property_to_hold=True, 
                                     is_existential=True)
def smt_test_additive_inverses_uniqueness_pattern(current_omega_py: int):
    property_name_base = f"SMT Additive Inverse Uniqueness Pattern (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None: # type: ignore
        _report_native_test_result(property_name_base + " SKIPPED (SMT UNAVAILABLE or ZU_const_sym not init)", current_omega_py, True)
        return

    omega_smt_node = Int(current_omega_py) # type: ignore

    # Test 1: Unio's inverse is unique and is Unio.
    # This is already strongly implied by smt_test_additive_identity and existence.
    # For example, if U + x = U, then x must be U. If U + y = U and y != U, then y must be DFI.
    # But U + DFI = DFI (not U). So only x=U works.

    # Test 2: For DFI Fp(1) (if it exists, i.e. Ω>=2), its DFI inverse is unique.
    if current_omega_py >= 2:
        property_name_fp1 = property_name_base + " for DFI Fp(1) (uniqueness)"
        fp1_val = 1
        a_fp1 = create_symbolic_avc_val("a_fp1_inv_uniq")
        x_inv = create_symbolic_avc_val("x_fp1_inv_uniq") # One potential DFI inverse
        y_inv = create_symbolic_avc_val("y_fp1_inv_uniq_other") # Another potential DFI inverse
        res_ax = create_symbolic_avc_val("res_ax_fp1_inv_uniq")
        res_ay = create_symbolic_avc_val("res_ay_fp1_inv_uniq_other")

        if not all([a_fp1, x_inv, y_inv, res_ax, res_ay, ZU_const_sym, omega_smt_node]): return

        # Setup:
        # a_fp1 is Fp(1)
        # x_inv is a DFI inverse of a_fp1
        # y_inv is a DFI inverse of a_fp1
        setup_fp1_unique_check = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
        setup_fp1_unique_check.extend([
            Iff(a_fp1["is_finite"], TRUE()),  # a_fp1 is DFI # Changed to Iff
            Equals(a_fp1["val"], Int(fp1_val)), # type: ignore # a_fp1 is value 1
            
            Iff(x_inv["is_finite"], TRUE()),  # x_inv is DFI # Changed to Iff
            avc_add_smt_logic(a_fp1, x_inv, res_ax, omega_smt_node), # type: ignore
            avc_equiv_smt(res_ax, ZU_const_sym), # type: ignore # a_fp1 + x_inv = Unio

            Iff(y_inv["is_finite"], TRUE()),  # y_inv is DFI # Changed to Iff
            avc_add_smt_logic(a_fp1, y_inv, res_ay, omega_smt_node), # type: ignore
            avc_equiv_smt(res_ay, ZU_const_sym)  # type: ignore # a_fp1 + y_inv = Unio
        ])
        setup_fp1_unique_check.extend(get_base_avc_constraints(res_ax, omega_smt_node, current_omega_py)) # type: ignore
        setup_fp1_unique_check.extend(get_base_avc_constraints(res_ay, omega_smt_node, current_omega_py)) # type: ignore
        
        # Property: If x_inv and y_inv are both DFI inverses of a_fp1, then they must be the same.
        property_to_verify = Equals(x_inv["val"], y_inv["val"]) # type: ignore 
        
        # Fp(1) always has a unique DFI inverse (Fp(Omega-1)) if Omega >=2. So, expect this to hold.
        prove_or_find_counterexample_smt(property_name_fp1, current_omega_py, setup_fp1_unique_check, 
                                         property_to_verify, # type: ignore
                                         [a_fp1, x_inv, y_inv, res_ax, res_ay, ZU_const_sym], # type: ignore
                                         expect_property_to_hold=True)

    # Test 3: For DFI Fp(2) (if it exists, i.e. Ω>=3), are there AT LEAST TWO DISTINCT DFI inverses?
    if current_omega_py >= 3:
        property_name_fp2 = property_name_base + " for DFI Fp(2) (has >=2 distinct DFI inverses)"
        fp2_val = 2
        a_fp2 = create_symbolic_avc_val("a_fp2_inv_multi")
        x1_inv = create_symbolic_avc_val("x1_fp2_inv_multi")
        x2_inv = create_symbolic_avc_val("x2_fp2_inv_multi")
        res_ax1 = create_symbolic_avc_val("res_ax1_fp2_inv_multi")
        res_ax2 = create_symbolic_avc_val("res_ax2_fp2_inv_multi")

        if not all([a_fp2, x1_inv, x2_inv, res_ax1, res_ax2, ZU_const_sym, omega_smt_node]): return

        # Setup:
        # a_fp2 is Fp(2)
        # x1_inv is a DFI inverse of a_fp2
        # x2_inv is a DFI inverse of a_fp2
        setup_fp2 = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
        setup_fp2.extend([
            Iff(a_fp2["is_finite"], TRUE()),  # a_fp2 is DFI # Changed to Iff
            Equals(a_fp2["val"], Int(fp2_val)), # type: ignore # a_fp2 is value 2
            
            Iff(x1_inv["is_finite"], TRUE()), # x1_inv is DFI # Changed to Iff
            avc_add_smt_logic(a_fp2, x1_inv, res_ax1, omega_smt_node), # type: ignore
            avc_equiv_smt(res_ax1, ZU_const_sym), # type: ignore # a_fp2 + x1_inv = Unio

            Iff(x2_inv["is_finite"], TRUE()), # x2_inv is DFI # Changed to Iff
            avc_add_smt_logic(a_fp2, x2_inv, res_ax2, omega_smt_node), # type: ignore
            avc_equiv_smt(res_ax2, ZU_const_sym)  # type: ignore # a_fp2 + x2_inv = Unio
        ])
        setup_fp2.extend(get_base_avc_constraints(res_ax1, omega_smt_node, current_omega_py)) # type: ignore
        setup_fp2.extend(get_base_avc_constraints(res_ax2, omega_smt_node, current_omega_py)) # type: ignore

        # Property: x1_inv and x2_inv are distinct (their DFI values differ).
        prop_fp2_multiple_distinct_dfi_inv = Not(Equals(x1_inv["val"], x2_inv["val"])) # type: ignore
        
        # Fp(2) has 2 DFI inverses if Omega>=3 (specifically Fp(Omega-2) and Fp(Omega-1)).
        # So, we expect to FIND such distinct x1, x2.
        prove_or_find_counterexample_smt(property_name_fp2, current_omega_py, setup_fp2, 
                                         prop_fp2_multiple_distinct_dfi_inv, # type: ignore
                                         [a_fp2, x1_inv, x2_inv, res_ax1, res_ax2, ZU_const_sym], # type: ignore
                                         expect_property_to_hold=True, # Expect to find such distinct inverses
                                         is_existential=True)
def smt_test_zero_divisors_mul(current_omega_py: int):
    property_name = f"SMT Existence of Non-Unio Zero Divisors (⊗_v1.2)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None or AS_const_sym is None: # type: ignore
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE or Unio consts not init)", current_omega_py, True)
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_zero_div")
    b = create_symbolic_avc_val("b_zero_div")
    res_ab = create_symbolic_avc_val("res_ab_zero_div")

    if not all([a,b,res_ab, ZU_const_sym, AS_const_sym, omega_smt_node]): return # SMT init check

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    setup_formulas.extend([
        # a and b must be DFI
        Iff(a["is_finite"], TRUE()), # a is DFI
        Iff(b["is_finite"], TRUE()), # b is DFI
        avc_mul_smt_logic(a,b,res_ab, omega_smt_node) # type: ignore
    ])
    # Ensure res_ab itself is constrained to be a valid AVCA value
    setup_formulas.extend(get_base_avc_constraints(res_ab, omega_smt_node, current_omega_py)) # type: ignore
    
    # Property: a*b is algebraically equivalent to Unio.
    # We can use ZU_const_sym as the representative for algebraic Unio.
    # The avc_mul_smt_logic for DFI*DFI overflow should yield a state
    # that is algebraically equivalent to AS_const_sym (and thus ZU_const_sym).
    property_to_verify = avc_equiv_smt(res_ab, ZU_const_sym) # type: ignore
    
    expected_to_hold = (current_omega_py >= 3) # Zero divisors exist (result is Unio) iff Omega >= 3

    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Exist' if expected_to_hold else 'Not Exist'})", 
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a,b,res_ab, ZU_const_sym, AS_const_sym], # type: ignore # Added AS_const_sym for model if needed
                                     expect_property_to_hold=expected_to_hold, 
                                     is_existential=True)


def smt_test_additive_cancellation(current_omega_py: int):
    property_name = f"SMT Additive Cancellation (a⊕c == b⊕c ⇒ a == b)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True)
        return

    expected_to_hold = (current_omega_py <= 2)
    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_add_cancel")
    b = create_symbolic_avc_val("b_add_cancel")
    c = create_symbolic_avc_val("c_add_cancel")
    ac_res = create_symbolic_avc_val("ac_res_add_cancel")
    bc_res = create_symbolic_avc_val("bc_res_add_cancel")

    if not all([a,b,c,ac_res,bc_res, omega_smt_node]): return

    setup_formulas = [
        avc_add_smt_logic(a,c,ac_res,omega_smt_node), # type: ignore
        avc_add_smt_logic(b,c,bc_res,omega_smt_node)  # type: ignore
    ]
    setup_formulas.extend(get_base_avc_constraints(ac_res, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(bc_res, omega_smt_node, current_omega_py)) # type: ignore

    premise = avc_equiv_smt(ac_res, bc_res) # type: ignore
    conclusion = avc_equiv_smt(a,b) # type: ignore
    property_to_verify = Implies(premise, conclusion) # type: ignore

    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})",
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a,b,c,ac_res,bc_res],
                                     expect_property_to_hold=expected_to_hold)

def smt_test_multiplicative_cancellation(current_omega_py: int):
    property_name = f"SMT Multiplicative Cancellation (a⊗c == b⊗c ∧ c≠U ⇒ a == b)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None: # type: ignore
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE or ZU_const_sym not init)", current_omega_py, True)
        return

    expected_to_hold = (current_omega_py <= 2)
    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_mul_cancel")
    b = create_symbolic_avc_val("b_mul_cancel")
    c = create_symbolic_avc_val("c_mul_cancel")
    ac_res = create_symbolic_avc_val("ac_res_mul_cancel")
    bc_res = create_symbolic_avc_val("bc_res_mul_cancel")

    if not all([a,b,c,ac_res,bc_res, ZU_const_sym, omega_smt_node]): return

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    setup_formulas.extend([
        avc_mul_smt_logic(a,c,ac_res,omega_smt_node), # type: ignore
        avc_mul_smt_logic(b,c,bc_res,omega_smt_node)  # type: ignore
    ])
    setup_formulas.extend(get_base_avc_constraints(ac_res, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(bc_res, omega_smt_node, current_omega_py)) # type: ignore

    # c is not Unio (algebraically) means c is DFI
    c_is_not_unio = Iff(c["is_finite"], TRUE()) # type: ignore # Changed Equals to Iff
    
    premise = And(avc_equiv_smt(ac_res, bc_res), c_is_not_unio) # type: ignore
    conclusion = avc_equiv_smt(a,b) # type: ignore
    property_to_verify = Implies(premise, conclusion) # type: ignore

    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})",
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a,b,c,ac_res,bc_res,ZU_const_sym], # type: ignore
                                     expect_property_to_hold=expected_to_hold)
# TODO later: SMT test for uniqueness pattern of additive inverses (more complex SMT logic)
# We will add more SMT tests for Mul Comm/Assoc and Distributivity later.
# And SMT for Additive Inverses.

def smt_test_subtraction_right_identity(current_omega_py: int):
    property_name = f"SMT Subtraction Right Identity (X ⊖ U == X)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None or AS_const_sym is None: # type: ignore
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE or Unio consts not init)", current_omega_py, True)
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    x = create_symbolic_avc_val("x_sub_id")
    # Test with both ZU and AS as the identity U being subtracted
    res_x_zu = create_symbolic_avc_val("res_x_zu_sub_id")
    res_x_as = create_symbolic_avc_val("res_x_as_sub_id")

    if not all([x, res_x_zu, res_x_as, ZU_const_sym, AS_const_sym, omega_smt_node]): return

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    setup_formulas.extend([
        avc_sub_smt_logic(x, ZU_const_sym, res_x_zu, omega_smt_node), # type: ignore
        avc_sub_smt_logic(x, AS_const_sym, res_x_as, omega_smt_node)  # type: ignore
    ])
    setup_formulas.extend(get_base_avc_constraints(res_x_zu, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_x_as, omega_smt_node, current_omega_py)) # type: ignore

    prop_zu_is_right_id = avc_equiv_smt(res_x_zu, x) # type: ignore
    prop_as_is_right_id = avc_equiv_smt(res_x_as, x) # type: ignore
    property_to_verify = And(prop_zu_is_right_id, prop_as_is_right_id) # type: ignore
    
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [x, ZU_const_sym, AS_const_sym, res_x_zu, res_x_as], 
                                     expect_property_to_hold=True)

def smt_test_subtraction_stuck_at_areo(current_omega_py: int):
    property_name = f"SMT Subtraction 'Stuck-at-Areo' (U ⊖ DFI_k == AREO_UNIO)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None or AS_const_sym is None: # type: ignore
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE or Unio consts not init)", current_omega_py, True)
        return
    
    if current_omega_py <= 1: # DFI is empty, property is vacuous or not well-defined
        _report_native_test_result(property_name + f" SKIPPED (Ω={current_omega_py}, DFI empty)", current_omega_py, True, "VACUOUS")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    dfi_k = create_symbolic_avc_val("dfi_k_sub_stuck")
    res_zu_dfik = create_symbolic_avc_val("res_zu_dfik_sub_stuck")
    res_as_dfik = create_symbolic_avc_val("res_as_dfik_sub_stuck")

    if not all([dfi_k, res_zu_dfik, res_as_dfik, ZU_const_sym, AS_const_sym, omega_smt_node]): return

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    setup_formulas.extend([
        Iff(dfi_k["is_finite"], TRUE()), # dfi_k is DFI # type: ignore
        avc_sub_smt_logic(ZU_const_sym, dfi_k, res_zu_dfik, omega_smt_node), # type: ignore
        avc_sub_smt_logic(AS_const_sym, dfi_k, res_as_dfik, omega_smt_node)  # type: ignore
    ])
    setup_formulas.extend(get_base_avc_constraints(res_zu_dfik, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_as_dfik, omega_smt_node, current_omega_py)) # type: ignore

    # Property: ZU-DFIk and AS-DFIk both result in AREO_UNIO (algebraically AS_const_sym)
    prop_zu_minus_dfi_is_as = avc_equiv_smt(res_zu_dfik, AS_const_sym) # type: ignore
    prop_as_minus_dfi_is_as = avc_equiv_smt(res_as_dfik, AS_const_sym) # type: ignore
    property_to_verify = And(prop_zu_minus_dfi_is_as, prop_as_minus_dfi_is_as) # type: ignore
    
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [dfi_k, ZU_const_sym, AS_const_sym, res_zu_dfik, res_as_dfik], 
                                     expect_property_to_hold=True) # Holds for Ω > 1

def smt_test_subtraction_non_commutativity(current_omega_py: int):
    property_name = f"SMT Subtraction Non-Commutativity (a⊖b == b⊖a)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True)
        return

    # Commutativity for subtraction holds iff Ω=1 (trivially, U-U = U-U)
    # So, for Ω >= 2, we expect commutativity to FAIL (i.e., non-commutativity holds)
    expect_commutativity_to_hold = (current_omega_py == 1)
    
    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_sub_noncomm")
    b = create_symbolic_avc_val("b_sub_noncomm")
    res1 = create_symbolic_avc_val("res1_sub_noncomm") # a-b
    res2 = create_symbolic_avc_val("res2_sub_noncomm") # b-a

    if not all([a,b,res1,res2, omega_smt_node]): return

    setup_formulas = [
        avc_sub_smt_logic(a,b,res1,omega_smt_node), # type: ignore
        avc_sub_smt_logic(b,a,res2,omega_smt_node)  # type: ignore
    ]
    setup_formulas.extend(get_base_avc_constraints(res1, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res2, omega_smt_node, current_omega_py)) # type: ignore

    property_is_commutative = avc_equiv_smt(res1, res2) # type: ignore
    
    prove_or_find_counterexample_smt(property_name + f" (Testing FOR Commutativity, Expect: {'Holds' if expect_commutativity_to_hold else 'Fails'})",
                                     current_omega_py, setup_formulas, property_is_commutative, # type: ignore
                                     [a,b,res1,res2], 
                                     expect_property_to_hold=expect_commutativity_to_hold)

def smt_test_subtraction_non_associativity(current_omega_py: int):
    property_name = f"SMT Subtraction Non-Associativity ((a⊖b)⊖c == a⊖(b⊖c))"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True)
        return

    # Associativity for subtraction holds iff Ω=1 (trivially)
    # So, for Ω >= 2, we expect associativity to FAIL
    expect_associativity_to_hold = (current_omega_py == 1)

    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_sub_nonassoc")
    b = create_symbolic_avc_val("b_sub_nonassoc")
    c = create_symbolic_avc_val("c_sub_nonassoc")
    ab = create_symbolic_avc_val("ab_sub_nonassoc") # a-b
    lhs = create_symbolic_avc_val("lhs_sub_nonassoc") # (a-b)-c
    bc = create_symbolic_avc_val("bc_sub_nonassoc") # b-c
    rhs = create_symbolic_avc_val("rhs_sub_nonassoc") # a-(b-c)

    if not all([a,b,c,ab,lhs,bc,rhs,omega_smt_node]): return

    setup_formulas = [
        avc_sub_smt_logic(a,b,ab,omega_smt_node), # type: ignore
        avc_sub_smt_logic(ab,c,lhs,omega_smt_node), # type: ignore
        avc_sub_smt_logic(b,c,bc,omega_smt_node), # type: ignore
        avc_sub_smt_logic(a,bc,rhs,omega_smt_node)  # type: ignore
    ]
    intermediate_results = [ab,lhs,bc,rhs]
    for res_sym in intermediate_results:
        setup_formulas.extend(get_base_avc_constraints(res_sym, omega_smt_node, current_omega_py)) # type: ignore
        
    property_is_associative = avc_equiv_smt(lhs,rhs) # type: ignore

    prove_or_find_counterexample_smt(property_name + f" (Testing FOR Associativity, Expect: {'Holds' if expect_associativity_to_hold else 'Fails'})",
                                     current_omega_py, setup_formulas, property_is_associative, # type: ignore
                                     [a,b,c,ab,lhs,bc,rhs],
                                     expect_property_to_hold=expect_associativity_to_hold)

def smt_test_dfi_additive_inverse_count_specific_case(current_omega_py: int):
    property_name = f"SMT Additive Inverse Count for DFI Fp(2) (Ω=3)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None: # type: ignore
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return

    if current_omega_py != 3: # This specific test is for Omega=3
        _report_native_test_result(property_name + f" SKIPPED (Test specific to Ω=3, current is {current_omega_py})", current_omega_py, True, "OMEGA_MISMATCH")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    
    a_sym = create_symbolic_avc_val("a_inv_count")      # Element to find inverses for (Fp(2))
    x1_sym = create_symbolic_avc_val("x1_inv_count")    # First DFI inverse
    x2_sym = create_symbolic_avc_val("x2_inv_count")    # Second DFI inverse
    y_sym = create_symbolic_avc_val("y_inv_count")      # Arbitrary DFI element to test uniqueness

    res_ax1 = create_symbolic_avc_val("res_ax1_count")
    res_ax2 = create_symbolic_avc_val("res_ax2_count")
    res_ay = create_symbolic_avc_val("res_ay_count")

    if not all([a_sym, x1_sym, x2_sym, y_sym, res_ax1, res_ax2, res_ay, ZU_const_sym, omega_smt_node]): return

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    # Constrain 'a' to be Fp(2) for Omega=3
    setup_formulas.extend([
        Iff(a_sym["is_finite"], TRUE()), # type: ignore
        Equals(a_sym["val"], Int(2)), # type: ignore
    ])

    # 1. Assert x1 is a DFI inverse of a_sym
    setup_formulas.extend(get_base_avc_constraints(x1_sym, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_ax1, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend([
        Iff(x1_sym["is_finite"], TRUE()), # type: ignore
        avc_add_smt_logic(a_sym, x1_sym, res_ax1, omega_smt_node), # type: ignore
        avc_equiv_smt(res_ax1, ZU_const_sym) # type: ignore
    ])

    # 2. Assert x2 is a DFI inverse of a_sym
    setup_formulas.extend(get_base_avc_constraints(x2_sym, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_ax2, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend([
        Iff(x2_sym["is_finite"], TRUE()), # type: ignore
        avc_add_smt_logic(a_sym, x2_sym, res_ax2, omega_smt_node), # type: ignore
        avc_equiv_smt(res_ax2, ZU_const_sym) # type: ignore
    ])
    
    # 3. Assert x1 and x2 are distinct DFI values
    setup_formulas.append(Not(Equals(x1_sym["val"], x2_sym["val"]))) # type: ignore

    # 4. Property: For any other DFI y_sym that is an inverse of a_sym, 
    #    y_sym must be equal to x1_sym or x2_sym.
    #    ForAll y: ( (y is DFI) AND (a+y = U) ) IMPLIES ( y.val = x1.val OR y.val = x2.val )
    setup_formulas_prop = list(setup_formulas) # Setup for the property which includes y_sym
    setup_formulas_prop.extend(get_base_avc_constraints(y_sym, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas_prop.extend(get_base_avc_constraints(res_ay, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas_prop.append(avc_add_smt_logic(a_sym, y_sym, res_ay, omega_smt_node)) # type: ignore

    premise_y_is_dfi_inverse = And(Iff(y_sym["is_finite"], TRUE()), avc_equiv_smt(res_ay, ZU_const_sym)) # type: ignore
    conclusion_y_is_x1_or_x2 = Or(Equals(y_sym["val"], x1_sym["val"]), Equals(y_sym["val"], x2_sym["val"])) # type: ignore
    property_to_verify = Implies(premise_y_is_dfi_inverse, conclusion_y_is_x1_or_x2) # type: ignore

    # This is a universal property about 'y', given that x1 and x2 satisfying the setup exist.
    # The overall test is existential for x1,x2 and then universal for y.
    # For SMT, we can ask: Does there exist x1, x2 (distinct DFI inverses) such that
    # for all other DFI y that are inverses, y is one of x1 or x2.
    # This is complex. Simpler: Find x1, x2. Then separately verify the "no other" part.
    # For now, let's assert existence of two distinct inverses (already in uniqueness_pattern for Fp(2))
    # and then separately test that only Fp(1) and Fp(2) are inverses for Fp(2) when Omega=3.
    
    # Test for exactly two (Fp(1) and Fp(2) for a=Fp(2), Omega=3)
    # We need x1 and x2 to be Fp(1) and Fp(2) in some order.
    # (x1=1 and x2=2) OR (x1=2 and x2=1)
    prop_specific_inverses = Or( # type: ignore
        And(Equals(x1_sym["val"], Int(1)), Equals(x2_sym["val"], Int(2))), # type: ignore
        And(Equals(x1_sym["val"], Int(2)), Equals(x2_sym["val"], Int(1)))  # type: ignore
    )
    final_setup_for_specific_inverses = setup_formulas + [prop_specific_inverses] # type: ignore
    
    # Check if this specific configuration (a=Fp(2) has inverses Fp(1) and Fp(2)) is possible
    prove_or_find_counterexample_smt(property_name + " (Fp(2) has inverses Fp(1),Fp(2))", 
                                     current_omega_py, final_setup_for_specific_inverses, # type: ignore
                                     TRUE(), # We are checking satisfiability of the setup
                                     [a_sym, x1_sym, x2_sym, ZU_const_sym], # type: ignore
                                     expect_property_to_hold=True, 
                                     is_existential=True) # Expect to find such x1, x2

def smt_test_fp1_multiplicative_identity_for_dfi(current_omega_py: int):
    property_name = f"SMT Fp(1) as Conditional Multiplicative Identity for DFI"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None: # type: ignore
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return
    
    if current_omega_py <= 1: # Fp(1) DFI element does not exist
        _report_native_test_result(property_name + f" SKIPPED (Ω={current_omega_py}, Fp(1) DFI N/A)", current_omega_py, True, "VACUOUS")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    fp1_sym = create_symbolic_avc_val("fp1_mul_id")
    k_sym = create_symbolic_avc_val("k_dfi_mul_id")
    res_ek = create_symbolic_avc_val("res_ek_mul_id") # fp1 * k
    res_ke = create_symbolic_avc_val("res_ke_mul_id") # k * fp1

    if not all([fp1_sym, k_sym, res_ek, res_ke, ZU_const_sym, omega_smt_node]): return

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    # Constrain fp1_sym to be Fp(1)
    setup_formulas.extend([
        Iff(fp1_sym["is_finite"], TRUE()), # type: ignore
        Equals(fp1_sym["val"], Int(1)), # type: ignore
    ])
    # k_sym is any DFI
    setup_formulas.append(Iff(k_sym["is_finite"], TRUE())) # type: ignore
    
    # Define operations
    setup_formulas.append(avc_mul_smt_logic(fp1_sym, k_sym, res_ek, omega_smt_node)) # type: ignore
    setup_formulas.append(avc_mul_smt_logic(k_sym, fp1_sym, res_ke, omega_smt_node)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_ek, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_ke, omega_smt_node, current_omega_py)) # type: ignore

    # Property: IF fp1*k (res_ek) is DFI AND k*fp1 (res_ke) is DFI, 
    # THEN res_ek == k AND res_ke == k
    premise = And(Iff(res_ek["is_finite"], TRUE()), Iff(res_ke["is_finite"], TRUE())) # type: ignore
    conclusion = And(avc_equiv_smt(res_ek, k_sym), avc_equiv_smt(res_ke, k_sym)) # type: ignore
    property_to_verify = Implies(premise, conclusion) # type: ignore

    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [fp1_sym, k_sym, res_ek, res_ke], 
                                     expect_property_to_hold=True)

def smt_test_fp1_not_universal_multiplicative_identity(current_omega_py: int):
    property_name = f"SMT Fp(1) Not Universal Multiplicative Identity (vs Unio)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None: # type: ignore
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return

    if current_omega_py <= 1: # Fp(1) DFI element does not exist
        _report_native_test_result(property_name + f" SKIPPED (Ω={current_omega_py}, Fp(1) DFI N/A)", current_omega_py, True, "VACUOUS")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    fp1_sym = create_symbolic_avc_val("fp1_not_univ_id")
    # We will test Fp(1) * ZU_const_sym
    res_fp1_zu = create_symbolic_avc_val("res_fp1_zu_not_univ_id")
    
    if not all([fp1_sym, res_fp1_zu, ZU_const_sym, AS_const_sym, omega_smt_node]): return

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    # Constrain fp1_sym to be Fp(1)
    setup_formulas.extend([
        Iff(fp1_sym["is_finite"], TRUE()), # type: ignore
        Equals(fp1_sym["val"], Int(1)), # type: ignore
    ])
    setup_formulas.append(avc_mul_smt_logic(fp1_sym, ZU_const_sym, res_fp1_zu, omega_smt_node)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(res_fp1_zu, omega_smt_node, current_omega_py)) # type: ignore

    # Property: Fp(1) * ZU_const_sym == ZU_const_sym (which is true)
    # AND ZU_const_sym is NOT Fp(1) (which is true if Omega > 1)
    # This means Fp(1) is not a universal identity because Fp(1)*ZU != Fp(1)
    
    # We test that Fp(1) * ZU is NOT Fp(1)
    property_to_verify = Not(avc_equiv_smt(res_fp1_zu, fp1_sym)) # type: ignore
    
    # This property (Fp(1)*ZU != Fp(1)) is expected to HOLD for Omega > 1
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [fp1_sym, ZU_const_sym, res_fp1_zu], 
                                     expect_property_to_hold=True)

def smt_test_subtraction_dfi_cases(current_omega_py: int):
    property_name_base = f"SMT Subtraction DFI Cases (⊖_v1.0)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None or AS_const_sym is None: # type: ignore
        _report_native_test_result(property_name_base + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return

    if current_omega_py < 2: # Need DFI elements
        _report_native_test_result(property_name_base + f" SKIPPED (Ω={current_omega_py} no DFI)", current_omega_py, True, "VACUOUS")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1 # Count as 1 suite
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    
    # Case 1: DFI - DFI -> DFI (e.g., For Ω=3, Fp(2) - Fp(1) = Fp(1))
    if current_omega_py >= 3: # Requires at least Fp(1), Fp(2)
        prop_name1 = property_name_base + " DFI-DFI -> DFI (e.g. Ω=3, 2-1=1)"
        a1 = create_symbolic_avc_val("a1_sub_dfi")
        b1 = create_symbolic_avc_val("b1_sub_dfi")
        res1 = create_symbolic_avc_val("res1_sub_dfi")
        expected_res1 = create_symbolic_avc_val("exp_res1_sub_dfi")
        if not all([a1,b1,res1,expected_res1,omega_smt_node]): return

        setup1 = [
            Iff(a1["is_finite"], TRUE()), Equals(a1["val"], Int(2)), # a1 = Fp(2) # type: ignore
            Iff(b1["is_finite"], TRUE()), Equals(b1["val"], Int(1)), # b1 = Fp(1) # type: ignore
            Iff(expected_res1["is_finite"], TRUE()), Equals(expected_res1["val"], Int(1)), # expected = Fp(1) # type: ignore
            avc_sub_smt_logic(a1,b1,res1,omega_smt_node) # type: ignore
        ]
        setup1.extend(get_base_avc_constraints(res1, omega_smt_node, current_omega_py)) # type: ignore
        prove_or_find_counterexample_smt(prop_name1, current_omega_py, setup1, 
                                         avc_equiv_smt(res1, expected_res1), # type: ignore
                                         [a1,b1,res1,expected_res1], expect_property_to_hold=True)

    # Case 2: DFI - DFI -> AREO_UNIO (underflow, e.g., For Ω=3, Fp(1) - Fp(2) = AU)
    if current_omega_py >= 3: # Requires at least Fp(1), Fp(2)
        prop_name2 = property_name_base + " DFI-DFI -> AREO_UNIO (e.g. Ω=3, 1-2=AU)"
        a2 = create_symbolic_avc_val("a2_sub_dfi_au")
        b2 = create_symbolic_avc_val("b2_sub_dfi_au")
        res2 = create_symbolic_avc_val("res2_sub_dfi_au")
        if not all([a2,b2,res2,AS_const_sym,omega_smt_node]): return

        setup2 = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
        setup2.extend([
            Iff(a2["is_finite"], TRUE()), Equals(a2["val"], Int(1)), # a2 = Fp(1) # type: ignore
            Iff(b2["is_finite"], TRUE()), Equals(b2["val"], Int(2)), # b2 = Fp(2) # type: ignore
            avc_sub_smt_logic(a2,b2,res2,omega_smt_node) # type: ignore
        ])
        setup2.extend(get_base_avc_constraints(res2, omega_smt_node, current_omega_py)) # type: ignore
        prove_or_find_counterexample_smt(prop_name2, current_omega_py, setup2,
                                         avc_equiv_smt(res2, AS_const_sym), # type: ignore
                                         [a2,b2,res2,AS_const_sym], expect_property_to_hold=True) # type: ignore

    # Case 3: DFI - DFI -> AREO_UNIO (cancellation, e.g., For Ω=2, Fp(1) - Fp(1) = AU)
    if current_omega_py >= 2: # Requires Fp(1)
        prop_name3 = property_name_base + " DFI-DFI -> AREO_UNIO (e.g. Ω=2, 1-1=AU)"
        a3 = create_symbolic_avc_val("a3_sub_dfi_au_cancel")
        b3 = create_symbolic_avc_val("b3_sub_dfi_au_cancel") # Should be same as a3
        res3 = create_symbolic_avc_val("res3_sub_dfi_au_cancel")
        if not all([a3,b3,res3,AS_const_sym,omega_smt_node]): return

        setup3 = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
        setup3.extend([
            Iff(a3["is_finite"], TRUE()), Equals(a3["val"], Int(1)), # a3 = Fp(1) # type: ignore
            Iff(b3["is_finite"], TRUE()), Equals(b3["val"], Int(1)), # b3 = Fp(1) # type: ignore
            avc_sub_smt_logic(a3,b3,res3,omega_smt_node) # type: ignore
        ])
        setup3.extend(get_base_avc_constraints(res3, omega_smt_node, current_omega_py)) # type: ignore
        prove_or_find_counterexample_smt(prop_name3, current_omega_py, setup3,
                                         avc_equiv_smt(res3, AS_const_sym), # type: ignore
                                         [a3,b3,res3,AS_const_sym], expect_property_to_hold=True) # type: ignore

def smt_test_division_unio_interactions(current_omega_py: int):
    property_name_base = f"SMT Division Unio Interactions (⊘_v1.2B)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None or AS_const_sym is None: # type: ignore
        _report_native_test_result(property_name_base + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    x = create_symbolic_avc_val("x_div_unio") # Generic x from S_Omega
    dfi_k_val = 1 # A representative DFI value, ensure it's valid for current_omega_py
    if current_omega_py == 1 and dfi_k_val >= current_omega_py: # Adjust if DFI doesn't exist
        pass # DFI related sub-tests will be skipped by Omega check
        
    # Sub-Test 1 (Rule B1): X ⊘ U == AREO_UNIO (algebraically AS_const_sym)
    prop_name1 = property_name_base + " X ⊘ Unio == AREO_UNIO"
    res_x_zu_div = create_symbolic_avc_val("res_x_zu_div_unio")
    res_x_as_div = create_symbolic_avc_val("res_x_as_div_unio")
    if not all([x, res_x_zu_div, res_x_as_div, ZU_const_sym, AS_const_sym, omega_smt_node]): return

    setup1 = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    setup1.extend([
        avc_div_smt_logic(x, ZU_const_sym, res_x_zu_div, omega_smt_node), # type: ignore
        avc_div_smt_logic(x, AS_const_sym, res_x_as_div, omega_smt_node)  # type: ignore
    ])
    setup1.extend(get_base_avc_constraints(res_x_zu_div, omega_smt_node, current_omega_py)) # type: ignore
    setup1.extend(get_base_avc_constraints(res_x_as_div, omega_smt_node, current_omega_py)) # type: ignore
    prop1 = And(avc_equiv_smt(res_x_zu_div, AS_const_sym), avc_equiv_smt(res_x_as_div, AS_const_sym)) # type: ignore
    prove_or_find_counterexample_smt(prop_name1, current_omega_py, setup1, prop1, # type: ignore
                                     [x, ZU_const_sym, AS_const_sym, res_x_zu_div, res_x_as_div], # type: ignore
                                     expect_property_to_hold=True)

    # Sub-Test 2 (Rule B2): ZERO_UNIO ⊘ DFI_k == ZERO_UNIO
    if current_omega_py > 1: # DFI_k exists
        prop_name2 = property_name_base + " ZU ⊘ DFI_k == ZU"
        dfi_k_sym_b2 = create_symbolic_avc_val("dfik_b2_div_unio")
        res_zu_dfik_div = create_symbolic_avc_val("res_zu_dfik_div_unio")
        if not all([dfi_k_sym_b2, res_zu_dfik_div, ZU_const_sym, omega_smt_node]): return

        setup2 = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
        setup2.extend([
            Iff(dfi_k_sym_b2["is_finite"], TRUE()), # dfi_k is DFI # type: ignore
            # Could constrain dfi_k_sym_b2["val"] to be dfi_k_val if needed, or leave generic DFI
            avc_div_smt_logic(ZU_const_sym, dfi_k_sym_b2, res_zu_dfik_div, omega_smt_node) # type: ignore
        ])
        setup2.extend(get_base_avc_constraints(res_zu_dfik_div, omega_smt_node, current_omega_py)) # type: ignore
        prop2 = avc_equiv_smt(res_zu_dfik_div, ZU_const_sym) # type: ignore
        prove_or_find_counterexample_smt(prop_name2, current_omega_py, setup2, prop2, # type: ignore
                                         [dfi_k_sym_b2, ZU_const_sym, res_zu_dfik_div], # type: ignore
                                         expect_property_to_hold=True)

    # Sub-Test 3 (Rule B2): AREO_UNIO ⊘ DFI_k == AREO_UNIO
    if current_omega_py > 1: # DFI_k exists
        prop_name3 = property_name_base + " AS ⊘ DFI_k == AS"
        dfi_k_sym_b3 = create_symbolic_avc_val("dfik_b3_div_unio")
        res_as_dfik_div = create_symbolic_avc_val("res_as_dfik_div_unio")
        if not all([dfi_k_sym_b3, res_as_dfik_div, AS_const_sym, omega_smt_node]): return

        setup3 = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
        setup3.extend([
            Iff(dfi_k_sym_b3["is_finite"], TRUE()), # dfi_k is DFI # type: ignore
            avc_div_smt_logic(AS_const_sym, dfi_k_sym_b3, res_as_dfik_div, omega_smt_node) # type: ignore
        ])
        setup3.extend(get_base_avc_constraints(res_as_dfik_div, omega_smt_node, current_omega_py)) # type: ignore
        prop3 = avc_equiv_smt(res_as_dfik_div, AS_const_sym) # type: ignore
        prove_or_find_counterexample_smt(prop_name3, current_omega_py, setup3, prop3, # type: ignore
                                         [dfi_k_sym_b3, AS_const_sym, res_as_dfik_div], # type: ignore
                                         expect_property_to_hold=True)

def smt_test_division_dfi_cases(current_omega_py: int):
    property_name_base = f"SMT Division DFI Cases (⊘_v1.2B)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None or AS_const_sym is None: # type: ignore
        _report_native_test_result(property_name_base + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return
    if current_omega_py < 2: # Need DFI for non-trivial tests
        _report_native_test_result(property_name_base + f" SKIPPED (Ω={current_omega_py})", current_omega_py, True, "VACUOUS_NO_DFI_PAIRS")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    omega_smt_node = Int(current_omega_py) # type: ignore

    # Case 1: Exact DFI/DFI -> DFI (e.g., For Ω=4, Fp(2) ⊘ Fp(1) = Fp(2))
    if current_omega_py >= 2: # Fp(1) exists
        prop_name1 = property_name_base + " Exact DFI/DFI -> DFI (e.g. Ω=4, 2⊘1=2)"
        a1_val = 2 if current_omega_py >=3 else 1 # Ensure 'a' is valid DFI
        b1_val = 1
        exp_res1_val = a1_val // b1_val

        if a1_val < current_omega_py and exp_res1_val < current_omega_py and exp_res1_val >=1 : # Ensure test case is valid for current Omega
            a1 = create_symbolic_avc_val("a1_div_dfi")
            b1 = create_symbolic_avc_val("b1_div_dfi")
            res1 = create_symbolic_avc_val("res1_div_dfi")
            expected_res1 = create_symbolic_avc_val("exp_res1_div_dfi")
            if not all([a1,b1,res1,expected_res1,omega_smt_node]): return

            setup1 = [
                Iff(a1["is_finite"], TRUE()), Equals(a1["val"], Int(a1_val)), # type: ignore
                Iff(b1["is_finite"], TRUE()), Equals(b1["val"], Int(b1_val)), # type: ignore
                Iff(expected_res1["is_finite"], TRUE()), Equals(expected_res1["val"], Int(exp_res1_val)), # type: ignore
                avc_div_smt_logic(a1,b1,res1,omega_smt_node) # type: ignore
            ]
            setup1.extend(get_base_avc_constraints(res1, omega_smt_node, current_omega_py)) # type: ignore
            prove_or_find_counterexample_smt(prop_name1, current_omega_py, setup1,
                                             avc_equiv_smt(res1, expected_res1), # type: ignore
                                             [a1,b1,res1,expected_res1], expect_property_to_hold=True)
        else: # Test case not suitable for current Omega
            _report_native_test_result(prop_name1 + f" SKIPPED (case invalid for Ω={current_omega_py})", current_omega_py, True, "CASE_INVALID")
            smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1


    # Case 2: Non-exact DFI/DFI -> AREO_UNIO (e.g., For Ω=4, Fp(3) ⊘ Fp(2) = AU)
    if current_omega_py >= 4: # Requires Fp(3), Fp(2)
        prop_name2 = property_name_base + " Non-Exact DFI/DFI -> AREO_UNIO (e.g. Ω=4, 3⊘2=AU)"
        a2 = create_symbolic_avc_val("a2_div_dfi_au")
        b2 = create_symbolic_avc_val("b2_div_dfi_au")
        res2 = create_symbolic_avc_val("res2_div_dfi_au")
        if not all([a2,b2,res2,AS_const_sym,omega_smt_node]): return

        setup2 = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
        setup2.extend([
            Iff(a2["is_finite"], TRUE()), Equals(a2["val"], Int(3)), # type: ignore
            Iff(b2["is_finite"], TRUE()), Equals(b2["val"], Int(2)), # type: ignore
            avc_div_smt_logic(a2,b2,res2,omega_smt_node) # type: ignore
        ])
        setup2.extend(get_base_avc_constraints(res2, omega_smt_node, current_omega_py)) # type: ignore
        prove_or_find_counterexample_smt(prop_name2, current_omega_py, setup2,
                                         avc_equiv_smt(res2, AS_const_sym), # type: ignore
                                         [a2,b2,res2,AS_const_sym], expect_property_to_hold=True) # type: ignore
    elif current_omega_py >=2 : # For smaller Omegas where this specific case (3/2) doesn't apply, mark skipped
        _report_native_test_result(property_name_base + " Non-Exact DFI/DFI (3⊘2) SKIPPED", current_omega_py, True, "CASE_NA_FOR_OMEGA")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1


    # Case 3: DFI/DFI where quotient is 0 -> AREO_UNIO (e.g., For Ω=3, Fp(1) ⊘ Fp(2) = AU)
    if current_omega_py >= 3: # Requires Fp(1), Fp(2)
        prop_name3 = property_name_base + " DFI/DFI (quotient 0) -> AREO_UNIO (e.g. Ω=3, 1⊘2=AU)"
        a3 = create_symbolic_avc_val("a3_div_dfi_au_qzero")
        b3 = create_symbolic_avc_val("b3_div_dfi_au_qzero")
        res3 = create_symbolic_avc_val("res3_div_dfi_au_qzero")
        if not all([a3,b3,res3,AS_const_sym,omega_smt_node]): return

        setup3 = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
        setup3.extend([
            Iff(a3["is_finite"], TRUE()), Equals(a3["val"], Int(1)), # type: ignore
            Iff(b3["is_finite"], TRUE()), Equals(b3["val"], Int(2)), # type: ignore
            avc_div_smt_logic(a3,b3,res3,omega_smt_node) # type: ignore
        ])
        setup3.extend(get_base_avc_constraints(res3, omega_smt_node, current_omega_py)) # type: ignore
        prove_or_find_counterexample_smt(prop_name3, current_omega_py, setup3,
                                         avc_equiv_smt(res3, AS_const_sym), # type: ignore
                                         [a3,b3,res3,AS_const_sym], expect_property_to_hold=True) # type: ignore
    elif current_omega_py >=2 :
        _report_native_test_result(property_name_base + " DFI/DFI (1⊘2) SKIPPED", current_omega_py, True, "CASE_NA_FOR_OMEGA")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1

# Initial SMT test for a constrained Round-Trip Law for Division
def smt_test_division_round_trip_constrained(current_omega_py: int):
    property_name = f"SMT Division Round-Trip Constrained ((a⊘b)⊗b == a)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED (SMT UNAVAILABLE)", current_omega_py, True)
        return
    if current_omega_py < 2 : # Needs DFI
        _report_native_test_result(property_name + f" SKIPPED (Ω={current_omega_py})", current_omega_py, True, "VACUOUS")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    a_rt = create_symbolic_avc_val("a_div_rt")
    b_rt = create_symbolic_avc_val("b_div_rt")
    q_rt = create_symbolic_avc_val("q_div_rt") # a / b
    lhs_rt = create_symbolic_avc_val("lhs_div_rt") # (a/b)*b

    if not all([a_rt, b_rt, q_rt, lhs_rt, omega_smt_node]): return

    # Constraints for the law to hold:
    # 1. a, b are DFI
    # 2. b divides a exactly (remainder is 0 for a_val, b_val)
    # 3. Quotient q = a/b is a valid DFI element (1 <= q < Omega)
    # 4. (a/b)*b does not overflow (result is DFI)
    
    # Symbolic remainder and quotient from a_rt["val"] and b_rt["val"]
    smt_q_val = Div(a_rt["val"], b_rt["val"]) # type: ignore
    smt_r_val = Minus(a_rt["val"], Times(b_rt["val"], smt_q_val)) # type: ignore
    
    constraints = [
        Iff(a_rt["is_finite"], TRUE()), # a is DFI # type: ignore
        Iff(b_rt["is_finite"], TRUE()), # b is DFI # type: ignore
        Equals(smt_r_val, Int(0)),      # b divides a exactly # type: ignore
        smt_q_val >= Int(1),            # quotient is >= 1 # type: ignore
        smt_q_val < omega_smt_node,     # quotient is < Omega # type: ignore
        
        avc_div_smt_logic(a_rt, b_rt, q_rt, omega_smt_node), # type: ignore
        Iff(q_rt["is_finite"], TRUE()), # Ensure intermediate q_rt is DFI # type: ignore
        Equals(q_rt["val"], smt_q_val), # Ensure q_rt is the actual quotient # type: ignore

        avc_mul_smt_logic(q_rt, b_rt, lhs_rt, omega_smt_node), # type: ignore
        Iff(lhs_rt["is_finite"], TRUE()) # Ensure (a/b)*b does not overflow to Unio # type: ignore
    ]
    setup_formulas = list(constraints) # Make a mutable copy
    # Add base constraints for results (q_rt and lhs_rt are constrained by their logic here)
    # No, q_rt and lhs_rt are results of ops, their base constraints should be added too
    setup_formulas.extend(get_base_avc_constraints(q_rt, omega_smt_node, current_omega_py)) # type: ignore
    setup_formulas.extend(get_base_avc_constraints(lhs_rt, omega_smt_node, current_omega_py)) # type: ignore


    property_to_verify = avc_equiv_smt(lhs_rt, a_rt) # type: ignore
    
    # This constrained version is expected to hold.
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a_rt, b_rt, q_rt, lhs_rt], 
                                     expect_property_to_hold=True)

def smt_test_additive_right_alternative_law(current_omega_py: int):
    # (b⊕a)⊕a == b⊕(a⊕a)
    property_name = f"SMT Additive Right Alternative Law (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return
        
    expected_to_hold = (current_omega_py <= 2) # Holds iff Ω <= 2
    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_right_alt")
    b = create_symbolic_avc_val("b_right_alt")
    
    # LHS: (b⊕a)⊕a
    b_plus_a_lhs = create_symbolic_avc_val("bpa_lhs_right_alt")
    lhs = create_symbolic_avc_val("lhs_right_alt")
    
    # RHS: b⊕(a⊕a)
    a_plus_a_rhs = create_symbolic_avc_val("apa_rhs_right_alt")
    rhs = create_symbolic_avc_val("rhs_right_alt")

    if not all ([a, b, b_plus_a_lhs, lhs, a_plus_a_rhs, rhs, omega_smt_node]): return

    setup_formulas = [
        # LHS
        avc_add_smt_logic(b, a, b_plus_a_lhs, omega_smt_node), # type: ignore
        avc_add_smt_logic(b_plus_a_lhs, a, lhs, omega_smt_node), # type: ignore
        # RHS
        avc_add_smt_logic(a, a, a_plus_a_rhs, omega_smt_node), # type: ignore
        avc_add_smt_logic(b, a_plus_a_rhs, rhs, omega_smt_node)  # type: ignore
    ]
    intermediate_results = [b_plus_a_lhs, lhs, a_plus_a_rhs, rhs]
    for res_sym in intermediate_results:
        setup_formulas.extend(get_base_avc_constraints(res_sym, omega_smt_node, current_omega_py)) # type: ignore
        
    property_to_verify = avc_equiv_smt(lhs, rhs) # type: ignore
    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a, b, b_plus_a_lhs, lhs, a_plus_a_rhs, rhs], 
                                     expect_property_to_hold=expected_to_hold)

def smt_test_additive_right_bol_identity(current_omega_py: int):
    # ((x⊕y)⊕z)⊕y == x⊕((y⊕z)⊕y)
    property_name = f"SMT Additive Right Bol Identity (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return

    expected_to_hold = (current_omega_py <= 2) # Holds iff Ω <= 2
    omega_smt_node = Int(current_omega_py) # type: ignore
    x = create_symbolic_avc_val("x_rbol")
    y = create_symbolic_avc_val("y_rbol")
    z = create_symbolic_avc_val("z_rbol")

    # LHS: ((x⊕y)⊕z)⊕y
    xy = create_symbolic_avc_val("xy_rbol")
    xyz = create_symbolic_avc_val("xyz_rbol")
    lhs = create_symbolic_avc_val("lhs_rbol")

    # RHS: x⊕((y⊕z)⊕y)
    yz = create_symbolic_avc_val("yz_rbol")
    yzy = create_symbolic_avc_val("yzy_rbol") # (y+z)+y
    rhs = create_symbolic_avc_val("rhs_rbol")
    
    if not all([x,y,z,xy,xyz,lhs,yz,yzy,rhs,omega_smt_node]): return

    setup_formulas = [
        # LHS
        avc_add_smt_logic(x,y,xy,omega_smt_node), # type: ignore
        avc_add_smt_logic(xy,z,xyz,omega_smt_node), # type: ignore
        avc_add_smt_logic(xyz,y,lhs,omega_smt_node), # type: ignore
        # RHS
        avc_add_smt_logic(y,z,yz,omega_smt_node), # type: ignore
        avc_add_smt_logic(yz,y,yzy,omega_smt_node), # type: ignore
        avc_add_smt_logic(x,yzy,rhs,omega_smt_node)  # type: ignore
    ]
    intermediate_results = [xy,xyz,lhs,yz,yzy,rhs]
    for res_sym in intermediate_results:
        setup_formulas.extend(get_base_avc_constraints(res_sym, omega_smt_node, current_omega_py)) # type: ignore

    property_to_verify = avc_equiv_smt(lhs,rhs) # type: ignore
    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})",
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [x,y,z,xy,xyz,lhs,yz,yzy,rhs],
                                     expect_property_to_hold=expected_to_hold)

def smt_test_unio_multiplicative_roles_explicit(current_omega_py: int):
    property_name_base = f"SMT Unio Multiplicative Roles Explicit (⊗_v1.2)"
    if not SMT_MODE_AVAILABLE or ZU_const_sym is None or AS_const_sym is None: # type: ignore
        _report_native_test_result(property_name_base + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    x_dfi = create_symbolic_avc_val("x_dfi_mul_unio") # Represents a DFI element
    
    res_zu_dfi = create_symbolic_avc_val("res_zu_dfi_mul")
    res_dfi_zu = create_symbolic_avc_val("res_dfi_zu_mul")
    res_as_dfi = create_symbolic_avc_val("res_as_dfi_mul")
    res_dfi_as = create_symbolic_avc_val("res_dfi_as_mul")
    res_zu_zu = create_symbolic_avc_val("res_zu_zu_mul")
    res_as_as = create_symbolic_avc_val("res_as_as_mul")
    res_zu_as = create_symbolic_avc_val("res_zu_as_mul")
    res_as_zu = create_symbolic_avc_val("res_as_zu_mul")

    if not all([x_dfi, res_zu_dfi, res_dfi_zu, res_as_dfi, res_dfi_as, 
                res_zu_zu, res_as_as, res_zu_as, res_as_zu,
                ZU_const_sym, AS_const_sym, omega_smt_node]): return

    setup_formulas = get_smt_unio_constant_constraints(ZU_const_sym, AS_const_sym, omega_smt_node) # type: ignore
    # Constrain x_dfi to be DFI if Omega > 1
    if current_omega_py > 1:
        setup_formulas.append(Iff(x_dfi["is_finite"], TRUE())) # type: ignore
    else: # Omega = 1, x_dfi must be Unio
        setup_formulas.append(Or(Iff(x_dfi["is_zero"], TRUE()), Iff(x_dfi["is_areo"], TRUE()))) # type: ignore
        # If x_dfi is forced to be Unio, some tests below are less meaningful for "DFI" interaction

    # Define all operations
    ops_to_define = [
        (ZU_const_sym, x_dfi, res_zu_dfi), (x_dfi, ZU_const_sym, res_dfi_zu),
        (AS_const_sym, x_dfi, res_as_dfi), (x_dfi, AS_const_sym, res_dfi_as),
        (ZU_const_sym, ZU_const_sym, res_zu_zu), (AS_const_sym, AS_const_sym, res_as_as),
        (ZU_const_sym, AS_const_sym, res_zu_as), (AS_const_sym, ZU_const_sym, res_as_zu)
    ]
    for op1, op2, res_op in ops_to_define:
        setup_formulas.append(avc_mul_smt_logic(op1, op2, res_op, omega_smt_node)) # type: ignore
        setup_formulas.extend(get_base_avc_constraints(res_op, omega_smt_node, current_omega_py)) # type: ignore
    
    # Properties based on v1.2 "Areo dominates, else Zero"
    # ZU * X_DFI -> ZU
    prop1 = Implies(Iff(x_dfi["is_finite"], TRUE()), avc_equiv_smt(res_zu_dfi, ZU_const_sym)) if current_omega_py > 1 else TRUE() # type: ignore
    # AS * X_DFI -> AS
    prop2 = Implies(Iff(x_dfi["is_finite"], TRUE()), avc_equiv_smt(res_as_dfi, AS_const_sym)) if current_omega_py > 1 else TRUE() # type: ignore
    # ZU * ZU -> ZU
    prop3 = avc_equiv_smt(res_zu_zu, ZU_const_sym) # type: ignore
    # AS * AS -> AS
    prop4 = avc_equiv_smt(res_as_as, AS_const_sym) # type: ignore
    # ZU * AS -> AS
    prop5 = avc_equiv_smt(res_zu_as, AS_const_sym) # type: ignore
    # AS * ZU -> AS
    prop6 = avc_equiv_smt(res_as_zu, AS_const_sym) # type: ignore

    # Commutativity checks are implicitly covered if prop1/prop2 use generic x_dfi
    # and we check res_dfi_zu and res_dfi_as similarly
    
    property_to_verify = And(prop1, prop2, prop3, prop4, prop5, prop6) # type: ignore

    prove_or_find_counterexample_smt(property_name_base, current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [x_dfi, ZU_const_sym, AS_const_sym] + [item[2] for item in ops_to_define], # type: ignore
                                     expect_property_to_hold=True)

def smt_test_dfi_non_closure_add(current_omega_py: int):
    property_name = f"SMT DFI Non-Closure for Addition (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return

    if current_omega_py <= 1: # DFI is empty, so cannot pick two DFI elements
        _report_native_test_result(property_name + f" SKIPPED (Ω={current_omega_py}, DFI empty)", current_omega_py, True, "VACUOUS")
        smt_test_results_summary[current_omega_py]["skipped"] = smt_test_results_summary[current_omega_py].get("skipped",0) + 1
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_dfi_nonclose_add")
    b = create_symbolic_avc_val("b_dfi_nonclose_add")
    res_ab = create_symbolic_avc_val("res_ab_dfi_nonclose_add")
    if not all([a,b,res_ab,omega_smt_node]): return

    setup_formulas = [
        Iff(a["is_finite"], TRUE()), # type: ignore
        Iff(b["is_finite"], TRUE()), # type: ignore
        avc_add_smt_logic(a,b,res_ab,omega_smt_node) # type: ignore
    ]
    setup_formulas.extend(get_base_avc_constraints(res_ab, omega_smt_node, current_omega_py)) # type: ignore

    # Property: result is Unio (i.e., not DFI)
    property_to_verify = Or(Iff(res_ab["is_zero"], TRUE()), Iff(res_ab["is_areo"], TRUE())) # type: ignore
    
    # DFI is non-closed for ADD if Omega > 1 (which is true here)
    expected_to_find_witness = True 
    
    prove_or_find_counterexample_smt(property_name + f" (Expect: Exist)", current_omega_py, setup_formulas, 
                                     property_to_verify, # type: ignore
                                     [a,b,res_ab], 
                                     expect_property_to_hold=expected_to_find_witness, 
                                     is_existential=True)

def smt_test_additive_quasigroup_existence(current_omega_py: int):
    # ForAll a,b Exists x such that a + x = b
    property_name = f"SMT Additive Quasigroup Existence (a⊕x=b for ⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return

    omega_smt_node = Int(current_omega_py) # type: ignore
    a_qg = create_symbolic_avc_val("a_qg_exist")
    b_qg = create_symbolic_avc_val("b_qg_exist")
    x_qg = create_symbolic_avc_val("x_qg_exist") # The x we are looking for
    res_ax_qg = create_symbolic_avc_val("res_ax_qg_exist")

    if not all([a_qg, b_qg, x_qg, res_ax_qg, omega_smt_node]): return

    setup_formulas = [
        avc_add_smt_logic(a_qg, x_qg, res_ax_qg, omega_smt_node) # type: ignore
    ]
    setup_formulas.extend(get_base_avc_constraints(res_ax_qg, omega_smt_node, current_omega_py)) # type: ignore
    
    # Property: res_ax_qg is equivalent to b_qg
    property_solves_equation = avc_equiv_smt(res_ax_qg, b_qg) # type: ignore
    
    # Expected to hold for all Omega (existence of solution)
    prove_or_find_counterexample_smt(property_name, current_omega_py, setup_formulas, 
                                     property_solves_equation, # type: ignore
                                     [a_qg, b_qg, x_qg, res_ax_qg], 
                                     expect_property_to_hold=True, 
                                     is_existential=True) # Test for existence of x

def smt_test_additive_power_associativity(current_omega_py: int):
    # (a⊕a)⊕a == a⊕(a⊕a)
    property_name = f"SMT Additive Power Associativity (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return
        
    expected_to_hold = True # Power associativity holds for all Ω
    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_pow_assoc")
    
    # LHS: (a⊕a)⊕a
    a_plus_a_lhs = create_symbolic_avc_val("apa_lhs_pow_assoc")
    lhs = create_symbolic_avc_val("lhs_pow_assoc")
    
    # RHS: a⊕(a⊕a)
    a_plus_a_rhs = create_symbolic_avc_val("apa_rhs_pow_assoc") # Can be the same as apa_lhs if logic is careful
    rhs = create_symbolic_avc_val("rhs_pow_assoc")

    if not all ([a, a_plus_a_lhs, lhs, a_plus_a_rhs, rhs, omega_smt_node]): return

    setup_formulas = [
        # LHS
        avc_add_smt_logic(a, a, a_plus_a_lhs, omega_smt_node), # type: ignore
        avc_add_smt_logic(a_plus_a_lhs, a, lhs, omega_smt_node), # type: ignore
        # RHS
        avc_add_smt_logic(a, a, a_plus_a_rhs, omega_smt_node), # type: ignore
        avc_add_smt_logic(a, a_plus_a_rhs, rhs, omega_smt_node)  # type: ignore
    ]
    intermediate_results = [a_plus_a_lhs, lhs, a_plus_a_rhs, rhs]
    for res_sym in intermediate_results:
        setup_formulas.extend(get_base_avc_constraints(res_sym, omega_smt_node, current_omega_py)) # type: ignore
        
    property_to_verify = avc_equiv_smt(lhs, rhs) # type: ignore
    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a, a_plus_a_lhs, lhs, a_plus_a_rhs, rhs], 
                                     expect_property_to_hold=expected_to_hold)

def smt_test_additive_left_alternative_law(current_omega_py: int):
    # (a⊕a)⊕b == a⊕(a⊕b)
    property_name = f"SMT Additive Left Alternative Law (⊕_v1.1)"
    if not SMT_MODE_AVAILABLE:
        _report_native_test_result(property_name + " SKIPPED", current_omega_py, True, "SMT_UNAVAILABLE")
        return
        
    expected_to_hold = (current_omega_py <= 2) # Holds iff Ω <= 2
    omega_smt_node = Int(current_omega_py) # type: ignore
    a = create_symbolic_avc_val("a_left_alt")
    b = create_symbolic_avc_val("b_left_alt")
    
    # LHS: (a⊕a)⊕b
    a_plus_a_lhs = create_symbolic_avc_val("apa_lhs_left_alt")
    lhs = create_symbolic_avc_val("lhs_left_alt")
    
    # RHS: a⊕(a⊕b)
    a_plus_b_rhs = create_symbolic_avc_val("apb_rhs_left_alt")
    rhs = create_symbolic_avc_val("rhs_left_alt")

    if not all ([a, b, a_plus_a_lhs, lhs, a_plus_b_rhs, rhs, omega_smt_node]): return

    setup_formulas = [
        # LHS
        avc_add_smt_logic(a, a, a_plus_a_lhs, omega_smt_node), # type: ignore
        avc_add_smt_logic(a_plus_a_lhs, b, lhs, omega_smt_node), # type: ignore
        # RHS
        avc_add_smt_logic(a, b, a_plus_b_rhs, omega_smt_node), # type: ignore
        avc_add_smt_logic(a, a_plus_b_rhs, rhs, omega_smt_node)  # type: ignore
    ]
    intermediate_results = [a_plus_a_lhs, lhs, a_plus_b_rhs, rhs]
    for res_sym in intermediate_results:
        setup_formulas.extend(get_base_avc_constraints(res_sym, omega_smt_node, current_omega_py)) # type: ignore
        
    property_to_verify = avc_equiv_smt(lhs, rhs) # type: ignore
    prove_or_find_counterexample_smt(property_name + f" (Expect: {'Holds' if expected_to_hold else 'Fails'})", 
                                     current_omega_py, setup_formulas, property_to_verify, # type: ignore
                                     [a, b, a_plus_a_lhs, lhs, a_plus_b_rhs, rhs], 
                                     expect_property_to_hold=expected_to_hold)

def run_smt_foundational_tests(omega_values_to_test: List[int]):
    print("\n====== Running SMT Foundational Stress Tests ======")
    # Previous: add(c,a,id,inv_ex,inv_uq,inv_count_spec), Mul(c,a,zd,fp1_id,fp1_not_id), Distrib, Cancel(a,m) = 14
    # Sub(id,stuck,noncomm,nonassoc, dfi_cases(3parts)) = 4+3 = 7
    # Div(unio(3), dfi(3), round_trip(1)) = 7
    # New Add (qg_exist, pow_assoc, left_alt) = 3
    # This round: Add(RAlt, RBol) = 2, Mul(Unio_Roles) = 1 (complex test), DFI_NonClosure_Add = 1
    # Total approx = 14 + 7 + 7 + 3 + 2 + 1 + 1 = 35
    num_intended_smt_tests_approx = 35

    if not SMT_MODE_AVAILABLE:
        print("  SMT tests cannot run because PySMT/Solver is not available.")
        for omega_val in omega_values_to_test:
            _initialize_smt_omega_results(omega_val) # Ensures entry exists
            smt_test_results_summary[omega_val]["skipped"] += num_intended_smt_tests_approx
        return

    for omega_val in omega_values_to_test:
        print(f"\n--- SMT Tests for Ω = {omega_val} ---")
        if omega_val == 0: 
            print(f"  SKIPPING SMT Tests for invalid Ω = {omega_val}")
            _initialize_smt_omega_results(omega_val)
            smt_test_results_summary[omega_val]["skipped"] += num_intended_smt_tests_approx
            continue
        
        # === Addition Properties ===
        smt_test_commutativity_add(omega_val)
        smt_test_associativity_add(omega_val)
        smt_test_additive_identity(omega_val)
        smt_test_additive_inverses_existence(omega_val)
        smt_test_additive_inverses_uniqueness_pattern(omega_val)
        smt_test_dfi_additive_inverse_count_specific_case(omega_val)
        smt_test_additive_quasigroup_existence(omega_val) 
        smt_test_additive_power_associativity(omega_val)   
        smt_test_additive_left_alternative_law(omega_val) 
        smt_test_additive_right_alternative_law(omega_val) # New
        smt_test_additive_right_bol_identity(omega_val)    # New

        # === Multiplication Properties ===
        smt_test_commutativity_mul(omega_val)         
        smt_test_associativity_mul(omega_val)         
        smt_test_zero_divisors_mul(omega_val) 
        smt_test_fp1_multiplicative_identity_for_dfi(omega_val)
        smt_test_fp1_not_universal_multiplicative_identity(omega_val)
        smt_test_unio_multiplicative_roles_explicit(omega_val) # New
        
        # === DFI Properties ===
        smt_test_dfi_non_closure_add(omega_val) # New (can add for other ops later)

        # === Mixed Properties ===
        smt_test_distributivity_mul_over_add(omega_val) 
        
        # === Cancellation Laws ===
        smt_test_additive_cancellation(omega_val) 
        smt_test_multiplicative_cancellation(omega_val)

        # === Subtraction Properties ===
        smt_test_subtraction_right_identity(omega_val)
        smt_test_subtraction_stuck_at_areo(omega_val)
        smt_test_subtraction_non_commutativity(omega_val)
        smt_test_subtraction_non_associativity(omega_val)
        smt_test_subtraction_dfi_cases(omega_val)

        # === Division Properties ===
        smt_test_division_unio_interactions(omega_val)
        smt_test_division_dfi_cases(omega_val)
        smt_test_division_round_trip_constrained(omega_val)
        
        
    # --- SMT Test Summary Printing Logic (remains the same as your last working version) ---
    print("\n--- SMT Test Summary ---")
    total_passed_smt = 0
    total_failed_smt = 0
    total_skipped_smt = 0
    # Ensure summary is initialized for all omegas tested
    for omega_val_summary in omega_values_to_test: 
        if omega_val_summary not in smt_test_results_summary:
            _initialize_smt_omega_results(omega_val_summary)

    for omega_val, results in sorted(smt_test_results_summary.items()):
        passed = results.get("passed", 0)
        failed = results.get("failed", 0)
        skipped = results.get("skipped", 0)
        total_passed_smt += passed
        total_failed_smt += failed
        total_skipped_smt += skipped
        print(f"  Ω={omega_val}: Passed={passed}, Failed={failed}, Skipped={skipped}")
    
    # Corrected version for the problematic SMT failure details loop:
    if smt_test_failures_details:
        print("\n  --- SMT Test Failure Details ---")
        for failure in sorted(smt_test_failures_details, key=lambda x: x['omega']): # type: ignore
            print(f"    Ω={failure['omega']}, Property='{failure['property']}'")
            # The 'message' field already contains a detailed status including expected/observed.
            print(f"      Message: {failure['message']}") 
            
            # Use 'model_str' and 'model_available' which are stored in the failure dictionary
            model_str_to_print = failure.get('model_str', "N/A")
            model_is_available = failure.get('model_available', False)
            is_existential_failure = failure.get('is_existential', False)
            observed_holds_failure = failure.get('observed_holds', False)
            # expected_to_hold_failure = failure.get('expected_to_hold', False) # For more refined label if needed

            if model_is_available and model_str_to_print and model_str_to_print != "N/A" and not isinstance(model_str_to_print, Exception):
                label = "Model Details" # Generic default
                if is_existential_failure:
                    label = "Witness" if observed_holds_failure else "Details (No Witness)"
                else: # Universal
                    label = "Counterexample" if not observed_holds_failure else "Details (No Counterexample)"
                
                # Further refinement for the label (optional, but makes output clearer)
                # This logic should ideally match the immediate print logic in prove_or_find_counterexample_smt for consistency
                # For simplicity here, we'll use the determined label.

                # Avoid printing redundant "No witness found" if already in message or N/A
                # This condition might need further refinement based on exact content of model_str_to_print vs message
                if not ( (is_existential_failure and not observed_holds_failure and "No witness found" in model_str_to_print) or \
                         (not is_existential_failure and observed_holds_failure and model_str_to_print == "N/A") ): # type: ignore
                     print(f"      {label}: {model_str_to_print}")

    if total_failed_smt == 0 and total_passed_smt > 0 :
        print("✅ All executed SMT foundational tests PASSED (or matched expectations)!")
    elif total_passed_smt == 0 and total_failed_smt == 0 and total_skipped_smt > 0:
        print("⚪ All SMT foundational tests were SKIPPED.")
    elif total_failed_smt == 0 and total_passed_smt == 0 and total_skipped_smt == 0:
        print("⚪ No SMT foundational tests were executed or recorded.")
    else:
        print("❌ SOME SMT FOUNDATIONAL TESTS FAILED (or did not match expectations)!")
    print("==========================================")
    print("\n====== Running SMT Foundational Stress Tests ======")
    if not SMT_MODE_AVAILABLE:
        print("  SMT tests cannot run because PySMT/Solver is not available.")
        num_potential_tests = 11 # Updated count: add(comm,assoc,id,inv_exist,inv_uniq), mul(comm,assoc,zero_div), distrib, cancel(add,mul)
        for omega_val in omega_values_to_test:
            _initialize_smt_omega_results(omega_val)
            smt_test_results_summary[omega_val]["skipped"] += num_potential_tests 
        return

    for omega_val in omega_values_to_test:
        print(f"\n--- SMT Tests for Ω = {omega_val} ---")
        if omega_val == 0:
            print(f"  SKIPPING SMT Tests for invalid Ω = {omega_val}")
            _initialize_smt_omega_results(omega_val)
            smt_test_results_summary[omega_val]["skipped"] += 11 # Number of tests below
            continue
        
        # Call SMT test functions
        smt_test_commutativity_add(omega_val)
        smt_test_associativity_add(omega_val)
        smt_test_additive_identity(omega_val)
        # Add calls to smt_test_commutativity_mul, smt_test_associativity_mul, 
        # smt_test_distributivity_mul_over_add, smt_test_additive_inverses
        # once they are defined.
        smt_test_additive_inverses_existence(omega_val) # New

        smt_test_commutativity_mul(omega_val)          # New
        smt_test_associativity_mul(omega_val)          # New
        
        smt_test_distributivity_mul_over_add(omega_val) # New

    print("\n--- SMT Test Summary ---")
    total_passed_smt = 0
    total_failed_smt = 0
    total_skipped_smt = 0
    # Ensure summary is initialized for all omegas tested
    for omega_val_summary in omega_values_to_test:
        if omega_val_summary not in smt_test_results_summary:
            _initialize_smt_omega_results(omega_val_summary)

    for omega_val, results in sorted(smt_test_results_summary.items()):
        passed = results.get("passed", 0)
        failed = results.get("failed", 0)
        skipped = results.get("skipped", 0)
        total_passed_smt += passed
        total_failed_smt += failed
        total_skipped_smt += skipped
        print(f"  Ω={omega_val}: Passed={passed}, Failed={failed}, Skipped={skipped}")
    
    if smt_test_failures_details: # This loop starts around line 1779 in your pasted code
     print("\n  --- SMT Test Failure Details ---")
    for failure in sorted(smt_test_failures_details, key=lambda x: x['omega']): # type: ignore
        print(f"    Ω={failure['omega']}, Property='{failure['property']}'")
        print(f"      Expected: {'Hold' if failure['expected_to_hold'] else 'Fail'}, Observed: {'Holds' if failure['observed_holds'] else 'Fails/No Witness'}") # Around 1783
        print(f"      Message: {failure['message']}") # Around 1784
        # The following 'if' statement is where your traceback's line 1764 logically falls
        model_str_to_print = failure.get('model_str', "N/A")
        is_existential_failure = failure.get('is_existential', False)
        observed_holds_failure = failure.get('observed_holds', False)
            
        if model_str_to_print and model_str_to_print != "N/A":
                  label = "Witness/Counterexample" # Default label
                  if is_existential_failure:
                        label = "Witness" if observed_holds_failure else "Details (No Witness)"
                  else: # Universal property
                        label = "Counterexample" if not observed_holds_failure else "Details (No Counterexample)"
                  print(f"      {label}: {model_str_to_print}")    

    if total_failed_smt == 0 and total_passed_smt > 0 :
        print("✅ All executed SMT foundational tests PASSED (or matched expectations)!")
    elif total_passed_smt == 0 and total_failed_smt == 0 and total_skipped_smt > 0:
        print("⚪ All SMT foundational tests were SKIPPED.")
    elif total_failed_smt == 0 and total_passed_smt == 0 and total_skipped_smt == 0:
        print("⚪ No SMT foundational tests were executed or recorded.")
    else:
        print("❌ SOME SMT FOUNDATIONAL TESTS FAILED (or did not match expectations)!")
    print("==========================================")
# --- Main Execution Block ---
if __name__ == "__main__":
    print("AVCA Max-Brutality Stress-Testing & Research Programme Harness")
    print(f"SMT Mode Available: {SMT_MODE_AVAILABLE}")
    
    # --- Configuration for this run ---
    # Omegas for Native tests (exhaustive, usually smaller)
    native_omegas_for_testing = [1, 2, 3, 4] 
    current_omega_native_max = OMEGA_NATIVE_MAX_DEFAULT 

    # Omegas for SMT tests (can be same or include larger ones like 5, 7 for phase checks)
    smt_omegas_for_testing = [1, 2, 3, 5] # Common set from AVCA DraftV4 for SMT

    # == Run Native Foundational Tests ==
    run_native_foundational_tests(native_omegas_for_testing, current_omega_native_max)

    # == Run SMT Foundational Tests ==
    run_smt_foundational_tests(smt_omegas_for_testing)

    print("\nProgramme Finished.")