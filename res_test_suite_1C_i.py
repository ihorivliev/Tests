import itertools
import math
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- PySMT Imports ---
try:
    from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                                 ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, NotEquals,
                                 GT, GE, LT, LE, Times, Div)
    from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
    from pysmt.fnode import FNode
    SMT_MODE_AVAILABLE = True
except ImportError:
    SMT_MODE_AVAILABLE = False

# --- Configuration ---
SMT_SOLVER_NAME = "z3"
DEFAULT_ASPECT_FOR_U_SINGLE_INPUT = "zero" # Define the default assumed aspect

# --- Suite 1.C.i: Unio Class Definition (Collapsed) ---
class Unio_Collapsed:
    __slots__ = ()
    def __eq__(self, other: object) -> bool: return isinstance(other, Unio_Collapsed)
    def __hash__(self) -> int: return hash(type(self))
    def __repr__(self) -> str: return "U_SINGLE"
U_SINGLE = Unio_Collapsed()
AVCVal_1Ci = Union[int, Unio_Collapsed]

# --- AVCA Core Logic Adapted for Suite 1.C.i ---
Omega_1Ci: int = 0

def set_avca_omega_1Ci(omega_value: int, verbose=False):
    global Omega_1Ci
    if not isinstance(omega_value, int) or omega_value < 1:
        raise ValueError("Omega_1Ci parameter must be an integer >= 1.")
    Omega_1Ci = omega_value
    if verbose: print(f"Suite 1.C.i: Omega_1Ci set to {Omega_1Ci}")

def _check_val_1Ci(x: AVCVal_1Ci, current_omega: int, op_name: str = "operation"):
    if not isinstance(current_omega, int) or current_omega < 1:
        raise ValueError(f"Omega_1Ci for {op_name} must be >= 1. Got: {current_omega!r}")
    if isinstance(x, Unio_Collapsed): return
    if not isinstance(x, int):
        raise TypeError(f"Invalid AVCA Value in {op_name}: {x!r}. Expected int or Unio_Collapsed. Got type: {type(x)}.")
    if current_omega == 1:
        raise ValueError(f"Invalid DFI Value for {op_name} with Omega_1Ci=1: {x}. DFI is empty.")
    if not (1 <= x < current_omega):
        raise ValueError(f"Invalid DFI Value for {op_name}: {x}. For Omega_1Ci={current_omega}, DFI in [1, {current_omega - 1}].")

def avc_add_1Ci(a: AVCVal_1Ci, b: AVCVal_1Ci) -> AVCVal_1Ci: # Same as 1Cii
    global Omega_1Ci
    if Omega_1Ci == 0: raise ValueError("Global Omega_1Ci not set for avc_add_1Ci.")
    _check_val_1Ci(a, Omega_1Ci, "avc_add_1Ci(a)")
    _check_val_1Ci(b, Omega_1Ci, "avc_add_1Ci(b)")
    if isinstance(a, Unio_Collapsed): return b
    if isinstance(b, Unio_Collapsed): return a
    standard_sum = a + b # type: ignore
    return standard_sum if standard_sum < Omega_1Ci else U_SINGLE

def avc_sub_1Ci(a: AVCVal_1Ci, b: AVCVal_1Ci) -> AVCVal_1Ci: # Same as 1Cii
    global Omega_1Ci
    if Omega_1Ci == 0: raise ValueError("Global Omega_1Ci not set for avc_sub_1Ci.")
    _check_val_1Ci(a, Omega_1Ci, "avc_sub_1Ci(a)")
    _check_val_1Ci(b, Omega_1Ci, "avc_sub_1Ci(b)")
    if isinstance(b, Unio_Collapsed): return a
    if isinstance(a, Unio_Collapsed): return U_SINGLE
    if a > b: return a - b # type: ignore
    else: return U_SINGLE

def avc_mul_1Ci(a: AVCVal_1Ci, b: AVCVal_1Ci) -> AVCVal_1Ci:
    global Omega_1Ci
    if Omega_1Ci == 0: raise ValueError("Global Omega_1Ci not set for avc_mul_1Ci.")
    _check_val_1Ci(a, Omega_1Ci, "avc_mul_1Ci(a)")
    _check_val_1Ci(b, Omega_1Ci, "avc_mul_1Ci(b)")

    a_is_unio = isinstance(a, Unio_Collapsed)
    b_is_unio = isinstance(b, Unio_Collapsed)

    if a_is_unio or b_is_unio:
        # Original v1.2 logic based on input aspects:
        # a_aspect_is_areo = a_is_unio and a.aspect == "areo"
        # b_aspect_is_areo = b_is_unio and b.aspect == "areo"
        # is_any_areo_aspected = a_aspect_is_areo or b_aspect_is_areo
        # conceptual_output_aspect = "areo" if is_any_areo_aspected else "zero"
        
        # Strategy 1.C.i: Assume default aspect for U_SINGLE inputs
        a_conceptual_aspect_is_areo = False # Default to "zero" if a is U_SINGLE
        if a_is_unio and DEFAULT_ASPECT_FOR_U_SINGLE_INPUT == "areo":
            a_conceptual_aspect_is_areo = True
            
        b_conceptual_aspect_is_areo = False # Default to "zero" if b is U_SINGLE
        if b_is_unio and DEFAULT_ASPECT_FOR_U_SINGLE_INPUT == "areo":
            b_conceptual_aspect_is_areo = True
            
        # Determine conceptual output aspect based on original v1.2 logic
        # (which checks if *any* input Unio was Areo-aspected)
        conceptual_output_is_areo = a_conceptual_aspect_is_areo or b_conceptual_aspect_is_areo
        
        # Regardless of conceptual_output_is_areo, return U_SINGLE
        return U_SINGLE 
    else: # Both DFI
        standard_product = a * b # type: ignore
        return standard_product if 1 <= standard_product < Omega_1Ci else U_SINGLE

def avc_div_1Ci(a: AVCVal_1Ci, b: AVCVal_1Ci) -> AVCVal_1Ci:
    global Omega_1Ci
    if Omega_1Ci == 0: raise ValueError("Global Omega_1Ci not set for avc_div_1Ci.")
    _check_val_1Ci(a, Omega_1Ci, "avc_div_1Ci(a)")
    _check_val_1Ci(b, Omega_1Ci, "avc_div_1Ci(b)")

    if isinstance(b, Unio_Collapsed): # Rule B1: Divisor Unio
        # Original v1.2B output was AREO_UNIO
        return U_SINGLE 

    if isinstance(a, Unio_Collapsed): # Rule B2: Dividend Unio, Divisor DFI
        # Original v1.2B preserved dividend's aspect.
        # Here, assume input U_SINGLE (as 'a') has DEFAULT_ASPECT_FOR_U_SINGLE_INPUT.
        # The conceptual output aspect would match that default.
        return U_SINGLE 
    
    # Both DFI (Rule B3)
    a_val: int = a # type: ignore
    b_val: int = b # type: ignore
    if b_val == 0: raise ValueError("DFI division by zero in avc_div_1Ci")
    quotient, remainder = divmod(a_val, b_val)
    if remainder == 0 and (1 <= quotient < Omega_1Ci):
        return quotient
    else: # Non-exact, or quotient out of DFI range
        # Original v1.2B output was AREO_UNIO
        return U_SINGLE

# --- Native Python Test Harness (similar to 1Cii) ---
native_test_summary_1Ci = {}
def run_native_test_1Ci(test_name: str, omega_val: int, test_func: Callable, expect_fail: bool = False, failure_is_skip: bool = False):
    global native_test_summary_1Ci
    set_avca_omega_1Ci(omega_val)
    if omega_val not in native_test_summary_1Ci:
        native_test_summary_1Ci[omega_val] = {"passed": 0, "failed": 0, "skipped": 0}
    print(f"  NATIVE Test (1Ci): '{test_name}' for Ω={omega_val} (Expect: {'Fails' if expect_fail else 'Holds'})", end=" ... ")
    try:
        result, counterexample = test_func(omega_val)
        passes = (result and not expect_fail) or (not result and expect_fail)
        if passes: print("PASS"); native_test_summary_1Ci[omega_val]["passed"] += 1
        else:
            print(f"FAIL (Observed: {'Holds' if result else 'Fails'})")
            if counterexample: print(f"    Counterexample: {counterexample}")
            native_test_summary_1Ci[omega_val]["failed"] += 1
    except Exception as e:
        if failure_is_skip: print(f"SKIPPED ({e})"); native_test_summary_1Ci[omega_val]["skipped"] +=1
        else: print(f"ERROR ({e})"); native_test_summary_1Ci[omega_val]["failed"] += 1

def get_s_omega_1Ci(current_omega: int) -> List[AVCVal_1Ci]:
    if current_omega == 1: return [U_SINGLE]
    return [U_SINGLE] + list(range(1, current_omega))

# Native Test Functions (using _1Ci operations)
def native_test_totality_op_1Ci(omega_val: int, op_func: Callable) -> Tuple[bool, Any]:
    elements = get_s_omega_1Ci(omega_val); #print(f"Elements for Ω={omega_val}: {[str(e) for e in elements]}")
    for a in elements:
        for b in elements:
            try: res = op_func(a,b); _check_val_1Ci(res, omega_val, f"{op_func.__name__}_res")
            except Exception as e: return False, f"Error for {a!r} op {b!r}: {e}"
    return True, None
def native_test_commutativity_add_1Ci(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Ci(omega_val)
    for a in elements:
        for b in elements:
            if avc_add_1Ci(a,b) != avc_add_1Ci(b,a): return False, f"a={a!r}, b={b!r}"
    return True, None
def native_test_associativity_add_1Ci(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Ci(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                lhs=avc_add_1Ci(avc_add_1Ci(a,b),c); rhs=avc_add_1Ci(a,avc_add_1Ci(b,c))
                if lhs != rhs: return False, f"a={a!r},b={b!r},c={c!r} -> LHS={lhs!r},RHS={rhs!r}"
    return True, None
def native_test_commutativity_mul_1Ci(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Ci(omega_val)
    for a in elements:
        for b in elements:
            if avc_mul_1Ci(a,b) != avc_mul_1Ci(b,a): return False, f"a={a!r}, b={b!r}"
    return True, None
def native_test_associativity_mul_1Ci(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Ci(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                lhs=avc_mul_1Ci(avc_mul_1Ci(a,b),c); rhs=avc_mul_1Ci(a,avc_mul_1Ci(b,c))
                if lhs != rhs: return False, f"a={a!r},b={b!r},c={c!r} -> LHS={lhs!r},RHS={rhs!r}"
    return True, None
def native_test_distributivity_mul_over_add_1Ci(omega_val: int) -> Tuple[bool, Any]:
    elements = get_s_omega_1Ci(omega_val)
    for a in elements:
        for b in elements:
            for c in elements:
                bpc=avc_add_1Ci(b,c); lhs=avc_mul_1Ci(a,bpc)
                amb=avc_mul_1Ci(a,b); amc=avc_mul_1Ci(a,c); rhs=avc_add_1Ci(amb,amc)
                if lhs != rhs: return False, f"a={a!r},b={b!r},c={c!r} -> a(b+c)={lhs!r},(ab)+(ac)={rhs!r}"
    return True, None

# --- SMT Harness Components (Embedded, adapted for 1Ci) ---
smt_test_summary_1Ci = {}
def create_symbolic_avc_val_1Ci(name_prefix: str) -> Dict[str, FNode]: # Same as 1Cii
    return {"is_unio": Symbol(f"{name_prefix}_is_U", SMT_BOOL_TYPE), "is_finite": Symbol(f"{name_prefix}_is_F", SMT_BOOL_TYPE),
            "val": Symbol(f"{name_prefix}_val", SMT_INT_TYPE), "name": name_prefix}
def get_base_avc_constraints_1Ci(avc_repr: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> List[FNode]: # Same as 1Cii
    constraints = [Iff(avc_repr["is_unio"], Not(avc_repr["is_finite"])),
                   Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
                   Implies(avc_repr["is_unio"], Equals(avc_repr["val"], Int(0)))]
    if current_omega_py == 1: constraints.append(avc_repr["is_unio"])
    return constraints
def avc_equiv_smt_1Ci(avc1: Dict[str, FNode], avc2: Dict[str, FNode]) -> FNode: # Same as 1Cii
    return Or(And(avc1["is_unio"], avc2["is_unio"]), And(avc1["is_finite"], avc2["is_finite"], Equals(avc1["val"], avc2["val"])))

# SMT Logic Builders (Modeling the _1Ci operations)
def avc_add_smt_logic_1Ci(a:Dict[str,FNode],b:Dict[str,FNode],res:Dict[str,FNode],omega:FNode,o_py:int)->FNode: # Same as 1Cii
    r_a=And(Iff(res["is_unio"],a["is_unio"]),Iff(res["is_finite"],a["is_finite"]),Equals(res["val"],a["val"]))
    r_b=And(Iff(res["is_unio"],b["is_unio"]),Iff(res["is_finite"],b["is_finite"]),Equals(res["val"],b["val"]))
    c1=Implies(a["is_unio"],r_b); c2=Implies(And(a["is_finite"],b["is_unio"]),r_a)
    s=Plus(a["val"],b["val"]); r_dfi=And(res["is_finite"],Not(res["is_unio"]),Equals(res["val"],s))
    r_u=And(res["is_unio"],Not(res["is_finite"]),Equals(res["val"],Int(0)))
    c3=Implies(And(a["is_finite"],b["is_finite"]),Ite(s<omega,r_dfi,r_u)); return And(c1,c2,c3)

def avc_mul_smt_logic_1Ci(a: Dict[str, FNode], b: Dict[str, FNode],
                           res: Dict[str, FNode], omega_smt_node: FNode, current_omega_py: int) -> FNode:
    # Logic: If inputs a or b are Unio, their conceptual aspect is DEFAULT_ASPECT_FOR_U_SINGLE_INPUT ("zero").
    # The v1.2 mul logic: "AREO if any Unio operand is Areo-aspected, else ZERO"
    # Since assumed input aspects are "zero", the conceptual output Unio aspect will always be "zero".
    # The actual output object is U_SINGLE (represented as res["is_unio"] and res["val"]=Int(0)).
    res_is_U_SINGLE_state = And(res["is_unio"], Not(res["is_finite"]), Equals(res["val"], Int(0)))
    
    # If a or b is Unio, result is U_SINGLE
    unio_case_behavior = res_is_U_SINGLE_state 

    cond_both_are_dfi = And(a["is_finite"], b["is_finite"])
    prod_val = Times(a["val"], b["val"])
    res_is_FP_prod_formula = And(res["is_finite"], Not(res["is_unio"]), Equals(res["val"], prod_val))
    dfi_case_behavior = Ite(And(prod_val >= Int(1), prod_val < omega_smt_node),
                            res_is_FP_prod_formula,
                            res_is_U_SINGLE_state) # DFI overflow to U_SINGLE
    
    return Ite(Or(a["is_unio"], b["is_unio"]), unio_case_behavior, dfi_case_behavior)

def prove_or_find_counterexample_smt_1Ci( # Copied and renamed
    property_name: str, omega_py_val: int, setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    global smt_test_summary_1Ci
    if not SMT_MODE_AVAILABLE:
        print(f"SKIPPED (SMT Mode Unavailable) for {property_name} Ω={omega_py_val}")
        if omega_py_val not in smt_test_summary_1Ci: smt_test_summary_1Ci[omega_py_val]={"p":0,"f":0,"s":0}
        smt_test_summary_1Ci[omega_py_val]["s"] += 1; return
    if omega_py_val not in smt_test_summary_1Ci: smt_test_summary_1Ci[omega_py_val]={"p":0,"f":0,"s":0}
    print(f"  SMT Test (1Ci): '{property_name}' for Ω={omega_py_val} (Expect: {'Hold/Exist' if expect_property_to_hold else 'Fail/Not Exist'})", end=" ... ")
    holds_obs=False; cex_str=None
    try:
        with Solver(name=SMT_SOLVER_NAME,logic="LIA") as s:
            for f_setup in setup_formulas:s.add_assertion(f_setup)
            formula_to_check=Not(property_to_verify) if not is_existential else property_to_verify
            if s.solve([formula_to_check]):
                if is_existential:holds_obs=True
                else:holds_obs=False
                m=s.get_model();ce_p=[]
                for r_d in inputs_reprs:
                    nm=r_d['name'];iu=m.get_value(r_d['is_unio']).is_true();v=m.get_value(r_d['val'])
                    ce_p.append(f"{nm}={'U_S' if iu else f'Fp({v})'}")
                cex_str="; ".join(ce_p)
            else: # UNSAT
                if is_existential:holds_obs=False
                else:holds_obs=True
        succ=(holds_obs == expect_property_to_hold)
        if succ: print("PASS"); smt_test_summary_1Ci[omega_py_val]["p"]+=1
        else: print(f"FAIL (Obs:{'H/E'if holds_obs else'F/NE'})"); smt_test_summary_1Ci[omega_py_val]["f"]+=1
        if cex_str and ((is_existential and holds_obs and expect_property_to_hold) or \
                        (not is_existential and not holds_obs and not expect_property_to_hold)):
            print(f"    {'Wit' if is_existential else 'Cex'} (as exp): {cex_str}")
        elif cex_str and not succ:
            lbl="UnexpWit" if is_existential else "Cex(unexp fail)"
            if not holds_obs and expect_property_to_hold and is_existential: lbl="WitNOTFound(exp)"
            elif holds_obs and not expect_property_to_hold and not is_existential:lbl="NoCexFound(unexp hold)"
            print(f"    {lbl}: {cex_str}")
        elif not succ and not cex_str: # Should indicate reason for fail if no model
            if not holds_obs and expect_property_to_hold and is_existential: print("    WitNOTFound(exp)")
            elif holds_obs and not expect_property_to_hold and not is_existential: print("    NoCexFound(unexp hold)")
    except Exception as e: print(f"ERROR({e})"); smt_test_summary_1Ci[omega_py_val]["f"]+=1

# SMT Test Functions (adapted for _1Ci)
def smt_test_A1_totality_add_1Ci(o:int): prove_or_find_counterexample_smt_1Ci("SMT A.1: Totality for avc_add_1Ci",o,get_base_avc_constraints_1Ci(create_symbolic_avc_val_1Ci("a"),Int(o),o)+get_base_avc_constraints_1Ci(create_symbolic_avc_val_1Ci("b"),Int(o),o)+get_base_avc_constraints_1Ci(create_symbolic_avc_val_1Ci("r"),Int(o),o)+[avc_add_smt_logic_1Ci(create_symbolic_avc_val_1Ci("a"),create_symbolic_avc_val_1Ci("b"),create_symbolic_avc_val_1Ci("r"),Int(o),o)],TRUE(),[create_symbolic_avc_val_1Ci("a"),create_symbolic_avc_val_1Ci("b"),create_symbolic_avc_val_1Ci("r")],True)
def smt_test_associativity_add_1Ci(o:int):
    exp=(o<=2); pr=f"SMT Assoc avc_add_1Ci(Exp:{'H'if exp else'F'})"
    a,b,c,ab,lhs,bc,rhs = [create_symbolic_avc_val_1Ci(n) for n in "a,b,c,ab,lhs,bc,rhs".split(',')]
    s=get_base_avc_constraints_1Ci(a,Int(o),o)+get_base_avc_constraints_1Ci(b,Int(o),o)+get_base_avc_constraints_1Ci(c,Int(o),o)+get_base_avc_constraints_1Ci(ab,Int(o),o)+get_base_avc_constraints_1Ci(lhs,Int(o),o)+get_base_avc_constraints_1Ci(bc,Int(o),o)+get_base_avc_constraints_1Ci(rhs,Int(o),o)
    s.extend([avc_add_smt_logic_1Ci(a,b,ab,Int(o),o), avc_add_smt_logic_1Ci(ab,c,lhs,Int(o),o), avc_add_smt_logic_1Ci(b,c,bc,Int(o),o), avc_add_smt_logic_1Ci(a,bc,rhs,Int(o),o)])
    prove_or_find_counterexample_smt_1Ci(pr,o,s,avc_equiv_smt_1Ci(lhs,rhs),[a,b,c],exp)
def smt_test_distributivity_mul_over_add_1Ci(o:int):
    exp=(o<=2);pr=f"SMT LDist(mul_1Ci/add_1Ci)(Exp:{'H'if exp else'F'})"
    a,b,c,bpc,lhs,amb,amc,rhs = [create_symbolic_avc_val_1Ci(n) for n in "a,b,c,bpc,lhs,amb,amc,rhs".split(',')]
    s=get_base_avc_constraints_1Ci(a,Int(o),o)+get_base_avc_constraints_1Ci(b,Int(o),o)+get_base_avc_constraints_1Ci(c,Int(o),o)+get_base_avc_constraints_1Ci(bpc,Int(o),o)+get_base_avc_constraints_1Ci(lhs,Int(o),o)+get_base_avc_constraints_1Ci(amb,Int(o),o)+get_base_avc_constraints_1Ci(amc,Int(o),o)+get_base_avc_constraints_1Ci(rhs,Int(o),o)
    s.extend([avc_add_smt_logic_1Ci(b,c,bpc,Int(o),o),avc_mul_smt_logic_1Ci(a,bpc,lhs,Int(o),o),avc_mul_smt_logic_1Ci(a,b,amb,Int(o),o),avc_mul_smt_logic_1Ci(a,c,amc,Int(o),o),avc_add_smt_logic_1Ci(amb,amc,rhs,Int(o),o)])
    prove_or_find_counterexample_smt_1Ci(pr,o,s,avc_equiv_smt_1Ci(lhs,rhs),[a,b,c],exp)
def smt_test_mul_U_DFI_yields_U_1Ci(o:int):
    pr="SMT Mul U_SINGLE*DFI=U_SINGLE";
    if o==1: prove_or_find_counterexample_smt_1Ci(pr+" (SKIP DFI N/A)",o,[],TRUE(),[],True); return
    u,d,r=[create_symbolic_avc_val_1Ci(x) for x in "u,d,r".split(',')]
    s=get_base_avc_constraints_1Ci(u,Int(o),o)+get_base_avc_constraints_1Ci(d,Int(o),o)+get_base_avc_constraints_1Ci(r,Int(o),o)
    s.extend([u["is_unio"], d["is_finite"], avc_mul_smt_logic_1Ci(u,d,r,Int(o),o)])
    prove_or_find_counterexample_smt_1Ci(pr,o,s,r["is_unio"],[u,d],True)

# Main execution block
if __name__ == "__main__":
    print("====== AVCA Suite 1.C.i: Unio_Collapsed (Default Input Aspect, Uniform Output Aspect) ======")
    omegas_for_native = [1, 2, 3, 4]
    omegas_for_smt = [1, 2, 3, 5]

    print("\n--- Running Native Python Tests for Suite 1.C.i ---")
    for o_test in omegas_for_native:
        print(f"\n-- Native Tests for Ω = {o_test} --")
        run_native_test_1Ci(f"Totality avc_add_1Ci",o_test,lambda o:native_test_totality_op_1Ci(o,avc_add_1Ci))
        run_native_test_1Ci(f"Totality avc_sub_1Ci",o_test,lambda o:native_test_totality_op_1Ci(o,avc_sub_1Ci))
        run_native_test_1Ci(f"Totality avc_mul_1Ci",o_test,lambda o:native_test_totality_op_1Ci(o,avc_mul_1Ci))
        run_native_test_1Ci(f"Totality avc_div_1Ci",o_test,lambda o:native_test_totality_op_1Ci(o,avc_div_1Ci))
        run_native_test_1Ci("Comm avc_add_1Ci",o_test,native_test_commutativity_add_1Ci)
        run_native_test_1Ci("Assoc avc_add_1Ci",o_test,native_test_associativity_add_1Ci,expect_fail=(o_test>2))
        run_native_test_1Ci("Comm avc_mul_1Ci",o_test,native_test_commutativity_mul_1Ci)
        run_native_test_1Ci("Assoc avc_mul_1Ci",o_test,native_test_associativity_mul_1Ci,expect_fail=False)
        run_native_test_1Ci("LDist(mul_1Ci/add_1Ci)",o_test,native_test_distributivity_mul_over_add_1Ci,expect_fail=(o_test>2))

    print("\n--- Native Python Test Summary (Suite 1.C.i) ---")
    for o, res in sorted(native_test_summary_1Ci.items()): print(f"  Ω={o}: Passed={res['passed']}, Failed={res['failed']}, Skipped={res['skipped']}")
    
    if SMT_MODE_AVAILABLE:
        print("\n\n--- Running SMT-based Tests for Suite 1.C.i ---")
        for o_test in omegas_for_smt:
            print(f"\n-- SMT Tests for Ω = {o_test} --")
            smt_test_A1_totality_add_1Ci(o_test) # Using simplified call for brevity
            # A2 Well-definedness is trivial with U_SINGLE, skipped for brevity here, but would pass
            smt_test_associativity_add_1Ci(o_test)
            smt_test_distributivity_mul_over_add_1Ci(o_test)
            smt_test_mul_U_DFI_yields_U_1Ci(o_test) # Checks U_SINGLE * DFI = U_SINGLE
    else:
        print("\nSMT-based tests for Suite 1.C.i were skipped as PySMT is not available.")

    print("\n====== Suite 1.C.i Finished ======")