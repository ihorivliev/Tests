import itertools
from typing import Literal, Union, Any, Tuple, List, Dict, Callable

# --- PySMT Imports ---
try:
    from pysmt.shortcuts import (Symbol, Int, BOOL, Equals, Not, And, Or, Implies, Iff,
                                 ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Minus, Times, Div, NotEquals,
                                 GT, GE, LT, LE, Ite) # Ite is now included
    from pysmt.typing import INT as SMT_INT_TYPE, BOOL as SMT_BOOL_TYPE
    from pysmt.fnode import FNode
    SMT_MODE_AVAILABLE = True
except ImportError:
    SMT_MODE_AVAILABLE = False
    print("CRITICAL ERROR: PySMT library not found. This script requires PySMT to run SMT tests.")
    # exit(1) # Optionally exit if SMT is mandatory for the script's purpose

# --- Configuration ---
SMT_SOLVER_NAME = "z3"

# --- SMT Harness Components for the "Best Combination" System ---
# These model the Python Unio class with 'zero' and 'areo' aspects
# ZERO_UNIO_OBJ_REPR: is_zero_aspect=T, is_areo_aspect=F, is_finite=F, val=0
# AREO_UNIO_OBJ_REPR: is_zero_aspect=F, is_areo_aspect=T, is_finite=F, val=Omega

smt_test_summary_BestCombo = {}
Omega_py_smt_BestCombo: int = 0

def create_symbolic_avc_val_bc(name_prefix: str) -> Dict[str, FNode]: # BC for Best Combo
    return {
        "is_zero_aspect": Symbol(f"{name_prefix}_is_Z", SMT_BOOL_TYPE),
        "is_areo_aspect": Symbol(f"{name_prefix}_is_A", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_F", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_v", SMT_INT_TYPE), # Stores 0 for ZU, Omega for AU, or DFI value
        "name": name_prefix
    }

def get_base_avc_constraints_bc(s: Dict[str, FNode], o_smt: FNode, o_py: int) -> List[FNode]:
    is_u = Or(s["is_zero_aspect"], s["is_areo_aspect"])
    c = [ Iff(is_u, Not(s["is_finite"])),
          Implies(s["is_zero_aspect"], Not(s["is_areo_aspect"])), # ZU and AU are mutually exclusive aspects
          Implies(s["is_finite"], And(s["val"] > Int(0), s["val"] < o_smt)),
          Implies(s["is_zero_aspect"], Equals(s["val"], Int(0))),
          Implies(s["is_areo_aspect"], Equals(s["val"], o_smt)) ]
    if o_py == 1: c.append(Not(s["is_finite"]))
    return c

def avc_equiv_smt_bc(s1: Dict[str, FNode], s2: Dict[str, FNode]) -> FNode:
    s1_is_u = Or(s1["is_zero_aspect"], s1["is_areo_aspect"])
    s2_is_u = Or(s2["is_zero_aspect"], s2["is_areo_aspect"])
    return Or(And(s1_is_u, s2_is_u), And(s1["is_finite"], s2["is_finite"], Equals(s1["val"], s2["val"])))

# --- SMT Logic Builders for the "Best Combination" ---

# ADDITION: avc_add_v1.1 logic (DFI overflow -> AREO_UNIO)
def avc_add_smt_logic_v11_bc(a: Dict[str,FNode], b: Dict[str,FNode], res: Dict[str,FNode], o_smt: FNode, o_py: int) -> FNode:
    a_is_u=Or(a["is_zero_aspect"],a["is_areo_aspect"]); b_is_u=Or(b["is_zero_aspect"],b["is_areo_aspect"])
    res_eq_a=And(Iff(res["is_finite"],a["is_finite"]),Iff(res["is_zero_aspect"],a["is_zero_aspect"]),Iff(res["is_areo_aspect"],a["is_areo_aspect"]),Equals(res["val"],a["val"]))
    res_eq_b=And(Iff(res["is_finite"],b["is_finite"]),Iff(res["is_zero_aspect"],b["is_zero_aspect"]),Iff(res["is_areo_aspect"],b["is_areo_aspect"]),Equals(res["val"],b["val"]))
    c1=Implies(a_is_u,res_eq_b); c2=Implies(And(a["is_finite"],b_is_u),res_eq_a)
    sval=Plus(a["val"],b["val"])
    res_dfi=And(res["is_finite"],Not(res["is_zero_aspect"]),Not(res["is_areo_aspect"]),Equals(res["val"],sval))
    res_areo=And(Not(res["is_finite"]),res["is_areo_aspect"],Not(res["is_zero_aspect"]),Equals(res["val"],o_smt))
    c3=Implies(And(a["is_finite"],b["is_finite"]),Ite(LT(sval,o_smt),res_dfi,res_areo))
    return And(c1,c2,c3)

# SUBTRACTION: avc_sub_v1.0 logic
def avc_sub_smt_logic_v10_bc(a: Dict[str,FNode], b: Dict[str,FNode], res: Dict[str,FNode], o_smt: FNode, o_py: int) -> FNode:
    b_is_u=Or(b["is_zero_aspect"],b["is_areo_aspect"])
    res_eq_a=And(Iff(res["is_finite"],a["is_finite"]),Iff(res["is_zero_aspect"],a["is_zero_aspect"]),Iff(res["is_areo_aspect"],a["is_areo_aspect"]),Equals(res["val"],a["val"]))
    res_areo=And(Not(res["is_finite"]),res["is_areo_aspect"],Not(res["is_zero_aspect"]),Equals(res["val"],o_smt))
    c1=Implies(b_is_u,res_eq_a)
    c2=Implies(And(Or(a["is_zero_aspect"],a["is_areo_aspect"]),b["is_finite"]),res_areo)
    dval=Minus(a["val"],b["val"])
    res_dfi=And(res["is_finite"],Not(res["is_zero_aspect"]),Not(res["is_areo_aspect"]),Equals(res["val"],dval))
    c3=Implies(And(a["is_finite"],b["is_finite"]),Ite(GT(a["val"],b["val"]),res_dfi,res_areo))
    return And(c1,c2,c3)

# MULTIPLICATION: avc_mul_v1.2 logic ("Areo dominates")
def avc_mul_smt_logic_v12_bc(a: Dict[str,FNode], b: Dict[str,FNode], res: Dict[str,FNode], o_smt: FNode, o_py: int) -> FNode:
    a_is_u=Or(a["is_zero_aspect"],a["is_areo_aspect"]); b_is_u=Or(b["is_zero_aspect"],b["is_areo_aspect"])
    a_is_areo=a["is_areo_aspect"]; b_is_areo=b["is_areo_aspect"]
    any_areo=Or(a_is_areo,b_is_areo)
    res_zero=And(Not(res["is_finite"]),res["is_zero_aspect"],Not(res["is_areo_aspect"]),Equals(res["val"],Int(0)))
    res_areo=And(Not(res["is_finite"]),res["is_areo_aspect"],Not(res["is_zero_aspect"]),Equals(res["val"],o_smt))
    unio_case=Ite(any_areo,res_areo,res_zero)
    pval=Times(a["val"],b["val"])
    res_dfi=And(res["is_finite"],Not(res["is_zero_aspect"]),Not(res["is_areo_aspect"]),Equals(res["val"],pval))
    dfi_case=Ite(And(pval>=Int(1),pval<o_smt),res_dfi,res_areo) # DFI overflow to AREO
    return Ite(Or(a_is_u,b_is_u),unio_case,dfi_case)

# DIVISION: avc_div_AltD_Balanced logic
def avc_div_smt_logic_AltD_bc(a: Dict[str,FNode], b: Dict[str,FNode], res: Dict[str,FNode], o_smt: FNode, o_py: int) -> FNode:
    res_zero=And(Not(res["is_finite"]),res["is_zero_aspect"],Not(res["is_areo_aspect"]),Equals(res["val"],Int(0)))
    res_areo=And(Not(res["is_finite"]),res["is_areo_aspect"],Not(res["is_zero_aspect"]),Equals(res["val"],o_smt))
    res_eq_a_aspect=Ite(a["is_zero_aspect"], res_zero, res_areo) # If a is Unio, result is a (object)

    # DFI/DFI logic part
    q_derived = Div(a["val"], b["val"])
    r_derived = (a["val"] - (q_derived * b["val"]))
    q_is_valid_dfi = And(Equals(r_derived, Int(0)), q_derived >= Int(1), q_derived < o_smt)
    res_is_FP_quotient = And(res["is_finite"], Not(res["is_zero_aspect"]),Not(res["is_areo_aspect"]),Equals(res["val"],q_derived))
    dfi_dfi_logic = Ite(q_is_valid_dfi, res_is_FP_quotient, res_areo) # Problematic DFI/DFI -> AREO

    # AltD structure:
    # 1. If b is DFI:
    #    a. If a is ZU -> ZU
    #    b. If a is AU -> AU
    #    c. If a is DFI -> _dfi_div_logic
    # 2. Else (b is Unio):
    #    a. If a is DFI -> AU
    #    b. Else (a is Unio - U/U case):
    #       i.  If b is AU -> AU
    #       ii. Else (b is ZU) -> preserve a's aspect

    rule1 = Implies(b["is_finite"], # Divisor b is DFI
                    Ite(a["is_zero_aspect"], res_zero,
                    Ite(a["is_areo_aspect"], res_areo,
                        dfi_dfi_logic # a is DFI
                    )))
    
    rule2_DFI_div_Unio = Implies(And(a["is_finite"], Or(b["is_zero_aspect"],b["is_areo_aspect"])), # a is DFI, b is Unio
                                 res_areo)
    
    rule2_Unio_div_Unio = Implies(And(Or(a["is_zero_aspect"],a["is_areo_aspect"]), Or(b["is_zero_aspect"],b["is_areo_aspect"])), # a is Unio, b is Unio
                                  Ite(b["is_areo_aspect"], # If divisor is AREO
                                      res_areo,
                                      res_eq_a_aspect # Else (divisor is ZERO), result is 'a' (preserves dividend aspect)
                                  ))
    return And(rule1, rule2_DFI_div_Unio, rule2_Unio_div_Unio)


# --- SMT Test Runner ---
def prove_or_find_counterexample_smt_bc(
    property_name: str, omega_py_val: int, setup_formulas: List[FNode],
    property_to_verify: FNode, inputs_reprs: List[Dict[str, Any]],
    expect_property_to_hold: bool, is_existential: bool = False):
    global smt_test_summary_BestCombo, Omega_py_smt_BestCombo
    Omega_py_smt_BestCombo = omega_py_val
    if not SMT_MODE_AVAILABLE:
        print(f"SKIPPED (SMT Mode Unavailable) for {property_name} Ω={omega_py_val}")
        if omega_py_val not in smt_test_summary_BestCombo: smt_test_summary_BestCombo[omega_py_val]={"p":0,"f":0,"s":0}
        smt_test_summary_BestCombo[omega_py_val]["s"]+=1; return
    if omega_py_val not in smt_test_summary_BestCombo: smt_test_summary_BestCombo[omega_py_val]={"p":0,"f":0,"s":0}
    print(f"  SMT Test (BestCombo): '{property_name}' for Ω={omega_py_val} (Expect: {'Hold/Exist' if expect_property_to_hold else 'Fail/Not Exist'})", end=" ... ")
    holds_obs=False; cex_str=None
    try:
        with Solver(name=SMT_SOLVER_NAME,logic="LIA") as s: # Changed to LIA for Times/Div
            for f_setup in setup_formulas:s.add_assertion(f_setup)
            formula_to_check=Not(property_to_verify) if not is_existential else property_to_verify
            if s.solve([formula_to_check]):
                if is_existential:holds_obs=True
                else:holds_obs=False
                m=s.get_model();ce_p=[]
                for r_d in inputs_reprs:
                    nm=r_d['name'];iz=m.get_value(r_d['is_zero_aspect']).is_true();ia=m.get_value(r_d['is_areo_aspect']).is_true()
                    isf=m.get_value(r_d['is_finite']).is_true();v=m.get_value(r_d['val'])
                    st="ERR";
                    if isf:st=f"Fp({v})"
                    elif iz:st="ZU_obj"
                    elif ia:st="AU_obj"
                    ce_p.append(f"{nm}={st}")
                cex_str="; ".join(ce_p)
            else: 
                if is_existential:holds_obs=False
                else:holds_obs=True
        succ=(holds_obs == expect_property_to_hold)
        if succ: print("PASS"); smt_test_summary_BestCombo[omega_py_val]["p"]+=1
        else: print(f"FAIL (Obs:{'H/E'if holds_obs else'F/NE'})"); smt_test_summary_BestCombo[omega_py_val]["f"]+=1
        if cex_str and ((is_existential and holds_obs and expect_property_to_hold) or \
                        (not is_existential and not holds_obs and not expect_property_to_hold)):
            print(f"    {'Wit' if is_existential else 'Cex'} (as exp): {cex_str}")
        elif cex_str and not succ:
            lbl="UnexpWit" if is_existential else "Cex(unexp fail)"
            if not holds_obs and expect_property_to_hold and is_existential: lbl="WitNOTFound(exp)"
            elif holds_obs and not expect_property_to_hold and not is_existential:lbl="NoCexFound(unexp hold)"
            print(f"    {lbl}: {cex_str}")
        elif not succ and not cex_str:
            if not holds_obs and expect_property_to_hold and is_existential: print("    WitNOTFound(exp)")
            elif holds_obs and not expect_property_to_hold and not is_existential: print("    NoCexFound(unexp hold)")
    except Exception as e: print(f"ERROR({type(e).__name__}:{e})"); smt_test_summary_BestCombo[omega_py_val]["f"]+=1


# --- Selected SMT Property Test Functions (Illustrative Subset) ---
# For a truly "maximal" script, many more of the 50-60+ tests per Omega from the harness would be here.
# This is a representative core set.

def run_smt_foundational_integrity_suite_bc(o_py: int):
    o_smt = Int(o_py)
    ops = { "Add": avc_add_smt_logic_v11_bc, "Sub": avc_sub_smt_logic_v10_bc, 
            "Mul": avc_mul_smt_logic_v12_bc, "Div": avc_div_smt_logic_AltD_bc }
    for op_name, op_logic in ops.items():
        # A.1 Totality
        a,b,r = [create_symbolic_avc_val_bc(p) for p in [f"a_tot{op_name[0]}", f"b_tot{op_name[0]}", f"r_tot{op_name[0]}"]]
        s = get_base_avc_constraints_bc(a,o_smt,o_py) + get_base_avc_constraints_bc(b,o_smt,o_py) + \
            get_base_avc_constraints_bc(r,o_smt,o_py) + [op_logic(a,b,r,o_smt,o_py)]
        prove_or_find_counterexample_smt_bc(f"A.1 Totality {op_name}", o_py, s, TRUE(), [a,b,r], True)
        # A.2 Well-Definedness
        a1,a2,b1,b2,r1,r2 = [create_symbolic_avc_val_bc(p) for p in [f"a1_wd{op_name[0]}",f"a2_wd{op_name[0]}",f"b1_wd{op_name[0]}",f"b2_wd{op_name[0]}",f"r1_wd{op_name[0]}",f"r2_wd{op_name[0]}"]]
        s_wd = get_base_avc_constraints_bc(a1,o_smt,o_py)+get_base_avc_constraints_bc(a2,o_smt,o_py)+get_base_avc_constraints_bc(b1,o_smt,o_py)+get_base_avc_constraints_bc(b2,o_smt,o_py)+get_base_avc_constraints_bc(r1,o_smt,o_py)+get_base_avc_constraints_bc(r2,o_smt,o_py)
        s_wd.extend([op_logic(a1,b1,r1,o_smt,o_py), op_logic(a2,b2,r2,o_smt,o_py)])
        prem = And(avc_equiv_smt_bc(a1,a2), avc_equiv_smt_bc(b1,b2))
        prove_or_find_counterexample_smt_bc(f"A.2 Well-Definedness {op_name}", o_py, s_wd, Implies(prem, avc_equiv_smt_bc(r1,r2)), [a1,a2,b1,b2], True)

def run_smt_additive_laws_suite_bc(o_py: int):
    o_smt = Int(o_py)
    a,b,c,r1,r2 = [create_symbolic_avc_val_bc(p) for p in ["a","b","c","r1","r2"]]
    s_comm = get_base_avc_constraints_bc(a,o_smt,o_py)+get_base_avc_constraints_bc(b,o_smt,o_py)+get_base_avc_constraints_bc(r1,o_smt,o_py)+get_base_avc_constraints_bc(r2,o_smt,o_py)
    s_comm.extend([avc_add_smt_logic_v11_bc(a,b,r1,o_smt,o_py), avc_add_smt_logic_v11_bc(b,a,r2,o_smt,o_py)])
    prove_or_find_counterexample_smt_bc("B.Add Commutativity", o_py, s_comm, avc_equiv_smt_bc(r1,r2), [a,b], True)

    exp_assoc = (o_py <= 2)
    ab,lhs,bc,rhs = [create_symbolic_avc_val_bc(p) for p in ["ab","lhs","bc","rhs"]]
    s_assoc=get_base_avc_constraints_bc(a,o_smt,o_py)+get_base_avc_constraints_bc(b,o_smt,o_py)+get_base_avc_constraints_bc(c,o_smt,o_py)+get_base_avc_constraints_bc(ab,o_smt,o_py)+get_base_avc_constraints_bc(lhs,o_smt,o_py)+get_base_avc_constraints_bc(bc,o_smt,o_py)+get_base_avc_constraints_bc(rhs,o_smt,o_py)
    s_assoc.extend([avc_add_smt_logic_v11_bc(a,b,ab,o_smt,o_py),avc_add_smt_logic_v11_bc(ab,c,lhs,o_smt,o_py),avc_add_smt_logic_v11_bc(b,c,bc,o_smt,o_py),avc_add_smt_logic_v11_bc(a,bc,rhs,o_smt,o_py)])
    prove_or_find_counterexample_smt_bc("B.Add Associativity",o_py,s_assoc,avc_equiv_smt_bc(lhs,rhs),[a,b,c],exp_assoc)

def run_smt_multiplicative_laws_suite_bc(o_py: int): # Similar structure for Mul
    o_smt = Int(o_py)
    a,b,c,r1,r2 = [create_symbolic_avc_val_bc(p) for p in ["a","b","c","r1","r2"]]
    s_comm = get_base_avc_constraints_bc(a,o_smt,o_py)+get_base_avc_constraints_bc(b,o_smt,o_py)+get_base_avc_constraints_bc(r1,o_smt,o_py)+get_base_avc_constraints_bc(r2,o_smt,o_py)
    s_comm.extend([avc_mul_smt_logic_v12_bc(a,b,r1,o_smt,o_py), avc_mul_smt_logic_v12_bc(b,a,r2,o_smt,o_py)])
    prove_or_find_counterexample_smt_bc("C.Mul Commutativity", o_py, s_comm, avc_equiv_smt_bc(r1,r2), [a,b], True)

    exp_assoc = True # Mul is always associative
    ab,lhs,bc,rhs = [create_symbolic_avc_val_bc(p) for p in ["ab","lhs","bc","rhs"]]
    s_assoc=get_base_avc_constraints_bc(a,o_smt,o_py)+get_base_avc_constraints_bc(b,o_smt,o_py)+get_base_avc_constraints_bc(c,o_smt,o_py)+get_base_avc_constraints_bc(ab,o_smt,o_py)+get_base_avc_constraints_bc(lhs,o_smt,o_py)+get_base_avc_constraints_bc(bc,o_smt,o_py)+get_base_avc_constraints_bc(rhs,o_smt,o_py)
    s_assoc.extend([avc_mul_smt_logic_v12_bc(a,b,ab,o_smt,o_py),avc_mul_smt_logic_v12_bc(ab,c,lhs,o_smt,o_py),avc_mul_smt_logic_v12_bc(b,c,bc,o_smt,o_py),avc_mul_smt_logic_v12_bc(a,bc,rhs,o_smt,o_py)])
    prove_or_find_counterexample_smt_bc("C.Mul Associativity",o_py,s_assoc,avc_equiv_smt_bc(lhs,rhs),[a,b,c],exp_assoc)

def run_smt_distributivity_suite_bc(o_py: int):
    o_smt = Int(o_py)
    exp_distrib = (o_py <= 2)
    a,b,c = [create_symbolic_avc_val_bc(x) for x in ['a','b','c']]
    bpc,lhs,ab,ac,rhs = [create_symbolic_avc_val_bc(x) for x in ['bpc','lhs','ab','ac','rhs']]
    s = get_base_avc_constraints_bc(a,o_smt,o_py)+get_base_avc_constraints_bc(b,o_smt,o_py)+get_base_avc_constraints_bc(c,o_smt,o_py)+ \
        get_base_avc_constraints_bc(bpc,o_smt,o_py)+get_base_avc_constraints_bc(lhs,o_smt,o_py)+get_base_avc_constraints_bc(ab,o_smt,o_py)+ \
        get_base_avc_constraints_bc(ac,o_smt,o_py)+get_base_avc_constraints_bc(rhs,o_smt,o_py)
    s.extend([avc_add_smt_logic_v11_bc(b,c,bpc,o_smt,o_py), avc_mul_smt_logic_v12_bc(a,bpc,lhs,o_smt,o_py), \
              avc_mul_smt_logic_v12_bc(a,b,ab,o_smt,o_py), avc_mul_smt_logic_v12_bc(a,c,ac,o_smt,o_py), \
              avc_add_smt_logic_v11_bc(ab,ac,rhs,o_smt,o_py) ])
    prove_or_find_counterexample_smt_bc("E.Left Distributivity (Mul over Add)", o_py,s,avc_equiv_smt_bc(lhs,rhs),[a,b,c],exp_distrib)

def run_smt_division_AltD_specifics_bc(o_py: int):
    o_smt = Int(o_py)
    # Test ZU/ZU = ZU for AltD
    zu_sym = create_symbolic_avc_val_bc("zu_arg")
    res_div = create_symbolic_avc_val_bc("res_div_zz")
    setup_zz = get_base_avc_constraints_bc(zu_sym, o_smt, o_py) + get_base_avc_constraints_bc(res_div, o_smt, o_py)
    setup_zz.extend([
        zu_sym["is_zero_aspect"], # Ensure zu_sym is indeed ZU object representation
        avc_div_smt_logic_AltD_bc(zu_sym, zu_sym, res_div, o_smt, o_py)
    ])
    # Property: result must be ZU object
    prop_zz = res_div["is_zero_aspect"]
    prove_or_find_counterexample_smt_bc("G.DivAltD: ZU/ZU = ZU_obj", o_py, setup_zz, prop_zz, [zu_sym, res_div], True if o_py > 0 else False) # Trivial for o_py=0

    # Test ZU/DFI = ZU for AltD
    if o_py > 1: # Need DFI
        zu_sym2 = create_symbolic_avc_val_bc("zu_arg2")
        dfi_sym = create_symbolic_avc_val_bc("dfi_arg")
        res_div2 = create_symbolic_avc_val_bc("res_div_zdfi")
        setup_zdfi = get_base_avc_constraints_bc(zu_sym2, o_smt, o_py) + \
                     get_base_avc_constraints_bc(dfi_sym, o_smt, o_py) + \
                     get_base_avc_constraints_bc(res_div2, o_smt, o_py)
        setup_zdfi.extend([
            zu_sym2["is_zero_aspect"],
            dfi_sym["is_finite"],
            avc_div_smt_logic_AltD_bc(zu_sym2, dfi_sym, res_div2, o_smt, o_py)
        ])
        prop_zdfi = res_div2["is_zero_aspect"]
        prove_or_find_counterexample_smt_bc("G.DivAltD: ZU/DFI = ZU_obj", o_py, setup_zdfi, prop_zdfi, [zu_sym2, dfi_sym], True)

        # Test RT: (ZU/DFI) * DFI = ZU
        q_rt = create_symbolic_avc_val_bc("q_rt")
        lhs_rt = create_symbolic_avc_val_bc("lhs_rt")
        setup_rt_zdfi = get_base_avc_constraints_bc(zu_sym2, o_smt, o_py) + \
                        get_base_avc_constraints_bc(dfi_sym, o_smt, o_py) + \
                        get_base_avc_constraints_bc(q_rt, o_smt, o_py) + \
                        get_base_avc_constraints_bc(lhs_rt, o_smt, o_py)
        setup_rt_zdfi.extend([
            zu_sym2["is_zero_aspect"], dfi_sym["is_finite"],
            avc_div_smt_logic_AltD_bc(zu_sym2, dfi_sym, q_rt, o_smt, o_py),      # q = ZU/DFI (should be ZU)
            avc_mul_smt_logic_v12_bc(q_rt, dfi_sym, lhs_rt, o_smt, o_py) # lhs = q*DFI (ZU*DFI should be ZU)
        ])
        prop_rt_zdfi = avc_equiv_smt_bc(lhs_rt, zu_sym2) # Check if LHS == original ZU
        prove_or_find_counterexample_smt_bc("G.DivAltD RT: (ZU/DFI)*DFI=ZU", o_py, setup_rt_zdfi, prop_rt_zdfi, [zu_sym2, dfi_sym], True)


# --- Main Execution Block ---
if __name__ == "__main__":
    print("====== AVCA Best Combination SMT Stress Test ======")
    print(f"      (Using Add_v1.1, Sub_v1.0, Mul_v1.2, Div_AltD_Balanced)")
    
    if not SMT_MODE_AVAILABLE:
        print("\nCRITICAL: PySMT library not found or failed to import. SMT tests cannot run.")
        print("Please install PySMT and an SMT solver (e.g., Z3: pip install pysmt z3-solver)")
    else:
        omegas_to_test_smt = [1, 2, 3, 5] # Representative set
        for omega_val_test in omegas_to_test_smt:
            Omega_py_smt_BestCombo = omega_val_test # Set for base constraints
            print(f"\n--- SMT Tests for Ω = {omega_val_test} ---")
            run_smt_foundational_integrity_suite_bc(omega_val_test)
            run_smt_additive_laws_suite_bc(omega_val_test)
            run_smt_multiplicative_laws_suite_bc(omega_val_test)
            run_smt_distributivity_suite_bc(omega_val_test)
            run_smt_division_AltD_specifics_bc(omega_val_test) # Key AltD checks

        print("\n\n--- Overall SMT Test Summary (Best Combination) ---")
        for suite_key, results in sorted(smt_test_summary_BestCombo.items()):
            print(f"  Ω={suite_key}: Passed={results['p']}, Failed={results['f']}, Skipped={results['s']}")
        
        total_passed = sum(r['p'] for r in smt_test_summary_BestCombo.values())
        total_failed = sum(r['f'] for r in smt_test_summary_BestCombo.values())
        total_skipped = sum(r['s'] for r in smt_test_summary_BestCombo.values())

        if total_failed == 0 and total_passed > 0:
            print(f"\n✅✅✅ All {total_passed} executed SMT tests for the Best Combination PASSED (or matched expectations)! ✅✅✅")
        elif total_passed == 0 and total_failed == 0 and total_skipped > 0:
            print(f"\n⚠️ All {total_skipped} SMT tests were SKIPPED (likely due to SMT solver not being found).")
        else:
            print(f"\n❌❌❌ WARNING: {total_failed} SMT tests FAILED for the Best Combination! Review output. ❌❌❌")
            print(f"    (Passed: {total_passed}, Skipped: {total_skipped})")

    print("\n====== Best Combination SMT Stress Test Finished ======")