# Script D.1: Symbolic Search for an Associativity-Restoring 1-bit Tag Rule (Ω=3) - Corrected
# Red-Team Audit: Claim 6 (related to R1) "Single-bit tag can’t fix associativity."
# Falsification Strategy: encode ⊕_tag as symbolic function of carry bits in SMT
# for Ω = 3; assert associativity; ask for SAT.

from pysmt.shortcuts import (Symbol, Int, BOOL, Function, Equals, Not, And, Or, Implies, Iff,
                             ExactlyOne, Solver, TRUE, FALSE, FunctionType, Plus, Ite, ForAll, Exists)
from pysmt.typing import INT as SMT_INT_TYPE
from pysmt.typing import BOOL as SMT_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Literal
import itertools

# --- Global Python Omega for SMT Context ---
_Omega_py_sD1: int = 0

# --- Symbolic Core AVCA Definitions (adapted from R5.2) ---
def create_symbolic_avc_val_sD1(name_prefix: str) -> Dict[str, Any]:
    return {
        "is_zero": Symbol(f"{name_prefix}_is_zero_sD1", SMT_BOOL_TYPE),
        "is_areo": Symbol(f"{name_prefix}_is_areo_sD1", SMT_BOOL_TYPE),
        "is_finite": Symbol(f"{name_prefix}_is_finite_sD1", SMT_BOOL_TYPE),
        "val": Symbol(f"{name_prefix}_val_sD1", SMT_INT_TYPE),
        "name": name_prefix
    }

def get_base_avc_constraints_sD1(avc_repr: Dict[str, FNode], omega_smt_node: FNode) -> List[FNode]:
    constraints = [
        ExactlyOne(avc_repr["is_zero"], avc_repr["is_areo"], avc_repr["is_finite"]),
        Implies(avc_repr["is_finite"], And(avc_repr["val"] > Int(0), avc_repr["val"] < omega_smt_node)),
        Implies(avc_repr["is_zero"], Equals(avc_repr["val"], Int(0))), 
        Implies(avc_repr["is_areo"], Equals(avc_repr["val"], omega_smt_node)) 
    ]
    global _Omega_py_sD1
    if _Omega_py_sD1 == 1: 
        constraints.append(Not(avc_repr["is_finite"])) 
    return constraints

def avc_add_smt_logic_sD1(a_val_repr: Dict[str, FNode], b_val_repr: Dict[str, FNode],
                           res_val_repr: Dict[str, FNode], omega_smt_node: FNode) -> FNode:
    a_is_unio = Or(a_val_repr["is_zero"], a_val_repr["is_areo"])
    b_is_unio = Or(b_val_repr["is_zero"], b_val_repr["is_areo"])
    res_becomes_a_state = And(Iff(res_val_repr["is_zero"], a_val_repr["is_zero"]),
                              Iff(res_val_repr["is_areo"], a_val_repr["is_areo"]),
                              Iff(res_val_repr["is_finite"], a_val_repr["is_finite"]),
                              Equals(res_val_repr["val"], a_val_repr["val"]))
    res_becomes_b_state = And(Iff(res_val_repr["is_zero"], b_val_repr["is_zero"]),
                              Iff(res_val_repr["is_areo"], b_val_repr["is_areo"]),
                              Iff(res_val_repr["is_finite"], b_val_repr["is_finite"]),
                              Equals(res_val_repr["val"], b_val_repr["val"]))
    case1_a_is_unio = Implies(a_is_unio, res_becomes_b_state)
    case2_b_is_unio_a_is_dfi = Implies(And(Not(a_is_unio), b_is_unio), res_becomes_a_state)
    cond_both_are_dfi = And(a_val_repr["is_finite"], b_val_repr["is_finite"])
    symbolic_sum_val = Plus(a_val_repr["val"], b_val_repr["val"])
    res_is_dfi_sum_state = And(Not(res_val_repr["is_zero"]), Not(res_val_repr["is_areo"]), 
                               res_val_repr["is_finite"], Equals(res_val_repr["val"], symbolic_sum_val))
    res_is_areo_unio_state = And(Not(res_val_repr["is_zero"]), res_val_repr["is_areo"], 
                                 Not(res_val_repr["is_finite"]), Equals(res_val_repr["val"], omega_smt_node))
    case3_dfi_dfi_logic = Implies(cond_both_are_dfi,
        Ite(symbolic_sum_val < omega_smt_node, res_is_dfi_sum_state, res_is_areo_unio_state))
    return And(case1_a_is_unio, case2_b_is_unio_a_is_dfi, case3_dfi_dfi_logic)

# --- Symbolic Tagged Addition ---
tag_params_global_sD1: Dict[str, FNode] = {f"p{i:03b}".replace("0b",""): Symbol(f"p{i:03b}".replace("0b","")+"_sD1param", SMT_BOOL_TYPE) for i in range(8)}

def avc_add_symbolic_tag(
    sa_val_repr: Dict[str, FNode], sa_tag: FNode, 
    sb_val_repr: Dict[str, FNode], sb_tag: FNode,
    # These are the symbolic representations for the *result* of this specific add_symbolic_tag call
    res_of_this_op_val_repr: Dict[str, FNode], 
    omega_smt_node: FNode,
    tag_params: Dict[str, FNode] 
) -> Tuple[FNode, FNode]: # Returns (value_definition_formula, result_tag_formula_expr)
    
    # 1. Define the resulting AVCA value part (v_res) and its properties
    # value_definition_formula defines how res_of_this_op_val_repr gets its value fields
    value_definition_formula = avc_add_smt_logic_sD1(sa_val_repr, sb_val_repr, res_of_this_op_val_repr, omega_smt_node)
    
    # 2. Define value_overflow_occurred (vo) for tag logic
    # True if both inputs sa_val_repr, sb_val_repr were DFI AND their sum (res_of_this_op_val_repr) is Unio.
    vo = And(sa_val_repr["is_finite"], 
             sb_val_repr["is_finite"], 
             Or(res_of_this_op_val_repr["is_zero"], res_of_this_op_val_repr["is_areo"]))

    # 3. Define result_tag_formula_expr (h_res_expr) using the 8 parameters
    h_res_expr = Ite(And(Not(sa_tag), Not(sb_tag), Not(vo)), tag_params["p000"],
                 Ite(And(Not(sa_tag), Not(sb_tag), vo),      tag_params["p001"],
                 Ite(And(Not(sa_tag), sb_tag,      Not(vo)), tag_params["p010"],
                 Ite(And(Not(sa_tag), sb_tag,      vo),      tag_params["p011"],
                 Ite(And(sa_tag,      Not(sb_tag), Not(vo)), tag_params["p100"],
                 Ite(And(sa_tag,      Not(sb_tag), vo),      tag_params["p101"],
                 Ite(And(sa_tag,      sb_tag,      Not(vo)), tag_params["p110"],
                                                            tag_params["p111"] 
                 )))))))
            
    return value_definition_formula, h_res_expr

# --- Main SMT Test Function ---
def find_associativity_restoring_tag_rule_smt(omega_val_py: int):
    global _Omega_py_sD1
    _Omega_py_sD1 = omega_val_py
    
    print(f"\n--- Script D.1: Symbolic Tag Rule Search for Ω = {omega_val_py} ---")
    print(f"Searching for tag parameters p000-p111 that make tagged addition associative.")

    omega_smt_node = Int(omega_val_py)
    tag_params: Dict[str, FNode] = {name: Symbol(name+"_param_exist", SMT_BOOL_TYPE) for name in tag_params_global_sD1.keys()}

    # Symbolic representations for three generic tagged AVCA values for ForAll
    sa_val = create_symbolic_avc_val_sD1("sa_v_fa") # _fa for ForAll
    sa_tag = Symbol("sa_h_fa", SMT_BOOL_TYPE)
    sb_val = create_symbolic_avc_val_sD1("sb_v_fa")
    sb_tag = Symbol("sb_h_fa", SMT_BOOL_TYPE)
    sc_val = create_symbolic_avc_val_sD1("sc_v_fa")
    sc_tag = Symbol("sc_h_fa", SMT_BOOL_TYPE)

    # Intermediate results for LHS: (sa ADD sb) ADD sc
    res_ab_val = create_symbolic_avc_val_sD1("res_ab_v_fa")
    res_ab_tag_sym = Symbol("res_ab_h_sym_fa", SMT_BOOL_TYPE) # Symbolic tag for intermediate result
    lhs_val = create_symbolic_avc_val_sD1("lhs_v_fa")
    lhs_tag_sym = Symbol("lhs_h_sym_fa", SMT_BOOL_TYPE)    # Symbolic tag for final LHS result

    # Intermediate results for RHS: sa ADD (sb ADD sc)
    res_bc_val = create_symbolic_avc_val_sD1("res_bc_v_fa")
    res_bc_tag_sym = Symbol("res_bc_h_sym_fa", SMT_BOOL_TYPE) # Symbolic tag for intermediate result
    rhs_val = create_symbolic_avc_val_sD1("rhs_v_fa")
    rhs_tag_sym = Symbol("rhs_h_sym_fa", SMT_BOOL_TYPE)    # Symbolic tag for final RHS result

    # Define the operations and get the defining formulas for values and tag expressions
    val_def_ab_formula, tag_expr_ab = avc_add_symbolic_tag(sa_val, sa_tag, sb_val, sb_tag, res_ab_val, omega_smt_node, tag_params)
    val_def_lhs_formula, tag_expr_lhs = avc_add_symbolic_tag(res_ab_val, res_ab_tag_sym, sc_val, sc_tag, lhs_val, omega_smt_node, tag_params)
    
    val_def_bc_formula, tag_expr_bc = avc_add_symbolic_tag(sb_val, sb_tag, sc_val, sc_tag, res_bc_val, omega_smt_node, tag_params)
    val_def_rhs_formula, tag_expr_rhs = avc_add_symbolic_tag(sa_val, sa_tag, res_bc_val, res_bc_tag_sym, rhs_val, omega_smt_node, tag_params)

    # Associativity: value parts must be algebraically equivalent AND tag parts must be equal
    val_lhs_is_unio = Or(lhs_val["is_zero"], lhs_val["is_areo"])
    val_rhs_is_unio = Or(rhs_val["is_zero"], rhs_val["is_areo"])
    values_are_algebraically_equal = Ite(
        And(val_lhs_is_unio, val_rhs_is_unio), TRUE(),
        Ite(And(lhs_val["is_finite"], rhs_val["is_finite"]), Equals(lhs_val["val"], rhs_val["val"]), FALSE())
    )
    tags_are_equal = Iff(lhs_tag_sym, rhs_tag_sym) # Compare the symbolic tags of final LHS and RHS

    associativity_property = And(values_are_algebraically_equal, tags_are_equal)
    
    # Premise: defines how intermediate results and their tags are computed
    premise_definitions = And(
        val_def_ab_formula, Iff(res_ab_tag_sym, tag_expr_ab),   # Corrected: Iff for Boolean assignment
        val_def_lhs_formula, Iff(lhs_tag_sym, tag_expr_lhs),    # Corrected: Iff for Boolean assignment
        val_def_bc_formula, Iff(res_bc_tag_sym, tag_expr_bc),   # Corrected: Iff for Boolean assignment
        val_def_rhs_formula, Iff(rhs_tag_sym, tag_expr_rhs)     # Corrected: Iff for Boolean assignment
    )
    
    associativity_holds_formula = Implies(premise_definitions, associativity_property)

    # Quantified variables for ForAll
    # AVCA value representations are dicts, their components are SMT FNodes
    q_vars = []
    for val_repr in [sa_val, sb_val, sc_val, res_ab_val, lhs_val, res_bc_val, rhs_val]:
        q_vars.extend([val_repr["is_zero"], val_repr["is_areo"], val_repr["is_finite"], val_repr["val"]])
    q_vars.extend([sa_tag, sb_tag, sc_tag, res_ab_tag_sym, lhs_tag_sym, res_bc_tag_sym, rhs_tag_sym])
    
    # Base constraints for input symbolic AVCA values sa_val, sb_val, sc_val
    # and for all intermediate and final AVCA value representations.
    all_base_constraints_formula = And(
        And(get_base_avc_constraints_sD1(sa_val, omega_smt_node)),
        And(get_base_avc_constraints_sD1(sb_val, omega_smt_node)),
        And(get_base_avc_constraints_sD1(sc_val, omega_smt_node)),
        And(get_base_avc_constraints_sD1(res_ab_val, omega_smt_node)), # Constraints for intermediate results
        And(get_base_avc_constraints_sD1(lhs_val, omega_smt_node)),
        And(get_base_avc_constraints_sD1(res_bc_val, omega_smt_node)),
        And(get_base_avc_constraints_sD1(rhs_val, omega_smt_node))
    )
    
    constrained_associativity = Implies(all_base_constraints_formula, associativity_holds_formula)
    
    # ForAll sa,sb,sc (properly defined AVCA values with tags), does assoc hold?
    # The parameters p000...p111 are free variables here; Z3 tries to find a model for them.
    final_smt_query = ForAll(q_vars, constrained_associativity)

    print("\nSolving with Z3 (this might take some time due to ForAll)...")
    # For solvers that don't directly support ForAll with this combination of theories,
    # this might be slow or return unknown. Z3 is powerful, though.
    with Solver(name="z3", solver_options={'timeout': 60000}) as s: # Added a timeout (60 seconds)
        # solver_options={'smt.mbqi': 'true'} # Example option for quantifiers, might help
        s.add_assertion(final_smt_query)
        
        try:
            result = s.solve()
            if result:
                print("Status: SAT")
                print("  This is UNEXPECTED (but would be a major finding!).")
                print("  A 1-bit tag propagation rule (defined by p000-p111) WAS FOUND that makes")
                print(f"  AVCA ⊕_v1.1 associative for Ω={omega_val_py} on tagged states.")
                model = s.get_model()
                print("  Model for tag parameters (p_ha_hb_vo):")
                for p_name_key in sorted(tag_params.keys()): # Iterate over original keys
                    p_symbol = tag_params[p_name_key]
                    print(f"    {p_symbol.symbol_name()} = {model.get_value(p_symbol)}")
            else:
                print("Status: UNSAT")
                print("  This is EXPECTED (as per math LLM).")
                print("  No 1-bit tag propagation rule (within the 256 parameterized possibilities defined by p000-p111)")
                print(f"  can make AVCA ⊕_v1.1 associative for Ω={omega_val_py} on tagged states.")

        except Exception as e:
            print(f"SMT Solver Error or Timeout: {e}")
            print("  This could be due to the complexity of the ForAll quantification or solver limitations.")
            print("  The math LLM suggested Z3 handles this quickly in prior tests for UNSAT.")
            print("  If it's a timeout, the problem might be too complex for quick resolution.")
            print("  If it's another error, the SMT formula construction might need review.")

    print("-" * 70)

# --- Main Execution ---
if __name__ == "__main__":
    print("====== Script D.1: Symbolic Search for Associativity-Restoring 1-bit Tag Rule (Ω=3) - Corrected ======")
    
    # For Ω = 3, S3_tagged has 2*3 = 6 elements. ForAll is over 6^3 = 216 instances for (sa,sb,sc).
    find_associativity_restoring_tag_rule_smt(omega_val_py=3)

    print("\n====== D.1 Script Finished ======")