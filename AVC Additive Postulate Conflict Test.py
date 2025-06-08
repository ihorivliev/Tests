from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any

# --- Configuration ---
DEFAULT_OMEGA_MAX_VAL_NAT_PY = 7 
DEFAULT_OMEGA_MAX_VAL_NAT_SMT = Int(DEFAULT_OMEGA_MAX_VAL_NAT_PY)

# --- Phase 1: Foundational Definitions (Copied) ---
def create_intensity_representation(name_prefix: str) -> Dict[str, Any]:
    is_zero = Symbol(f"{name_prefix}_is_zero", solver_BOOL_TYPE)
    is_areo = Symbol(f"{name_prefix}_is_areo", solver_BOOL_TYPE)
    is_finite = Symbol(f"{name_prefix}_is_finite", solver_BOOL_TYPE)
    val = Symbol(f"{name_prefix}_val", solver_INT_TYPE)
    constraint_exactly_one_state = ExactlyOne(is_zero, is_areo, is_finite)
    constraint_pos_nat_if_finite = Implies(is_finite, val > Int(0))
    all_constraints = And(constraint_exactly_one_state, constraint_pos_nat_if_finite)
    return {
        "is_zero": is_zero, "is_areo": is_areo, "is_finite": is_finite,
        "val": val, "constraints": all_constraints, "name": name_prefix
    }

def avc_equiv(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any]) -> FNode:
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"])
    finite_finite_equal_val = And(i1_repr["is_finite"], 
                                  i2_repr["is_finite"], 
                                  Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

def make_intensity_constraints(repr_dict: Dict[str, Any], kind: str, 
                               symbolic_fp_val: FNode = None, 
                               current_omega_smt: FNode = None,
                               fixed_val: int = None) -> List[FNode]:
    assertions = []
    if kind == "ZS":
        assertions.extend([repr_dict["is_zero"], Not(repr_dict["is_areo"]), Not(repr_dict["is_finite"])])
    elif kind == "AS":
        assertions.extend([repr_dict["is_areo"], Not(repr_dict["is_zero"]), Not(repr_dict["is_finite"])])
    elif kind == "Fp_sym": 
        if symbolic_fp_val is None or current_omega_smt is None:
            raise ValueError("symbolic_fp_val and current_omega_smt must be provided for kind 'Fp_sym'")
        assertions.extend([
            repr_dict["is_finite"], Not(repr_dict["is_zero"]), Not(repr_dict["is_areo"]),
            Equals(repr_dict["val"], symbolic_fp_val),
            symbolic_fp_val > Int(0), 
            symbolic_fp_val < current_omega_smt 
        ])
    elif kind == "Fp_fixed": 
        if fixed_val is None:
            raise ValueError("fixed_val must be provided for kind 'Fp_fixed'")
        if not (fixed_val > 0):
            print(f"WARNING for {repr_dict['name']} (in make_intensity_constraints): Fp_fixed value {fixed_val} is not > 0.")
        assertions.extend([
            repr_dict["is_finite"], Not(repr_dict["is_zero"]), Not(repr_dict["is_areo"]),
            Equals(repr_dict["val"], Int(fixed_val))
        ])
    else:
        raise ValueError(f"Unknown kind for make_intensity_constraints: {kind}")
    return assertions

# --- Generic Operation Result Definition (Abstract) ---
def define_abstract_op_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                              result_name_prefix: str, op_name_for_symbol: str) -> Dict[str, Any]:
    """
    Creates a symbolic result representation for an abstract operation Op(i1, i2).
    The actual logic of Op is NOT defined here but will be constrained by postulates.
    """
    res_repr = create_intensity_representation(result_name_prefix)
    # We don't add a ["definition"] here because the definition IS what the postulates will constrain.
    # We will need to ensure res_repr["constraints"] is asserted by the caller.
    return res_repr


# --- Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Additive Postulate Conflict Test ======\n")
    
    s = Solver(name="z3") 
    current_omega = DEFAULT_OMEGA_MAX_VAL_NAT_SMT # Using default Omega for this conceptual test

    # --- Symbolic Intensities ---
    # U_rep1 will represent Unio via its ZeroState aspect
    U_rep1 = create_intensity_representation("U_rep1_ZS_Conflict")
    # U_rep2 will represent Unio via its AreoState aspect
    U_rep2 = create_intensity_representation("U_rep2_AS_Conflict")
    # X_DFI_sym will represent a generic DFI element
    X_DFI_sym = create_intensity_representation("X_DFI_Conflict")
    # Symbolic value for X_DFI_sym
    val_dfi_conflict = Symbol("val_dfi_conflict", solver_INT_TYPE)

    # --- Abstract Addition Operation Results ---
    # Result of U_rep1 + X_DFI_sym (conceptually ZS + X_DFI)
    OpAdd_U1_XDFI = define_abstract_op_result(U_rep1, X_DFI_sym, "OpAdd_U1_XDFI_Res", "Add")
    # Result of U_rep2 + X_DFI_sym (conceptually AS + X_DFI)
    OpAdd_U2_XDFI = define_abstract_op_result(U_rep2, X_DFI_sym, "OpAdd_U2_XDFI_Res", "Add")

    print(f"--- Testing Compatibility of Additive Postulates for Unio (Omega = {DEFAULT_OMEGA_MAX_VAL_NAT_PY}) ---")
    s.push()

    # --- Assert Foundational Constraints and Definitions ---
    # 1. U_rep1, U_rep2, X_DFI_sym, OpAdd_U1_XDFI, OpAdd_U2_XDFI must be valid intensities
    s.add_assertion(U_rep1["constraints"])
    s.add_assertion(U_rep2["constraints"])
    s.add_assertion(X_DFI_sym["constraints"])
    s.add_assertion(OpAdd_U1_XDFI["constraints"]) # The results of addition must also be valid intensities
    s.add_assertion(OpAdd_U2_XDFI["constraints"])

    # 2. Define U_rep1 as ZeroState, U_rep2 as AreoState, X_DFI_sym as Finite(val_dfi_conflict)
    for constraint in make_intensity_constraints(U_rep1, "ZS"): s.add_assertion(constraint)
    for constraint in make_intensity_constraints(U_rep2, "AS"): s.add_assertion(constraint)
    for constraint in make_intensity_constraints(X_DFI_sym, "Fp_sym", val_dfi_conflict, current_omega): s.add_assertion(constraint)
    
    # --- Assert Conceptual Postulates for a single addition operation OpAdd ---

    # Postulate 4.1 (Unio Integrity): U_rep1 (ZS) is avc_equiv to U_rep2 (AS)
    # This is inherently true by their setup and avc_equiv definition. We assert it for clarity.
    s.add_assertion(avc_equiv(U_rep1, U_rep2)) 
    print("  Asserted: Unio Integrity (P4.1): U_rep1 (as ZS) ~ U_rep2 (as AS)")

    # Postulate 6.1 (ZS-Emergence from Unio for addition): U_rep1 + X_DFI_sym ~ X_DFI_sym
    # This means OpAdd(U_rep1, X_DFI_sym) should be avc_equiv to X_DFI_sym
    s.add_assertion(avc_equiv(OpAdd_U1_XDFI, X_DFI_sym))
    print(f"  Asserted: ZS-Emergence (P6.1): OpAdd(U_rep1, X_DFI_sym) ~ X_DFI_sym ({X_DFI_sym['name']})")

    # Postulate 2.2.iii (AS-Absorption for addition): U_rep2 + X_DFI_sym ~ U_rep2 (i.e., ~ AS)
    # This means OpAdd(U_rep2, X_DFI_sym) should be avc_equiv to U_rep2
    s.add_assertion(avc_equiv(OpAdd_U2_XDFI, U_rep2))
    print(f"  Asserted: AS-Absorption (P2.2.iii): OpAdd(U_rep2, X_DFI_sym) ~ U_rep2 ({U_rep2['name']})")

    # Implied by P4.1 (Unio Integrity for Operations): 
    # If U_rep1 ~ U_rep2 and X_DFI_sym ~ X_DFI_sym (identity), 
    # then for OpAdd to be well-defined on AVC_Space, it must be that
    # OpAdd(U_rep1, X_DFI_sym) ~ OpAdd(U_rep2, X_DFI_sym).
    # This is the "respectfulness" property (_outputs_are_avc_equiv).
    s.add_assertion(avc_equiv(OpAdd_U1_XDFI, OpAdd_U2_XDFI))
    print("  Asserted: Well-Definedness of OpAdd: OpAdd(U_rep1,X_DFI_sym) ~ OpAdd(U_rep2,X_DFI_sym)")
    
    # --- Check for Satisfiability ---
    # If this set of assertions is SAT, it means all these postulates can coexist.
    # If UNSAT, it means they are contradictory.
    print("\n  Checking satisfiability of all asserted postulates simultaneously...")
    result = s.solve()

    if not result: # UNSAT
        print("\nResult: UNSAT. The conceptual postulates for Unio's addition are CONTRADICTORY. ✅")
        print("  This formally proves that a single binary addition operation cannot simultaneously:")
        print("    1. Be well-defined on Unio (where ZS ~ AS).")
        print("    2. Have Unio (via ZS-aspect) + DFI yield DFI (P6.1).")
        print("    3. Have Unio (via AS-aspect) + DFI yield Unio/AS (P2.2.iii).")
        print("  The conflict arises because this would imply DFI ~ AS, which is false.")
    else: # SAT
        print("\nResult: SAT. The conceptual postulates for Unio's addition appear compatible. ❌")
        print("  This is UNEXPECTED and suggests a potential flaw in the test setup or SMT reasoning,")
        print("  as previous tests indicated `strict_areo_add` (which tries to model P2.2.iii and P6.1)")
        print("  was not well-defined (did not respect avc_equiv).")
        print("  Model found by solver:")
        model_vars = [U_rep1, U_rep2, X_DFI_sym, OpAdd_U1_XDFI, OpAdd_U2_XDFI]
        for var_repr in model_vars:
            val_str = f"V={s.get_value(var_repr['val'])}" if var_repr['val'] in s.get_model() else "V=?"
            is_z_str = f"Z={s.get_value(var_repr['is_zero'])}" if var_repr['is_zero'] in s.get_model() else "Z=?"
            is_a_str = f"A={s.get_value(var_repr['is_areo'])}" if var_repr['is_areo'] in s.get_model() else "A=?"
            is_f_str = f"F={s.get_value(var_repr['is_finite'])}" if var_repr['is_finite'] in s.get_model() else "F=?"
            print(f"    {var_repr['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")

    s.pop()
    print("-" * 70)
    print("====== AVC Additive Postulate Conflict Test Complete ======")

