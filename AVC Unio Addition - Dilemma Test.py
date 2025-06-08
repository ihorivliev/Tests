from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any

# --- Configuration ---
DEFAULT_OMEGA_MAX_VAL_NAT_PY = 7 
DEFAULT_OMEGA_MAX_VAL_NAT_SMT = Int(DEFAULT_OMEGA_MAX_VAL_NAT_PY)

# --- Phase 1: Foundational Definitions (Copied & Refined) ---
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

def make_intensity(solver: Solver, repr_dict: Dict[str, Any], kind: str, value: Any = None) -> None:
    solver.add_assertion(repr_dict["constraints"])
    if kind == "ZS":
        solver.add_assertion(repr_dict["is_zero"]); solver.add_assertion(Not(repr_dict["is_areo"])); solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "AS":
        solver.add_assertion(repr_dict["is_areo"]); solver.add_assertion(Not(repr_dict["is_zero"])); solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "Fp":
        solver.add_assertion(repr_dict["is_finite"]); solver.add_assertion(Not(repr_dict["is_zero"])); solver.add_assertion(Not(repr_dict["is_areo"]))
        if value is not None:
            if isinstance(value, int): 
                solver.add_assertion(Equals(repr_dict["val"], Int(value)))
                if not (value > 0): 
                     print(f"WARNING for {repr_dict['name']} (in make_intensity): Concrete Finite value {value} is not > 0.")
            elif isinstance(value, FNode) and value.get_type() == solver_INT_TYPE: 
                solver.add_assertion(Equals(repr_dict["val"], value))
            else:
                raise TypeError(f"Invalid type or PySMT type for 'value' in make_intensity for Finite: got type {type(value)}, value: {value}")
    else:
        raise ValueError(f"Unknown kind for make_intensity: {kind}")

# --- Phase 2: Raw Operations Definitions ---
def build_result_definition(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                            res_repr: Dict[str, Any], 
                            op_logic_builder: Callable, 
                            current_omega_smt: FNode) -> FNode:
    return op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)

# --- smart_raw_add (Conceptual U + X_DFI -> X_DFI via ZS-aspect) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # ZS + AS -> AS
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))))) # ZS + Fp -> Fp
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  # AS + ZS -> AS
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  # AS + AS -> AS
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))))) # AS + Fp -> Fp (Unio identity behavior)
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) # Fp + ZS -> Fp
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) # Fp + AS -> Fp (Unio identity behavior)
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), Ite(val_sum >= current_omega_smt, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)))))
    return And(formulas)

def define_smart_raw_add_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                                result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder, current_omega_smt)
    return res_repr

# --- strict_areo_add (Conceptual A + X_DFI -> A via AS-aspect absorption) ---
def strict_areo_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                  res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])), # ZS + ZS -> ZS
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # ZS + AS -> AS
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))))) # ZS + Fp -> Fp
    formulas.append(Implies(i1["is_areo"], # AS + X -> AS (Strict Areo absorption)
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) # Fp + ZS -> Fp
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), # Fp + AS -> AS (Strict Areo absorption)
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]))
    ))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), Ite(val_sum >= current_omega_smt, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)))))
    return And(formulas)

def define_strict_areo_add_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                                  result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, strict_areo_add_logic_builder, current_omega_smt)
    return res_repr

# --- Generic Property Prover ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[Any], 
                                 property_to_prove_true: Any, 
                                 model_vars_to_print: List[Dict[str, Any]] = [],
                                 print_model_on_fail: bool = True):
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions: solver.add_assertion(assertion)
    solver.add_assertion(Not(property_to_prove_true))
    result = solver.solve() 
    proved = False
    if not result: 
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved = True
    else: 
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_fail:
            for var_repr in model_vars_to_print:
                val_str = f"V={solver.get_value(var_repr['val'])}" if var_repr['val'] in solver.get_model() else "V=?"
                is_z_str = f"Z={solver.get_value(var_repr['is_zero'])}" if var_repr['is_zero'] in solver.get_model() else "Z=?"
                is_a_str = f"A={solver.get_value(var_repr['is_areo'])}" if var_repr['is_areo'] in solver.get_model() else "A=?"
                is_f_str = f"F={solver.get_value(var_repr['is_finite'])}" if var_repr['is_finite'] in solver.get_model() else "F=?"
                print(f"  {var_repr['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
    solver.pop() 
    print("-" * 70)
    return proved

# --- Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Unio Addition Dilemma Test ======\n")
    
    s = Solver(name="z3") 
    current_omega = DEFAULT_OMEGA_MAX_VAL_NAT_SMT

    # Symbolic intensities for respectfulness tests
    i1_respect = create_intensity_representation("i1_respect_dilemma")
    j1_respect = create_intensity_representation("j1_respect_dilemma") 
    i2_respect = create_intensity_representation("i2_respect_dilemma")
    j2_respect = create_intensity_representation("j2_respect_dilemma") 
    
    respect_setup = [
        i1_respect["constraints"], j1_respect["constraints"], 
        i2_respect["constraints"], j2_respect["constraints"],
        avc_equiv(i1_respect, i2_respect), avc_equiv(j1_respect, j2_respect)
    ]
    model_vars_for_respect_failure = [i1_respect, j1_respect, i2_respect, j2_respect] 

    # --- Part 1: Re-confirm smart_raw_add Respects Equivalence ---
    print("--- Part 1: Verifying smart_raw_add Respects avc_equiv (Well-defined on AVC_Space) ---")
    res1_smart = define_smart_raw_add_result(i1_respect, j1_respect, "res1_smart_respect", current_omega)
    res2_smart = define_smart_raw_add_result(i2_respect, j2_respect, "res2_smart_respect", current_omega)
    prove_or_find_counterexample(s, "smart_raw_add_outputs_are_avc_equiv",
                                 respect_setup + [res1_smart["definition"], res1_smart["constraints"], 
                                                  res2_smart["definition"], res2_smart["constraints"]],
                                 avc_equiv(res1_smart, res2_smart),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_smart, res2_smart], 
                                 print_model_on_fail=True)

    # --- Part 2: Re-confirm strict_areo_add Violates Equivalence ---
    print("\n--- Part 2: Verifying strict_areo_add Violates avc_equiv (NOT Well-defined on AVC_Space) ---")
    res1_strict = define_strict_areo_add_result(i1_respect, j1_respect, "res1_strict_respect", current_omega)
    res2_strict = define_strict_areo_add_result(i2_respect, j2_respect, "res2_strict_respect", current_omega)
    strict_add_respects = prove_or_find_counterexample(s, "strict_areo_add_outputs_are_avc_equiv",
                                 respect_setup + [res1_strict["definition"], res1_strict["constraints"], 
                                                  res2_strict["definition"], res2_strict["constraints"]],
                                 avc_equiv(res1_strict, res2_strict),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_strict, res2_strict], 
                                 print_model_on_fail=True)
    if not strict_add_respects:
        print("  ANALYSIS: The counterexample for strict_areo_add_outputs_are_avc_equiv demonstrates:")
        print("  If i1=ZeroState, i2=AreoState (so i1~i2), and j1=j2=Finite(p), then:")
        print("    strict_add(i1,j1) = ZS + Fp -> Fp")
        print("    strict_add(i2,j2) = AS + Fp -> AS")
        print("  Since Fp is NOT avc_equiv to AS, the results are not equivalent, violating respectfulness.")
        print("  This means strict_areo_add is NOT well-defined on AVC_Space where ZS and AS are identified.")

    # --- Part 3: Explicit Demonstration of the Dilemma for "Unio + Finite(p)" ---
    print("\n--- Part 3: Explicit Demonstration of 'Unio + Finite(p)' Dilemma ---")
    
    ZS_concrete = create_intensity_representation("ZS_concrete_dilemma")
    AS_concrete = create_intensity_representation("AS_concrete_dilemma")
    Fp_concrete = create_intensity_representation("Fp_concrete_dilemma")
    p_concrete_val = 3 # Example value

    # Setup concrete ZS, AS, Fp(3)
    s.push() # Context for concrete ZS, AS, Fp
    make_intensity(s, ZS_concrete, "ZS")
    make_intensity(s, AS_concrete, "AS")
    make_intensity(s, Fp_concrete, "Fp", value=p_concrete_val)

    print(f"\n  Scenario 3a: Using smart_raw_add (Unio's ZS-aspect for emergence) with Omega={DEFAULT_OMEGA_MAX_VAL_NAT_PY}")
    # smart_raw_add(ZS_concrete, Fp_concrete)
    res_smart_zs_fp = define_smart_raw_add_result(ZS_concrete, Fp_concrete, "res_smart_zs_fp", current_omega)
    s.add_assertion(res_smart_zs_fp["definition"]); s.add_assertion(res_smart_zs_fp["constraints"])
    # smart_raw_add(AS_concrete, Fp_concrete)
    res_smart_as_fp = define_smart_raw_add_result(AS_concrete, Fp_concrete, "res_smart_as_fp", current_omega)
    s.add_assertion(res_smart_as_fp["definition"]); s.add_assertion(res_smart_as_fp["constraints"])

    # Prove ZS+Fp is Fp(3)
    prove_or_find_counterexample(s, f"smart_add(ZS, Fp({p_concrete_val})) IS Fp({p_concrete_val})",
                                 [], And(res_smart_zs_fp["is_finite"], Equals(res_smart_zs_fp["val"], Int(p_concrete_val))))
    # Prove AS+Fp is Fp(3)
    prove_or_find_counterexample(s, f"smart_add(AS, Fp({p_concrete_val})) IS Fp({p_concrete_val})",
                                 [], And(res_smart_as_fp["is_finite"], Equals(res_smart_as_fp["val"], Int(p_concrete_val))))
    # Prove their results are equivalent
    prove_or_find_counterexample(s, "smart_add(ZS,Fp) ~ smart_add(AS,Fp) [Consistency for Unio]",
                                 [], avc_equiv(res_smart_zs_fp, res_smart_as_fp))
    print("  CONCLUSION for smart_raw_add: ZS+Fp -> Fp, and AS+Fp -> Fp. Results are avc_equiv.")
    print("  This aligns with Unio's Zero-aspect governing emergence (Postulate 6.1) and is well-defined.")

    print(f"\n  Scenario 3b: Using strict_areo_add (AS-aspect absorption) with Omega={DEFAULT_OMEGA_MAX_VAL_NAT_PY}")
    # strict_areo_add(ZS_concrete, Fp_concrete)
    res_strict_zs_fp = define_strict_areo_add_result(ZS_concrete, Fp_concrete, "res_strict_zs_fp", current_omega)
    s.add_assertion(res_strict_zs_fp["definition"]); s.add_assertion(res_strict_zs_fp["constraints"])
    # strict_areo_add(AS_concrete, Fp_concrete)
    res_strict_as_fp = define_strict_areo_add_result(AS_concrete, Fp_concrete, "res_strict_as_fp", current_omega)
    s.add_assertion(res_strict_as_fp["definition"]); s.add_assertion(res_strict_as_fp["constraints"])

    # Prove ZS+Fp is Fp(3)
    prove_or_find_counterexample(s, f"strict_add(ZS, Fp({p_concrete_val})) IS Fp({p_concrete_val})",
                                 [], And(res_strict_zs_fp["is_finite"], Equals(res_strict_zs_fp["val"], Int(p_concrete_val))))
    # Prove AS+Fp is AS
    prove_or_find_counterexample(s, f"strict_add(AS, Fp({p_concrete_val})) IS AS",
                                 [], res_strict_as_fp["is_areo"])
    # Prove their results are NOT equivalent
    prove_or_find_counterexample(s, "strict_add(ZS,Fp) IS NOT ~ strict_add(AS,Fp) [Inconsistency for Unio]",
                                 [], Not(avc_equiv(res_strict_zs_fp, res_strict_as_fp)), # Note: proving NOT equiv
                                 model_vars_to_print=[res_strict_zs_fp, res_strict_as_fp], print_model_on_fail=False) # Expect SAT for Not(equiv)
    
    print("  CONCLUSION for strict_areo_add: ZS+Fp -> Fp, but AS+Fp -> AS. Results are NOT avc_equiv.")
    print("  This highlights the conflict: if ZS~AS (Unio), then 'Unio+Fp' yields different outcomes.")
    s.pop() # Pop context for concrete ZS, AS, Fp

    # --- Part 4: Conceptual Implications (Textual) ---
    print("\n\n--- Part 4: Conceptual Implications of the Dilemma ---")
    print("The SMT tests rigorously demonstrate the following for addition (+_avc):")
    print("1. `smart_raw_add` (where Unio's ZS-aspect governs Fp addition, e.g., AS+Fp -> Fp):")
    print("   - RESPECTS `avc_equiv` (is well-defined on AVC_Space).")
    print("   - Aligns with Postulate 6.1 (Conceptual Addition from Unio: U + X_DFI -> X_DFI).")
    print("   - Leads to non-associative addition and non-distributive mul over add (as shown in previous tests).")
    print("\n2. `strict_areo_add` (where Unio's AS-aspect governs Fp addition, e.g., AS+Fp -> AS):")
    print("   - VIOLATES `avc_equiv` (is NOT well-defined on AVC_Space).")
    print("     The choice of Unio representative (ZS vs AS) yields non-avc_equiv results for `Unio + Fp`.")
    print("   - Attempts to align with Postulate 2.2.iii (Areo's transfinite absorption: A + X_DFI -> A).")
    print("   - Leads to associative addition and distributive mul over add (as shown in previous tests).")
    print("\nDILEMMA:")
    print("The AVC conceptual model desires both:")
    print("  a) Unio as a single identified point (ZS ~ AS) for consistent operations (Postulate 4.1).")
    print("  b) Emergence from Unio's Zero-potential for addition (Postulate 6.1: U + X_DFI -> X_DFI).")
    print("  c) AreoState having transfinite absorptive properties for addition (Postulate 2.2.iii: A + X_DFI -> A).")
    print("\nThe formal tests show that (b) and (c) lead to conflicting definitions of a single binary addition operation if (a) is to be upheld for that operation's respectfulness.")
    print("  - `smart_raw_add` satisfies (a) and (b), but operationalizes (c) as AS+Fp -> Fp (via equivalence to ZS+Fp).")
    print("  - `strict_areo_add` attempts (c) more directly (AS+Fp -> AS), but then violates (a) for addition.")
    print("\nThis implies that a single binary addition operation +_avc cannot simultaneously satisfy all three conceptual desires with full fidelity if Unio is a simple ZS~AS identification.")
    print("The model must prioritize which aspect of Unio's interaction dictates the primary addition rule, or define distinct operations.")
    print("The current `smart_raw_add` (used in most successful algebraic characterizations) prioritizes well-definedness on AVC_Space and emergence from Zero-potential.")

    print("\n====== AVC Unio Addition Dilemma Test Complete ======")

