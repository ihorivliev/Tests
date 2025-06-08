from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [3, 5, 7, 10] 
DEFAULT_OMEGA_MAX_VAL_NAT_PY = 7 
DEFAULT_OMEGA_MAX_VAL_NAT_SMT = Int(DEFAULT_OMEGA_MAX_VAL_NAT_PY)

# --- Phase 1: Foundational Definitions (Copied & Refined) ---
def create_intensity_representation(name_prefix: str) -> Dict[str, Any]:
    """
    Creates PySMT symbols for an Intensity and its critical validity constraints.
    An Intensity is abstractly one of: ZeroState, AreoState, or Finite(PosNat).
    This function models this using boolean flags and a conditional value.
    """
    is_zero = Symbol(f"{name_prefix}_is_zero", solver_BOOL_TYPE)
    is_areo = Symbol(f"{name_prefix}_is_areo", solver_BOOL_TYPE)
    is_finite = Symbol(f"{name_prefix}_is_finite", solver_BOOL_TYPE)
    val = Symbol(f"{name_prefix}_val", solver_INT_TYPE) # Value if finite

    constraint_exactly_one_state = ExactlyOne(is_zero, is_areo, is_finite)
    constraint_pos_nat_if_finite = Implies(is_finite, val > Int(0))
    
    all_constraints = And(constraint_exactly_one_state, constraint_pos_nat_if_finite)
    
    return {
        "is_zero": is_zero, "is_areo": is_areo, "is_finite": is_finite,
        "val": val, "constraints": all_constraints, "name": name_prefix
    }

def avc_equiv(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any]) -> FNode:
    """
    Defines the avc_equiv relation between two intensity representations.
    """
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"]) # Unio identification
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"]) # Unio identification
    finite_finite_equal_val = And(i1_repr["is_finite"], 
                                  i2_repr["is_finite"], 
                                  Equals(i1_repr["val"], i2_repr["val"]))
    
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

def make_intensity(solver: Solver, repr_dict: Dict[str, Any], kind: str, value: Any = None) -> None:
    """
    Asserts an intensity representation to be of a specific kind and optionally value.
    Ensures 'constraints' are asserted for the representation.
    """
    solver.add_assertion(repr_dict["constraints"]) # Ensure it's a valid structure
    if kind == "ZS":
        solver.add_assertion(repr_dict["is_zero"])
        solver.add_assertion(Not(repr_dict["is_areo"]))
        solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "AS":
        solver.add_assertion(repr_dict["is_areo"])
        solver.add_assertion(Not(repr_dict["is_zero"]))
        solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "Fp": # Using "Fp" for Finite(PosNat)
        solver.add_assertion(repr_dict["is_finite"])
        solver.add_assertion(Not(repr_dict["is_zero"]))
        solver.add_assertion(Not(repr_dict["is_areo"]))
        if value is not None:
            if isinstance(value, int): 
                solver.add_assertion(Equals(repr_dict["val"], Int(value)))
                if not (value > 0): 
                     print(f"WARNING for {repr_dict['name']} (in make_intensity): Concrete Finite value {value} is not > 0.")
            elif isinstance(value, FNode) and value.get_type() == solver_INT_TYPE: 
                solver.add_assertion(Equals(repr_dict["val"], value))
            else:
                raise TypeError(f"Invalid type or PySMT type for 'value' in make_intensity for Finite: got type {type(value)}, value: {value}")
        # If value is None, repr_dict["val"] is symbolic; its PosNat constraint (val > 0) is in repr_dict["constraints"]
    else:
        raise ValueError(f"Unknown kind for make_intensity: {kind}")

# --- Phase 2: Raw Operations Definitions ---
def build_result_definition(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                            res_repr: Dict[str, Any], 
                            op_logic_builder: Callable, 
                            current_omega_smt: FNode) -> FNode:
    """Helper to construct the definitional formula for an operation's result."""
    return op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)

# --- NEW: strict_areo_add ---
def strict_areo_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                  res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    """
    Logic builder for strict Areo absorption in addition.
    - ZS + X = X (emergence from Zero-aspect of Unio)
    - AS + X = AS (Areo absorption, X cannot "dilute" AS)
    - Fp + AS = AS 
    - Fp1 + Fp2 = standard thresholded sum
    """
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 

    # Case 1: i1 is ZeroState (ZS + X -> X)
    formulas.append(Implies(i1["is_zero"], 
        Or(
            # ZS + ZS -> ZS
            And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            # ZS + AS -> AS
            And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            # ZS + Fp -> Fp
            And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))
        )
    ))

    # Case 2: i1 is AreoState (AS + X -> AS)
    formulas.append(Implies(i1["is_areo"], 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) # Result is always AreoState
    ))
    
    # Case 3: i1 is Finite
    formulas.append(Implies(i1["is_finite"], 
        Or(
            # Fp + ZS -> Fp
            And(i2["is_zero"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])),
            # Fp + AS -> AS (Strict Areo absorption)
            And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            # Fp1 + Fp2 -> thresholded sum
            And(i2["is_finite"], 
                Ite(val_sum >= current_omega_smt, 
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # result is Areo
                    And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) # result is Finite(sum)
                )
            )
        )
    ))
    return And(formulas)

def define_strict_areo_add_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                                  result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, strict_areo_add_logic_builder, current_omega_smt)
    return res_repr

# --- Copied: raw_mul (unchanged) ---
def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"] 
    # ZS is annihilator
    formulas.append(Implies(i1["is_zero"], 
        And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), 
         And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    # AS * AS -> AS
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), 
                                i1["is_areo"], i2["is_areo"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    # AS * Fp -> if Fp.val > 0 then AS else ZS
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i1["is_areo"], i2["is_finite"]), 
        Ite(i2["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  
        )))
    # Fp * AS -> if Fp.val > 0 then AS else ZS
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i2["is_areo"], i1["is_finite"]), 
        Ite(i1["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  
        )))
    # Fp1 * Fp2 -> thresholded product
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
        Ite(val_prod >= current_omega_smt, 
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_prod)) 
        )))
    return And(formulas)

def define_raw_mul_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                          result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_mul_logic_builder, current_omega_smt)
    return res_repr

# --- Copied: raw_sub_from_Unio_Areo_aspect (unchanged) ---
def raw_sub_from_Unio_Areo_aspect_logic_builder(i_unio_areo: Dict[str, Any], _i_any: Dict[str, Any], 
                                                res: Dict[str, Any], _current_omega_smt: FNode) -> FNode: 
    # If first arg is ZS or AS (Unio), or even Finite (as per current definition), result is AS
    return And(Implies(Or(i_unio_areo["is_zero"], i_unio_areo["is_areo"], i_unio_areo["is_finite"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

def define_raw_sub_from_Unio_Areo_aspect_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                                                result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_sub_from_Unio_Areo_aspect_logic_builder, current_omega_smt)
    return res_repr

# --- Copied: raw_div (unchanged) ---
def raw_div_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode: 
    formulas = []
    # Create unique names for q_sym and rem_sym based on the result representation's name
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE) 
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE)

    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])
    formulas.append(Implies(divisor_is_unio, # X / Unio -> Areo (Unio)
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), # Divisor is Finite(p2)
        Or(
            # ZS / F(p2) => ZS
            And(i1["is_zero"], 
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            # AS / F(p2) => AS
            And(i1["is_areo"],  
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            # F(p1) / F(p2)
            And(i1["is_finite"], 
                # Assert the division algorithm
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), 
                    rem_sym >= Int(0), 
                    rem_sym < i2["val"]), # i2["val"] > 0 is from i2["constraints"]
                
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)), # Divides cleanly to a PosNat
                    Ite(q_sym >= current_omega_smt, # Apply Omega threshold
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # Result is Areo
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym)) # Result is Finite(quotient)
                    ),
                    # Does not divide cleanly to a PosNat (or quotient not > 0)
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) # Result is Areo (Unio)
                )
            )
        )
    ))
    return And(formulas)

def define_raw_div_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                          result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_div_logic_builder, current_omega_smt)
    return res_repr

# --- Generic Property Prover (Copied) ---
def prove_or_find_counterexample(solver: Solver, 
                                 property_name: str, 
                                 setup_assertions: List[Any], 
                                 property_to_prove_true: Any, 
                                 model_vars_to_print: List[Dict[str, Any]] = [],
                                 print_model_on_fail: bool = True):
    """
    Attempts to prove 'property_to_prove_true' given 'setup_assertions'.
    Proves P by checking if (setup AND NOT P) is UNSAT.
    If SAT, P does not hold universally, and a counterexample model is printed if requested.
    Returns True if property is proved, False otherwise.
    """
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions: solver.add_assertion(assertion)
    
    # Assert the negation of the property we want to prove true
    solver.add_assertion(Not(property_to_prove_true))
        
    result = solver.solve() # Check if "NOT property_to_prove_true" is SAT
    proved_universally = False

    if not result: # If "NOT property_to_prove_true" is UNSAT
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved_universally = True
    else: # If "NOT property_to_prove_true" is SAT, then "property_to_prove_true" does NOT hold universally
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_fail:
            for var_repr in model_vars_to_print:
                # Robust model printing
                val_str = f"V={solver.get_value(var_repr['val'])}" if var_repr['val'] in solver.get_model() else "V=?"
                is_z_str = f"Z={solver.get_value(var_repr['is_zero'])}" if var_repr['is_zero'] in solver.get_model() else "Z=?"
                is_a_str = f"A={solver.get_value(var_repr['is_areo'])}" if var_repr['is_areo'] in solver.get_model() else "A=?"
                is_f_str = f"F={solver.get_value(var_repr['is_finite'])}" if var_repr['is_finite'] in solver.get_model() else "F=?"
                print(f"  {var_repr['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
            
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Strict Areo Add - Algebraic Stress Test ======\n")
    
    # === Part 1: One-Time Foundational & Respectfulness Proofs (using DEFAULT Omega) ===
    print(f"--- Part 1: Foundational Integrity & Respectfulness (Default Omega = {DEFAULT_OMEGA_MAX_VAL_NAT_PY}) ---")
    s_base = Solver(name="z3")
    current_omega_default = DEFAULT_OMEGA_MAX_VAL_NAT_SMT

    # Symbolic intensities for foundational tests
    i1_base = create_intensity_representation("i1_base_saa") # saa for StrictAreoAdd
    i2_base = create_intensity_representation("i2_base_saa")
    i3_base = create_intensity_representation("i3_base_saa")
    
    # 1a. avc_equiv properties
    prove_or_find_counterexample(s_base, "Reflexivity of avc_equiv", [i1_base["constraints"]], avc_equiv(i1_base, i1_base))
    prove_or_find_counterexample(s_base, "Symmetry of avc_equiv", [i1_base["constraints"], i2_base["constraints"], avc_equiv(i1_base, i2_base)], avc_equiv(i2_base, i1_base))
    prove_or_find_counterexample(s_base, "Transitivity of avc_equiv", [i1_base["constraints"], i2_base["constraints"], i3_base["constraints"], avc_equiv(i1_base, i2_base), avc_equiv(i2_base, i3_base)], avc_equiv(i1_base, i3_base))
    
    # 1b. Impossible state checks
    impossible_i = create_intensity_representation("impossible_i_saa")
    prove_or_find_counterexample(s_base, "Constraint: NOT (is_finite AND val <= 0)", 
                             [impossible_i["constraints"], impossible_i["is_finite"], impossible_i["val"] <= Int(0)], FALSE())
    prove_or_find_counterexample(s_base, "Constraint: NOT (is_zero AND is_areo)",
                             [impossible_i["constraints"], impossible_i["is_zero"], impossible_i["is_areo"]], FALSE())
    # ... (add other impossible state checks if desired, e.g., is_zero AND is_finite)

    # 1c. Respectfulness (_outputs_are_avc_equiv) for ALL operations
    i1_respect = create_intensity_representation("i1_respect_saa")
    j1_respect = create_intensity_representation("j1_respect_saa") 
    i2_respect = create_intensity_representation("i2_respect_saa")
    j2_respect = create_intensity_representation("j2_respect_saa") 
    
    respect_setup = [
        i1_respect["constraints"], j1_respect["constraints"], 
        i2_respect["constraints"], j2_respect["constraints"],
        avc_equiv(i1_respect, i2_respect), avc_equiv(j1_respect, j2_respect)
    ]
    model_vars_for_respect_failure = [i1_respect, j1_respect, i2_respect, j2_respect] 

    # For strict_areo_add
    res1_saa = define_strict_areo_add_result(i1_respect, j1_respect, "res1_saa_respect", current_omega_default)
    res2_saa = define_strict_areo_add_result(i2_respect, j2_respect, "res2_saa_respect", current_omega_default)
    prove_or_find_counterexample(s_base, "strict_areo_add_outputs_are_avc_equiv",
                                 respect_setup + [res1_saa["definition"], res1_saa["constraints"], res2_saa["definition"], res2_saa["constraints"]],
                                 avc_equiv(res1_saa, res2_saa),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_saa, res2_saa], print_model_on_fail=True)
    # For raw_mul
    res1_rmul = define_raw_mul_result(i1_respect, j1_respect, "res1_rmul_respect_saa", current_omega_default)
    res2_rmul = define_raw_mul_result(i2_respect, j2_respect, "res2_rmul_respect_saa", current_omega_default)
    prove_or_find_counterexample(s_base, "raw_mul_outputs_are_avc_equiv",
                                 respect_setup + [res1_rmul["definition"], res1_rmul["constraints"], res2_rmul["definition"], res2_rmul["constraints"]],
                                 avc_equiv(res1_rmul, res2_rmul),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_rmul, res2_rmul], print_model_on_fail=True)
    # For raw_sub_from_Unio_Areo_aspect
    res1_rsub = define_raw_sub_from_Unio_Areo_aspect_result(i1_respect, j1_respect, "res1_rsub_respect_saa", current_omega_default)
    res2_rsub = define_raw_sub_from_Unio_Areo_aspect_result(i2_respect, j2_respect, "res2_rsub_respect_saa", current_omega_default)
    prove_or_find_counterexample(s_base, "raw_sub_from_Unio_Areo_aspect_outputs_are_avc_equiv",
                                 respect_setup + [res1_rsub["definition"], res1_rsub["constraints"], res2_rsub["definition"], res2_rsub["constraints"]],
                                 avc_equiv(res1_rsub, res2_rsub),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_rsub, res2_rsub], print_model_on_fail=True)
    # For raw_div
    res1_rdiv = define_raw_div_result(i1_respect, j1_respect, "res1_rdiv_respect_saa", current_omega_default)
    res2_rdiv = define_raw_div_result(i2_respect, j2_respect, "res2_rdiv_respect_saa", current_omega_default)
    prove_or_find_counterexample(s_base, "raw_div_outputs_are_avc_equiv",
                                 respect_setup + [res1_rdiv["definition"], res1_rdiv["constraints"], res2_rdiv["definition"], res2_rdiv["constraints"]],
                                 avc_equiv(res1_rdiv, res2_rdiv),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_rdiv, res2_rdiv], print_model_on_fail=True)
    del s_base # Release solver for Part 1

    # === Part 2: Parameterized Algebraic Gauntlet (Focus on strict_areo_add) ===
    print("\n\n--- Part 2: Parameterized Algebraic Property Tests (Focus on strict_areo_add) ---")
    
    # Symbolic intensities for algebraic laws, reused in loop
    a_alg = create_intensity_representation("a_alg_saa")
    b_alg = create_intensity_representation("b_alg_saa")
    c_alg = create_intensity_representation("c_alg_saa")
    
    ZS_const = create_intensity_representation("ZS_const_saa")
    AS_const = create_intensity_representation("AS_const_saa")

    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        current_omega_smt_loop = Int(omega_py_val)
        print(f"\n===== TESTING ALGEBRAIC PROPERTIES WITH Omega_max_val_nat = {omega_py_val} =====")
        s_omega = Solver(name="z3") # Fresh solver for each Omega value

        # Assert validity for a_alg, b_alg, c_alg, ZS_const, AS_const for this Omega context
        make_intensity(s_omega, a_alg, "Fp", value=Symbol(f"val_a_o{omega_py_val}", solver_INT_TYPE)) # Let them be symbolic Finite for broader tests
        make_intensity(s_omega, b_alg, "Fp", value=Symbol(f"val_b_o{omega_py_val}", solver_INT_TYPE))
        make_intensity(s_omega, c_alg, "Fp", value=Symbol(f"val_c_o{omega_py_val}", solver_INT_TYPE))
        s_omega.add_assertion(a_alg["constraints"]); s_omega.add_assertion(b_alg["constraints"]); s_omega.add_assertion(c_alg["constraints"])
        
        make_intensity(s_omega, ZS_const, "ZS")
        make_intensity(s_omega, AS_const, "AS")
        
        # Base setup lists for convenience (already asserted in s_omega by make_intensity)
        current_base_setup_abc = [a_alg["constraints"], b_alg["constraints"], c_alg["constraints"]]
        current_base_setup_ab = [a_alg["constraints"], b_alg["constraints"]]
        current_base_setup_a = [a_alg["constraints"]]
        
        # --- Commutativity of strict_areo_add ---
        res_ab_saa = define_strict_areo_add_result(a_alg, b_alg, f"res_ab_saa_o{omega_py_val}", current_omega_smt_loop)
        res_ba_saa = define_strict_areo_add_result(b_alg, a_alg, f"res_ba_saa_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s_omega, f"Commutativity of strict_areo_add (Omega={omega_py_val})", 
                                     current_base_setup_ab + [res_ab_saa["definition"], res_ab_saa["constraints"],
                                                              res_ba_saa["definition"], res_ba_saa["constraints"]],
                                     avc_equiv(res_ab_saa, res_ba_saa),
                                     model_vars_to_print=[a_alg,b_alg,res_ab_saa,res_ba_saa], print_model_on_fail=True)

        # --- Associativity of strict_areo_add ---
        sum_ab_saa = define_strict_areo_add_result(a_alg, b_alg, f"sum_ab_saa_o{omega_py_val}", current_omega_smt_loop)
        lhs_add_assoc_saa = define_strict_areo_add_result(sum_ab_saa, c_alg, f"lhs_saa_o{omega_py_val}", current_omega_smt_loop)
        sum_bc_saa = define_strict_areo_add_result(b_alg, c_alg, f"sum_bc_saa_o{omega_py_val}", current_omega_smt_loop)
        rhs_add_assoc_saa = define_strict_areo_add_result(a_alg, sum_bc_saa, f"rhs_saa_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s_omega, f"Associativity of strict_areo_add (Omega={omega_py_val})",
                                     current_base_setup_abc + [
                                         sum_ab_saa["definition"], sum_ab_saa["constraints"], lhs_add_assoc_saa["definition"], lhs_add_assoc_saa["constraints"],
                                         sum_bc_saa["definition"], sum_bc_saa["constraints"], rhs_add_assoc_saa["definition"], rhs_add_assoc_saa["constraints"]],
                                     avc_equiv(lhs_add_assoc_saa, rhs_add_assoc_saa), 
                                     model_vars_to_print=[a_alg,b_alg,c_alg,lhs_add_assoc_saa,rhs_add_assoc_saa], print_model_on_fail=True)

        # --- Distributivity (Left): raw_mul over strict_areo_add ---
        sum_bc_dist_l_saa = define_strict_areo_add_result(b_alg, c_alg, f"sum_bc_dl_saa_o{omega_py_val}", current_omega_smt_loop)
        lhs_dist_l_saa = define_raw_mul_result(a_alg, sum_bc_dist_l_saa, f"lhs_dl_saa_o{omega_py_val}", current_omega_smt_loop)
        prod_ab_dist_l_saa = define_raw_mul_result(a_alg, b_alg, f"prod_ab_dl_saa_o{omega_py_val}", current_omega_smt_loop)
        prod_ac_dist_l_saa = define_raw_mul_result(a_alg, c_alg, f"prod_ac_dl_saa_o{omega_py_val}", current_omega_smt_loop)
        rhs_dist_l_saa = define_strict_areo_add_result(prod_ab_dist_l_saa, prod_ac_dist_l_saa, f"rhs_dl_saa_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s_omega, f"Distributivity (Left) a*(b+c_strict) ~ (a*b)+(a*c_strict) (Omega={omega_py_val})",
                                     current_base_setup_abc + [
                                         sum_bc_dist_l_saa["definition"], sum_bc_dist_l_saa["constraints"], lhs_dist_l_saa["definition"], lhs_dist_l_saa["constraints"],
                                         prod_ab_dist_l_saa["definition"], prod_ab_dist_l_saa["constraints"], prod_ac_dist_l_saa["definition"], prod_ac_dist_l_saa["constraints"],
                                         rhs_dist_l_saa["definition"], rhs_dist_l_saa["constraints"]],
                                     avc_equiv(lhs_dist_l_saa, rhs_dist_l_saa),
                                     model_vars_to_print=[a_alg,b_alg,c_alg,lhs_dist_l_saa,rhs_dist_l_saa], print_model_on_fail=True)
        
        # --- Additive Cancellation with strict_areo_add ---
        add_ab_cxl_saa = define_strict_areo_add_result(a_alg, b_alg, f"add_ab_cxl_saa_o{omega_py_val}", current_omega_smt_loop)
        add_ac_cxl_saa = define_strict_areo_add_result(a_alg, c_alg, f"add_ac_cxl_saa_o{omega_py_val}", current_omega_smt_loop)
        premise_add_cxl_saa = And(add_ab_cxl_saa["definition"], add_ab_cxl_saa["constraints"],
                                add_ac_cxl_saa["definition"], add_ac_cxl_saa["constraints"],
                                avc_equiv(add_ab_cxl_saa, add_ac_cxl_saa))
        conclusion_add_cxl_saa = avc_equiv(b_alg, c_alg)
        prove_or_find_counterexample(s_omega, f"Additive Cancellation (strict_areo_add) (Omega={omega_py_val})",
                                     current_base_setup_abc + [premise_add_cxl_saa], 
                                     conclusion_add_cxl_saa, 
                                     model_vars_to_print=[a_alg, b_alg, c_alg, add_ab_cxl_saa, add_ac_cxl_saa], print_model_on_fail=True)

        # --- Idempotence for strict_areo_add ---
        add_aa_idem_saa = define_strict_areo_add_result(a_alg, a_alg, f"add_aa_idem_saa_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s_omega, f"Idempotence for strict_areo_add: a+a ~ a (Omega={omega_py_val})",
                                     current_base_setup_a + [add_aa_idem_saa["definition"], add_aa_idem_saa["constraints"]],
                                     avc_equiv(add_aa_idem_saa, a_alg),
                                     model_vars_to_print=[a_alg, add_aa_idem_saa], print_model_on_fail=True)
        
        # --- Identity-like Properties for strict_areo_add ---
        # ZS + a ~ a
        res_zs_a_saa = define_strict_areo_add_result(ZS_const, a_alg, f"res_zs_a_saa_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s_omega, f"strict_areo_add Identity (Left ZS): ZS + a ~ a (Omega={omega_py_val})",
                                     current_base_setup_a + [res_zs_a_saa["definition"], res_zs_a_saa["constraints"]], # ZS_const already asserted
                                     avc_equiv(res_zs_a_saa, a_alg))
        # AS + a ~ AS (This is the new key behavior)
        res_as_a_saa = define_strict_areo_add_result(AS_const, a_alg, f"res_as_a_saa_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s_omega, f"strict_areo_add Absorption (Left AS): AS + a ~ AS (Omega={omega_py_val})",
                                     current_base_setup_a + [res_as_a_saa["definition"], res_as_a_saa["constraints"]], # AS_const already asserted
                                     avc_equiv(res_as_a_saa, AS_const), # Expected result is AS
                                     model_vars_to_print=[AS_const, a_alg, res_as_a_saa], print_model_on_fail=True)

        # --- Sanity check: Associativity of raw_mul (should still hold) ---
        prod_ab_mul_recheck = define_raw_mul_result(a_alg, b_alg, f"prod_ab_rmul_recheck_o{omega_py_val}", current_omega_smt_loop)
        lhs_mul_assoc_recheck = define_raw_mul_result(prod_ab_mul_recheck, c_alg, f"lhs_rmul_recheck_o{omega_py_val}", current_omega_smt_loop)
        prod_bc_mul_recheck = define_raw_mul_result(b_alg, c_alg, f"prod_bc_rmul_recheck_o{omega_py_val}", current_omega_smt_loop)
        rhs_mul_assoc_recheck = define_raw_mul_result(a_alg, prod_bc_mul_recheck, f"rhs_rmul_recheck_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s_omega, f"Associativity of raw_mul (Re-check, Omega={omega_py_val})",
                                     current_base_setup_abc + [
                                         prod_ab_mul_recheck["definition"], prod_ab_mul_recheck["constraints"], lhs_mul_assoc_recheck["definition"], lhs_mul_assoc_recheck["constraints"],
                                         prod_bc_mul_recheck["definition"], prod_bc_mul_recheck["constraints"], rhs_mul_assoc_recheck["definition"], rhs_mul_assoc_recheck["constraints"]],
                                     avc_equiv(lhs_mul_assoc_recheck, rhs_mul_assoc_recheck))
        
        del s_omega # Release solver for this Omega value
        print("-" * 50)

    print("\n====== AVC Strict Areo Add - Algebraic Stress Test Complete ======")

