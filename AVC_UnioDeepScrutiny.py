from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE # Added FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode # <<< ADDED THIS IMPORT
from typing import Callable, List, Dict, Any

# --- Configuration ---
DEFAULT_OMEGA_MAX_VAL_NAT_PY = 7 
DEFAULT_OMEGA_MAX_VAL_NAT_SMT = Int(DEFAULT_OMEGA_MAX_VAL_NAT_PY)

# --- Phase 1: Foundational Definitions (Copied) ---
def create_intensity_representation(name_prefix: str):
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

def avc_equiv(i1_repr, i2_repr):
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"])
    finite_finite_equal_val = And(i1_repr["is_finite"], i2_repr["is_finite"], Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Corrected Helper to create and assert a specific intensity state ---
def make_intensity(solver: Solver, repr_dict: Dict[str, Any], kind: str, value: Any = None):
    solver.add_assertion(repr_dict["constraints"])
    if kind == "ZS":
        solver.add_assertion(repr_dict["is_zero"])
        solver.add_assertion(Not(repr_dict["is_areo"]))
        solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "AS":
        solver.add_assertion(repr_dict["is_areo"])
        solver.add_assertion(Not(repr_dict["is_zero"]))
        solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "Finite":
        solver.add_assertion(repr_dict["is_finite"])
        solver.add_assertion(Not(repr_dict["is_zero"]))
        solver.add_assertion(Not(repr_dict["is_areo"]))
        if value is not None:
            if isinstance(value, int): # If it's a Python int, convert to PySMT Int
                solver.add_assertion(Equals(repr_dict["val"], Int(value)))
                if not (value > 0): 
                     print(f"WARNING for {repr_dict['name']} (in make_intensity): Concrete Finite value {value} is not > 0.")
            # CORRECTED LINE BELOW: Check if value is an FNode (which Symbol() returns)
            elif isinstance(value, FNode) and value.get_type() == solver_INT_TYPE: # If it's already a PySMT FNode (Symbol)
                solver.add_assertion(Equals(repr_dict["val"], value))
                # The constraint that this symbolic 'value' (if it's meant to be a PosNat value)
                # is > 0 should be handled by the caller or is part of repr_dict["constraints"]
                # if repr_dict["val"] was intended to be this symbol from its creation.
                # Forcing it here might be redundant if 'value' is a fresh symbol for a test.
                # We rely on repr_dict["constraints"] to enforce repr_dict["val"] > 0.
            else:
                # This will catch if a non-int, non-FNode type is passed, or if FNode is not INT
                raise TypeError(f"Invalid type or PySMT type for 'value' in make_intensity for Finite: got type {type(value)}, value: {value}")
        # If value is None, repr_dict["val"] is fully symbolic, its PosNat constraint is in repr_dict["constraints"]
    else:
        raise ValueError(f"Unknown kind for make_intensity: {kind}")


# --- Phase 2: Raw Operations Definitions (Copied & Corrected raw_div) ---
def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder, current_omega_smt):
    core_logic_formula = op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)
    return core_logic_formula 

def smart_raw_add_logic_builder(i1, i2, res, current_omega_smt):
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])))))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))))) 
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) 
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"])))) 
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), Ite(val_sum >= current_omega_smt, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)))))
    return And(formulas)

def define_smart_raw_add_result(i1_repr, i2_repr, result_name_prefix: str, current_omega_smt):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder, current_omega_smt)
    return res_repr

def raw_mul_logic_builder(i1, i2, res, current_omega_smt):
    formulas = []
    val_prod = i1["val"] * i2["val"] 
    formulas.append(Implies(i1["is_zero"], 
        And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), 
         And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), 
                                i1["is_areo"], i2["is_areo"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i1["is_areo"], i2["is_finite"]), 
        Ite(i2["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  
        )))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]),
                                i2["is_areo"], i1["is_finite"]), 
        Ite(i1["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  
        )))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
        Ite(val_prod >= current_omega_smt, 
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_prod)) 
        )))
    return And(formulas)

def define_raw_mul_result(i1_repr, i2_repr, result_name_prefix: str, current_omega_smt):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_mul_logic_builder, current_omega_smt)
    return res_repr

def raw_sub_from_Unio_Areo_aspect_logic_builder(i_unio_areo, _i_any, res, _current_omega_smt): 
    return And(Implies(Or(i_unio_areo["is_zero"], i_unio_areo["is_areo"], i_unio_areo["is_finite"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

def define_raw_sub_from_Unio_Areo_aspect_result(i1_repr, i2_repr, result_name_prefix: str, current_omega_smt):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_sub_from_Unio_Areo_aspect_logic_builder, current_omega_smt)
    return res_repr

def raw_div_logic_builder(i1, i2, res, current_omega_smt): # i1 is dividend, i2 is divisor
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
            And(i1["is_zero"], # ZS / F(p2) => ZS
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            And(i1["is_areo"],  # AS / F(p2) => AS
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i1["is_finite"], # F(p1) / F(p2)
                # Assert the division algorithm: i1.val = q_sym * i2.val + rem_sym
                # AND 0 <= rem_sym < i2.val (since i2.val > 0 is guaranteed by i2["constraints"] if i2["is_finite"])
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), 
                    rem_sym >= Int(0), 
                    rem_sym < i2["val"]), 
                
                Ite(And(Equals(rem_sym, Int(0)), # Divides exactly
                          q_sym > Int(0)           # Quotient is positive (to form a PosNat)
                     ),
                    # Divides cleanly to a PosNat
                    Ite(q_sym >= current_omega_smt, # Apply Omega threshold to the quotient
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # Result is Areo
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], # Result is Finite(quotient)
                            Equals(res["val"], q_sym)) 
                    ),
                    # Does not divide cleanly to a PosNat (or quotient not > 0)
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) # Result is Areo (Unio)
                )
            )
        )
    ))
    return And(formulas)

def define_raw_div_result(i1_repr, i2_repr, result_name_prefix: str, current_omega_smt):
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
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions:
        solver.add_assertion(assertion)
    
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
                # Check if value exists in model before trying to get it
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
    print("====== AVC Unio & Division Deep Scrutiny (Corrected) ======\n")
    
    s = Solver(name="z3") 

    # Symbolic Intensities for tests
    i1 = create_intensity_representation("i1_unio_div")
    i2 = create_intensity_representation("i2_unio_div")
    # i3 = create_intensity_representation("i3_unio_div") # Not used in this version's main tests
    p_sym = create_intensity_representation("p_sym_unio_div") # For representing Finite(p)

    # Constants for Unio representation (asserted once in solver 's')
    ZS = create_intensity_representation("ZS_unio_const")
    AS = create_intensity_representation("AS_unio_const")
    s.add_assertion(ZS["constraints"]); s.add_assertion(ZS["is_zero"])
    s.add_assertion(AS["constraints"]); s.add_assertion(AS["is_areo"])

    current_omega = DEFAULT_OMEGA_MAX_VAL_NAT_SMT

    # --- 1. Re-verify raw_div_outputs_are_avc_equiv ---
    print("--- Verifying: raw_div_outputs_are_avc_equiv (Symbolic Core Test) ---")
    i1_op_val = create_intensity_representation("i1_op_div_val")
    j1_op_val = create_intensity_representation("j1_op_div_val") # Divisor 1
    i2_op_val = create_intensity_representation("i2_op_div_val")
    j2_op_val = create_intensity_representation("j2_op_div_val") # Divisor 2
    
    op_val_setup_div = [
        i1_op_val["constraints"], j1_op_val["constraints"], 
        i2_op_val["constraints"], j2_op_val["constraints"],
        avc_equiv(i1_op_val, i2_op_val), avc_equiv(j1_op_val, j2_op_val)
    ]

    res1_rdiv = define_raw_div_result(i1_op_val, j1_op_val, "res1_rdiv_val", current_omega)
    res2_rdiv = define_raw_div_result(i2_op_val, j2_op_val, "res2_rdiv_val", current_omega)
    
    prove_or_find_counterexample(s, "raw_div_outputs_are_avc_equiv",
                                 op_val_setup_div + [
                                     res1_rdiv["definition"], res1_rdiv["constraints"], 
                                     res2_rdiv["definition"], res2_rdiv["constraints"]],
                                 avc_equiv(res1_rdiv, res2_rdiv),
                                 model_vars_to_print=[i1_op_val, j1_op_val, i2_op_val, j2_op_val, res1_rdiv, res2_rdiv],
                                 print_model_on_fail=True)

    # --- 2. Systematic Explicit Tests for X / UnioRep ---
    print("\n--- Explicit Tests: X / UnioRepresentative ---")
    # Expected result for X / Unio is Unio (represented by AS as per raw_div_logic_builder)
    
    # 2a. Finite(p) / ZeroState ~ AreoState
    s.push()
    make_intensity(s, i1, "Finite", value=Symbol("val_for_fp_div_zs", solver_INT_TYPE)) 
    actual_res_fp_div_zs = define_raw_div_result(i1, ZS, "act_fp_div_zs", current_omega)
    s.add_assertion(actual_res_fp_div_zs["definition"]); s.add_assertion(actual_res_fp_div_zs["constraints"])
    prove_or_find_counterexample(s, "Explicit: Finite(p) / ZeroState ~ AreoState", [], avc_equiv(actual_res_fp_div_zs, AS))
    s.pop()

    # 2b. Finite(p) / AreoState ~ AreoState
    s.push()
    make_intensity(s, i1, "Finite", value=Symbol("val_for_fp_div_as", solver_INT_TYPE)) 
    actual_res_fp_div_as = define_raw_div_result(i1, AS, "act_fp_div_as", current_omega)
    s.add_assertion(actual_res_fp_div_as["definition"]); s.add_assertion(actual_res_fp_div_as["constraints"])
    prove_or_find_counterexample(s, "Explicit: Finite(p) / AreoState ~ AreoState", [], avc_equiv(actual_res_fp_div_as, AS))
    s.pop()

    # 2c. ZeroState / ZeroState ~ AreoState
    s.push()
    actual_res_zs_div_zs = define_raw_div_result(ZS, ZS, "act_zs_div_zs", current_omega)
    s.add_assertion(actual_res_zs_div_zs["definition"]); s.add_assertion(actual_res_zs_div_zs["constraints"])
    prove_or_find_counterexample(s, "Explicit: ZeroState / ZeroState ~ AreoState", [], avc_equiv(actual_res_zs_div_zs, AS))
    s.pop()
    
    # 2d. ZeroState / AreoState ~ AreoState
    s.push()
    actual_res_zs_div_as = define_raw_div_result(ZS, AS, "act_zs_div_as", current_omega)
    s.add_assertion(actual_res_zs_div_as["definition"]); s.add_assertion(actual_res_zs_div_as["constraints"])
    prove_or_find_counterexample(s, "Explicit: ZeroState / AreoState ~ AreoState", [], avc_equiv(actual_res_zs_div_as, AS))
    s.pop()

    # 2e. AreoState / ZeroState ~ AreoState
    s.push()
    actual_res_as_div_zs = define_raw_div_result(AS, ZS, "act_as_div_zs", current_omega)
    s.add_assertion(actual_res_as_div_zs["definition"]); s.add_assertion(actual_res_as_div_zs["constraints"])
    prove_or_find_counterexample(s, "Explicit: AreoState / ZeroState ~ AreoState", [], avc_equiv(actual_res_as_div_zs, AS))
    s.pop()

    # 2f. AreoState / AreoState ~ AreoState
    s.push()
    actual_res_as_div_as = define_raw_div_result(AS, AS, "act_as_div_as", current_omega)
    s.add_assertion(actual_res_as_div_as["definition"]); s.add_assertion(actual_res_as_div_as["constraints"])
    prove_or_find_counterexample(s, "Explicit: AreoState / AreoState ~ AreoState", [], avc_equiv(actual_res_as_div_as, AS))
    s.pop()

    # --- 3. Systematic Explicit Tests for UnioRep / Finite(p) ---
    print("\n--- Explicit Tests: UnioRepresentative / Finite(p) ---")
    # 3a. ZeroState / Finite(p) ~ ZeroState
    s.push()
    make_intensity(s, i1, "Finite", value=Symbol("val_for_zs_div_fp", solver_INT_TYPE)) 
    actual_res_zs_div_fp = define_raw_div_result(ZS, i1, "act_zs_div_fp", current_omega)
    s.add_assertion(actual_res_zs_div_fp["definition"]); s.add_assertion(actual_res_zs_div_fp["constraints"])
    prove_or_find_counterexample(s, "Explicit: ZeroState / Finite(p) ~ ZeroState", [], avc_equiv(actual_res_zs_div_fp, ZS))
    s.pop()

    # 3b. AreoState / Finite(p) ~ AreoState
    s.push()
    make_intensity(s, i1, "Finite", value=Symbol("val_for_as_div_fp", solver_INT_TYPE)) 
    actual_res_as_div_fp = define_raw_div_result(AS, i1, "act_as_div_fp", current_omega)
    s.add_assertion(actual_res_as_div_fp["definition"]); s.add_assertion(actual_res_as_div_fp["constraints"])
    prove_or_find_counterexample(s, "Explicit: AreoState / Finite(p) ~ AreoState", [], avc_equiv(actual_res_as_div_fp, AS))
    s.pop()

    # --- 4. Test Finite / Finite division cases more thoroughly ---
    print("\n--- Testing Finite / Finite Division Details ---")
    f1_div = create_intensity_representation("f1_div_detail")
    f2_div = create_intensity_representation("f2_div_detail")
    exp_div = create_intensity_representation("exp_div_detail")

    # Case 4a: F(6) / F(2) = F(3) (Omega=7)
    s.push()
    make_intensity(s, f1_div, "Finite", value=6)
    make_intensity(s, f2_div, "Finite", value=2)
    actual_f6_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f6f2", current_omega)
    s.add_assertion(actual_f6_div_f2["definition"]); s.add_assertion(actual_f6_div_f2["constraints"])
    make_intensity(s, exp_div, "Finite", value=3)
    prove_or_find_counterexample(s, "F(6)/F(2)=F(3) (Omega=7)", [], avc_equiv(actual_f6_div_f2, exp_div)) 
    s.pop()

    # Case 4b: F(5) / F(2) = Unio (Areo) because not exact (Omega=7)
    s.push()
    make_intensity(s, f1_div, "Finite", value=5)
    make_intensity(s, f2_div, "Finite", value=2)
    actual_f5_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f5f2", current_omega)
    s.add_assertion(actual_f5_div_f2["definition"]); s.add_assertion(actual_f5_div_f2["constraints"])
    make_intensity(s, exp_div, "AS") 
    prove_or_find_counterexample(s, "F(5)/F(2)=Areo (Omega=7, not exact)", [], avc_equiv(actual_f5_div_f2, exp_div))
    s.pop()
    
    # Case 4c: F(14) / F(2) = Areo (because quotient 7 >= Omega=7)
    s.push()
    make_intensity(s, f1_div, "Finite", value=14)
    make_intensity(s, f2_div, "Finite", value=2)
    actual_f14_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f14f2", current_omega)
    s.add_assertion(actual_f14_div_f2["definition"]); s.add_assertion(actual_f14_div_f2["constraints"])
    make_intensity(s, exp_div, "AS") 
    prove_or_find_counterexample(s, "F(14)/F(2)=Areo (Omega=7, quotient hits Omega)", [], avc_equiv(actual_f14_div_f2, exp_div))
    s.pop()

    # --- 5. Re-scrutinize Add/Mul with Unio (Chapter 6 Postulates) ---
    print("\n--- Re-scrutinizing Core Unio Operations (Add/Mul) ---")
    s.push() 
    make_intensity(s, p_sym, "Finite", value=Symbol("val_for_re_scrutiny_p", solver_INT_TYPE)) 

    actual_add_zs_f = define_smart_raw_add_result(ZS, p_sym, "act_addzs_f_re", current_omega)
    s.add_assertion(actual_add_zs_f["definition"]); s.add_assertion(actual_add_zs_f["constraints"])
    prove_or_find_counterexample(s, "Ch6: ZS + Finite(p) ~ Finite(p)", [], avc_equiv(actual_add_zs_f, p_sym))

    actual_mul_zs_f = define_raw_mul_result(ZS, p_sym, "act_mulzs_f_re", current_omega)
    s.add_assertion(actual_mul_zs_f["definition"]); s.add_assertion(actual_mul_zs_f["constraints"])
    prove_or_find_counterexample(s, "Ch6: ZS * Finite(p) ~ ZeroState", [], avc_equiv(actual_mul_zs_f, ZS))
    s.pop()


    print("\n====== AVC Unio & Division Deep Scrutiny Complete ======")

