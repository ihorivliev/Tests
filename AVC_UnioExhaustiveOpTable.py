from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
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

def avc_equiv(i1_repr, i2_repr): # Not used directly in this script's main tests, but kept for completeness
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"])
    finite_finite_equal_val = And(i1_repr["is_finite"], i2_repr["is_finite"], Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

def make_intensity(solver: Solver, repr_dict: Dict[str, Any], kind: str, value: Any = None):
    solver.add_assertion(repr_dict["constraints"])
    if kind == "ZS":
        solver.add_assertion(repr_dict["is_zero"]); solver.add_assertion(Not(repr_dict["is_areo"])); solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "AS":
        solver.add_assertion(repr_dict["is_areo"]); solver.add_assertion(Not(repr_dict["is_zero"])); solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "Fp": # Changed kind to "Fp" for clarity in this script
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

# --- Phase 2: Raw Operations Definitions (Copied) ---
def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder, current_omega_smt):
    return op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)

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

def raw_div_logic_builder(i1, i2, res, current_omega_smt): 
    formulas = []
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE) 
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE)
    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])
    formulas.append(Implies(divisor_is_unio, 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]), 
        Or(
            And(i1["is_zero"], 
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            And(i1["is_areo"],  
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i1["is_finite"], 
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym), 
                    rem_sym >= Int(0), rem_sym < i2["val"]), 
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)),
                    Ite(q_sym >= current_omega_smt, 
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))),
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))))); return And(formulas)

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
    print("====== AVC Unio Exhaustive Operation Table Test ======\n")
    
    s = Solver(name="z3") 
    current_omega = DEFAULT_OMEGA_MAX_VAL_NAT_SMT

    # Symbolic value for Fp cases in the table
    # This symbolic value will be used as the .val for Fp kinds.
    # Its > 0 constraint is handled by make_intensity when kind is "Fp".
    P_val_sym = Symbol("P_val_for_table", solver_INT_TYPE) 
    s.add_assertion(P_val_sym > Int(0)) # Assert it's positive once for all Fp uses

    op_list = [
        ("smart_raw_add", define_smart_raw_add_result),
        ("raw_mul", define_raw_mul_result),
        ("raw_sub", define_raw_sub_from_Unio_Areo_aspect_result), # Name for raw_sub_from_Unio_Areo_aspect
        ("raw_div", define_raw_div_result)
    ]
    
    kinds_to_test = ["ZS", "AS", "Fp"]

    for op_name, op_definer in op_list:
        print(f"\n--- Exhaustively Testing Operation: {op_name} with Unio/Finite Inputs ---")
        for kX_name in kinds_to_test:
            for kY_name in kinds_to_test:
                # Skip Fp op Fp for add, mul, div in this explicit table as their result is value-dependent on Omega
                if op_name in ["smart_raw_add", "raw_mul", "raw_div"] and kX_name == "Fp" and kY_name == "Fp":
                    print(f"    Skipping explicit table check for {op_name}(Fp, Fp) - value-dependent, covered by symbolic tests.")
                    continue
                
                s.push() # New context for each specific X, Y kind combination
                
                x_current = create_intensity_representation(f"x_{op_name}_{kX_name}")
                y_current = create_intensity_representation(f"y_{op_name}_{kY_name}")

                # Setup x_current and y_current to their specific kinds
                make_intensity(s, x_current, kX_name, value=(P_val_sym if kX_name == "Fp" else None) )
                make_intensity(s, y_current, kY_name, value=(P_val_sym if kY_name == "Fp" else None) )
                                
                actual_res = op_definer(x_current, y_current, f"res_{op_name}_{kX_name}_{kY_name}", current_omega)
                s.add_assertion(actual_res["definition"])
                s.add_assertion(actual_res["constraints"]) # Result must be valid

                # This list will hold the *precise properties* the actual_res should have
                expected_properties_of_actual_res = [] 
                
                # --- Define expected_properties_of_actual_res based on op_name, kX_name, kY_name ---
                # This is the manual specification of your AVC rules for each cell.
                if op_name == "smart_raw_add":
                    if kX_name == "ZS":
                        if kY_name == "ZS": expected_properties_of_actual_res.append(actual_res["is_zero"])
                        elif kY_name == "AS": expected_properties_of_actual_res.append(actual_res["is_areo"])
                        elif kY_name == "Fp": expected_properties_of_actual_res.extend([actual_res["is_finite"], Equals(actual_res["val"], y_current["val"])])
                    elif kX_name == "AS":
                        if kY_name == "ZS": expected_properties_of_actual_res.append(actual_res["is_areo"])
                        elif kY_name == "AS": expected_properties_of_actual_res.append(actual_res["is_areo"])
                        elif kY_name == "Fp": expected_properties_of_actual_res.extend([actual_res["is_finite"], Equals(actual_res["val"], y_current["val"])])
                    elif kX_name == "Fp":
                        if kY_name == "ZS": expected_properties_of_actual_res.extend([actual_res["is_finite"], Equals(actual_res["val"], x_current["val"])])
                        elif kY_name == "AS": expected_properties_of_actual_res.extend([actual_res["is_finite"], Equals(actual_res["val"], x_current["val"])])
                        # Fp + Fp is skipped above
                
                elif op_name == "raw_mul":
                    if kX_name == "ZS" or kY_name == "ZS": expected_properties_of_actual_res.append(actual_res["is_zero"])
                    elif kX_name == "AS" and kY_name == "AS": expected_properties_of_actual_res.append(actual_res["is_areo"])
                    elif (kX_name == "AS" and kY_name == "Fp") or \
                         (kX_name == "Fp" and kY_name == "AS"):
                        # Assumes P_val_sym > 0 (asserted globally for Fp cases)
                        expected_properties_of_actual_res.append(actual_res["is_areo"])
                    # Fp * Fp is skipped above
                
                elif op_name == "raw_sub": # raw_sub_from_Unio_Areo_aspect
                    # This operation always results in AreoState by its current definition,
                    # regardless of the second operand, if the first is ZS, AS, or Fp.
                    expected_properties_of_actual_res.append(actual_res["is_areo"])
                
                elif op_name == "raw_div":
                    if kY_name == "ZS" or kY_name == "AS": # Division by Unio
                        expected_properties_of_actual_res.append(actual_res["is_areo"])
                    elif kX_name == "ZS" and kY_name == "Fp": expected_properties_of_actual_res.append(actual_res["is_zero"])
                    elif kX_name == "AS" and kY_name == "Fp": expected_properties_of_actual_res.append(actual_res["is_areo"])
                    # Fp / Fp is skipped above
                
                if not expected_properties_of_actual_res:
                    # This should only be hit for skipped Fp op Fp cases
                    print(f"    Logic Error: No expected properties defined for {op_name}({kX_name}, {kY_name}) in table. Should have been skipped earlier.")
                    s.pop()
                    continue

                # The property to prove is that ALL expected assertions about actual_res hold true.
                property_actual_res_must_satisfy = And(expected_properties_of_actual_res)
                
                prove_or_find_counterexample(s, f"Table Check: {op_name}({kX_name}, {kY_name}) IS ExpectedState",
                                             [], # All setup (x_current, y_current, actual_res def/constraints) is in current solver 's' context
                                             property_actual_res_must_satisfy,
                                             model_vars_to_print=[x_current, y_current, actual_res], 
                                             print_model_on_fail=True)
                s.pop() # Pop context for this specific X, Y kind combination

    # Re-check specific Finite/Finite division cases from previous script for sanity
    print("\n--- Part 3: Re-checking Specific Finite / Finite Division Details (Omega=7) ---")
    f1_div = create_intensity_representation("f1_div_detail_table")
    f2_div = create_intensity_representation("f2_div_detail_table")

    s.push()
    make_intensity(s, f1_div, "Fp", value=6)
    make_intensity(s, f2_div, "Fp", value=2)
    actual_f6_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f6f2_table", current_omega)
    s.add_assertion(actual_f6_div_f2["definition"]); s.add_assertion(actual_f6_div_f2["constraints"])
    prove_or_find_counterexample(s, "F(6)/F(2) IS F(3) (Omega=7)", [], 
                                 And(actual_f6_div_f2["is_finite"], Equals(actual_f6_div_f2["val"], Int(3)))) 
    s.pop()
    
    s.push()
    make_intensity(s, f1_div, "Fp", value=5)
    make_intensity(s, f2_div, "Fp", value=2)
    actual_f5_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f5f2_table", current_omega)
    s.add_assertion(actual_f5_div_f2["definition"]); s.add_assertion(actual_f5_div_f2["constraints"])
    prove_or_find_counterexample(s, "F(5)/F(2) IS Areo (Omega=7, not exact)", [], 
                                 actual_f5_div_f2["is_areo"])
    s.pop()
    
    s.push()
    make_intensity(s, f1_div, "Fp", value=14)
    make_intensity(s, f2_div, "Fp", value=2)
    actual_f14_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f14f2_table", current_omega)
    s.add_assertion(actual_f14_div_f2["definition"]); s.add_assertion(actual_f14_div_f2["constraints"])
    prove_or_find_counterexample(s, "F(14)/F(2) IS Areo (Omega=7, quotient hits Omega)", [], 
                                 actual_f14_div_f2["is_areo"])
    s.pop()


    print("\n====== AVC Unio Exhaustive Operation Table Test Complete ======")

