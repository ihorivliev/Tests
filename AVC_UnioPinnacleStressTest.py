from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode # For isinstance check
# DO NOT import OP_EQUALS from pysmt.operators
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

def make_intensity(solver: Solver, repr_dict: Dict[str, Any], kind: str, value: Any = None):
    solver.add_assertion(repr_dict["constraints"])
    if kind == "ZS":
        solver.add_assertion(repr_dict["is_zero"]); solver.add_assertion(Not(repr_dict["is_areo"])); solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "AS":
        solver.add_assertion(repr_dict["is_areo"]); solver.add_assertion(Not(repr_dict["is_zero"])); solver.add_assertion(Not(repr_dict["is_finite"]))
    elif kind == "Finite":
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
    print("====== AVC Unio & Division Pinnacle Scrutiny (Corrected v2) ======\n")
    
    s = Solver(name="z3") 
    current_omega = DEFAULT_OMEGA_MAX_VAL_NAT_SMT

    i1 = create_intensity_representation("i1_unio_div")
    i2 = create_intensity_representation("i2_unio_div")
    p_sym = create_intensity_representation("p_sym_unio_div") 

    ZS = create_intensity_representation("ZS_unio_const")
    AS = create_intensity_representation("AS_unio_const")
    s.add_assertion(ZS["constraints"]); s.add_assertion(ZS["is_zero"])
    s.add_assertion(AS["constraints"]); s.add_assertion(AS["is_areo"])

    print("--- Part 1: Verifying ALL op_outputs_are_avc_equiv (Symbolic Core Test for Unio) ---")
    i1_respect = create_intensity_representation("i1_respect")
    j1_respect = create_intensity_representation("j1_respect") 
    i2_respect = create_intensity_representation("i2_respect")
    j2_respect = create_intensity_representation("j2_respect") 
    
    respect_setup = [
        i1_respect["constraints"], j1_respect["constraints"], 
        i2_respect["constraints"], j2_respect["constraints"],
        avc_equiv(i1_respect, i2_respect), avc_equiv(j1_respect, j2_respect)
    ]
    model_vars_for_respect_failure = [i1_respect, j1_respect, i2_respect, j2_respect] 

    res1_sra = define_smart_raw_add_result(i1_respect, j1_respect, "res1_sra_respect", current_omega)
    res2_sra = define_smart_raw_add_result(i2_respect, j2_respect, "res2_sra_respect", current_omega)
    prove_or_find_counterexample(s, "smart_raw_add_outputs_are_avc_equiv",
                                 respect_setup + [res1_sra["definition"], res1_sra["constraints"], res2_sra["definition"], res2_sra["constraints"]],
                                 avc_equiv(res1_sra, res2_sra),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_sra, res2_sra], print_model_on_fail=True)

    res1_rmul = define_raw_mul_result(i1_respect, j1_respect, "res1_rmul_respect", current_omega)
    res2_rmul = define_raw_mul_result(i2_respect, j2_respect, "res2_rmul_respect", current_omega)
    prove_or_find_counterexample(s, "raw_mul_outputs_are_avc_equiv",
                                 respect_setup + [res1_rmul["definition"], res1_rmul["constraints"], res2_rmul["definition"], res2_rmul["constraints"]],
                                 avc_equiv(res1_rmul, res2_rmul),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_rmul, res2_rmul], print_model_on_fail=True)

    res1_rsub = define_raw_sub_from_Unio_Areo_aspect_result(i1_respect, j1_respect, "res1_rsub_respect", current_omega)
    res2_rsub = define_raw_sub_from_Unio_Areo_aspect_result(i2_respect, j2_respect, "res2_rsub_respect", current_omega)
    prove_or_find_counterexample(s, "raw_sub_from_Unio_Areo_aspect_outputs_are_avc_equiv",
                                 respect_setup + [res1_rsub["definition"], res1_rsub["constraints"], res2_rsub["definition"], res2_rsub["constraints"]],
                                 avc_equiv(res1_rsub, res2_rsub),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_rsub, res2_rsub], print_model_on_fail=True)

    res1_rdiv = define_raw_div_result(i1_respect, j1_respect, "res1_rdiv_respect", current_omega)
    res2_rdiv = define_raw_div_result(i2_respect, j2_respect, "res2_rdiv_respect", current_omega)
    prove_or_find_counterexample(s, "raw_div_outputs_are_avc_equiv",
                                 respect_setup + [res1_rdiv["definition"], res1_rdiv["constraints"], res2_rdiv["definition"], res2_rdiv["constraints"]],
                                 avc_equiv(res1_rdiv, res2_rdiv),
                                 model_vars_to_print=model_vars_for_respect_failure + [res1_rdiv, res2_rdiv], print_model_on_fail=True)


    print("\n\n--- Part 2: Explicit Unio Interaction Table (Definitional Checks) ---")
    
    P_unio_table_finite_val_sym = Symbol("P_unio_table_val", solver_INT_TYPE) # Symbolic value for Fp cases
    s.add_assertion(P_unio_table_finite_val_sym > Int(0)) # Ensure this symbolic value is positive for Fp

    op_list = [
        ("smart_raw_add", define_smart_raw_add_result),
        ("raw_mul", define_raw_mul_result),
        ("raw_sub", define_raw_sub_from_Unio_Areo_aspect_result),
        ("raw_div", define_raw_div_result)
    ]
    
    kinds_X_names = ["ZS", "AS", "Fp"]
    kinds_Y_names = ["ZS", "AS", "Fp"]

    for op_name, op_definer in op_list:
        print(f"\n--- Testing Operation: {op_name} with Unio ---")
        for kX_name in kinds_X_names:
            for kY_name in kinds_Y_names:
                s.push() 
                
                x_current = create_intensity_representation(f"x_{op_name}_{kX_name}")
                y_current = create_intensity_representation(f"y_{op_name}_{kY_name}")

                if kX_name == "Fp": make_intensity(s, x_current, "Finite", value=P_unio_table_finite_val_sym)
                else: make_intensity(s, x_current, kX_name)
                
                if kY_name == "Fp": make_intensity(s, y_current, "Finite", value=P_unio_table_finite_val_sym)
                else: make_intensity(s, y_current, kY_name)
                
                actual_res = op_definer(x_current, y_current, f"res_{op_name}_{kX_name}_{kY_name}", current_omega)
                s.add_assertion(actual_res["definition"])
                s.add_assertion(actual_res["constraints"])

                expected_res_target = create_intensity_representation(f"exp_{op_name}_{kX_name}_{kY_name}")
                expected_assertions = [] # List of assertions for the expected state
                
                # --- Define expected_assertions based on op_name, kX_name, kY_name ---
                if op_name == "smart_raw_add":
                    if kX_name == "ZS":
                        if kY_name == "ZS": expected_assertions.extend([expected_res_target["is_zero"], Not(expected_res_target["is_areo"]), Not(expected_res_target["is_finite"])])
                        elif kY_name == "AS": expected_assertions.extend([Not(expected_res_target["is_zero"]), expected_res_target["is_areo"], Not(expected_res_target["is_finite"])])
                        elif kY_name == "Fp": expected_assertions.extend([Not(expected_res_target["is_zero"]), Not(expected_res_target["is_areo"]), expected_res_target["is_finite"], Equals(expected_res_target["val"], y_current["val"])])
                    elif kX_name == "AS":
                        if kY_name == "ZS": expected_assertions.extend([Not(expected_res_target["is_zero"]), expected_res_target["is_areo"], Not(expected_res_target["is_finite"])])
                        elif kY_name == "AS": expected_assertions.extend([Not(expected_res_target["is_zero"]), expected_res_target["is_areo"], Not(expected_res_target["is_finite"])])
                        elif kY_name == "Fp": expected_assertions.extend([Not(expected_res_target["is_zero"]), Not(expected_res_target["is_areo"]), expected_res_target["is_finite"], Equals(expected_res_target["val"], y_current["val"])])
                    elif kX_name == "Fp":
                        if kY_name == "ZS": expected_assertions.extend([Not(expected_res_target["is_zero"]), Not(expected_res_target["is_areo"]), expected_res_target["is_finite"], Equals(expected_res_target["val"], x_current["val"])])
                        elif kY_name == "AS": expected_assertions.extend([Not(expected_res_target["is_zero"]), Not(expected_res_target["is_areo"]), expected_res_target["is_finite"], Equals(expected_res_target["val"], x_current["val"])])
                        elif kY_name == "Fp": s.pop(); continue # Skip Fp+Fp
                
                elif op_name == "raw_mul":
                    if kX_name == "ZS" or kY_name == "ZS": expected_assertions.extend([expected_res_target["is_zero"], Not(expected_res_target["is_areo"]), Not(expected_res_target["is_finite"])])
                    elif kX_name == "AS" and kY_name == "AS": expected_assertions.extend([Not(expected_res_target["is_zero"]), expected_res_target["is_areo"], Not(expected_res_target["is_finite"])])
                    elif (kX_name == "AS" and kY_name == "Fp") or \
                         (kX_name == "Fp" and kY_name == "AS"):
                        # Assumes P_unio_table_finite_val_sym > 0 due to its setup for Fp
                        expected_assertions.extend([Not(expected_res_target["is_zero"]), expected_res_target["is_areo"], Not(expected_res_target["is_finite"])])
                    elif kX_name == "Fp" and kY_name == "Fp": s.pop(); continue 
                
                elif op_name == "raw_sub": 
                    expected_assertions.extend([Not(expected_res_target["is_zero"]), expected_res_target["is_areo"], Not(expected_res_target["is_finite"])])
                
                elif op_name == "raw_div":
                    if kY_name == "ZS" or kY_name == "AS": expected_assertions.extend([Not(expected_res_target["is_zero"]), expected_res_target["is_areo"], Not(expected_res_target["is_finite"])])
                    elif kX_name == "ZS" and kY_name == "Fp": expected_assertions.extend([expected_res_target["is_zero"], Not(expected_res_target["is_areo"]), Not(expected_res_target["is_finite"])])
                    elif kX_name == "AS" and kY_name == "Fp": expected_assertions.extend([Not(expected_res_target["is_zero"]), expected_res_target["is_areo"], Not(expected_res_target["is_finite"])])
                    elif kX_name == "Fp" and kY_name == "Fp": s.pop(); continue 
                
                if not expected_assertions:
                    print(f"    Skipping explicit check for {op_name}({kX_name}, {kY_name}) - No explicit expected assertions defined.")
                    s.pop()
                    continue

                s.push() 
                s.add_assertion(expected_res_target["constraints"])
                for exp_assert in expected_assertions: s.add_assertion(exp_assert)
                
                prove_or_find_counterexample(s, f"Table: {op_name}({kX_name}, {kY_name}) ~ Expected",
                                             [], 
                                             avc_equiv(actual_res, expected_res_target),
                                             model_vars_to_print=[x_current, y_current, actual_res, expected_res_target],
                                             print_model_on_fail=True)
                s.pop() 
                s.pop() 

    # --- Part 3: Specific raw_sub_from_Unio_Areo_aspect with Finite first arg ---
    # ... (Copied from previous correct version, ensures it uses global s) ...
    print("\n\n--- Part 3: Specific Scrutiny of raw_sub_from_Unio_Areo_aspect(Finite, X) ---")
    s.push()
    make_intensity(s, i1, "Finite", value=Symbol("val_for_sub_finite_arg1", solver_INT_TYPE)) 
    make_intensity(s, i2, "ZS") # i2 can be anything, let's use ZS, it's ignored
    
    actual_res_sub_fp_x = define_raw_sub_from_Unio_Areo_aspect_result(i1, i2, "act_sub_fp_x", current_omega)
    s.add_assertion(actual_res_sub_fp_x["definition"]); s.add_assertion(actual_res_sub_fp_x["constraints"])
    
    prove_or_find_counterexample(s, "raw_sub(Finite(p), X) ~ AreoState (confirms definition)",
                                 [], 
                                 avc_equiv(actual_res_sub_fp_x, AS), 
                                 model_vars_to_print=[i1, i2, actual_res_sub_fp_x], print_model_on_fail=True)
    s.pop()

    # --- Part 4: Explicit Finite / Finite Division Details (Re-check from previous script) ---
    print("\n--- Part 4: Re-checking Finite / Finite Division Details ---")
    f1_div = create_intensity_representation("f1_div_detail_re")
    f2_div = create_intensity_representation("f2_div_detail_re")
    exp_div = create_intensity_representation("exp_div_detail_re")

    s.push()
    make_intensity(s, f1_div, "Finite", value=6)
    make_intensity(s, f2_div, "Finite", value=2)
    actual_f6_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f6f2_re", current_omega)
    s.add_assertion(actual_f6_div_f2["definition"]); s.add_assertion(actual_f6_div_f2["constraints"])
    make_intensity(s, exp_div, "Finite", value=3)
    prove_or_find_counterexample(s, "F(6)/F(2)=F(3) (Omega=7) Re-check", [], avc_equiv(actual_f6_div_f2, exp_div)) 
    s.pop()
    
    s.push()
    make_intensity(s, f1_div, "Finite", value=5)
    make_intensity(s, f2_div, "Finite", value=2)
    actual_f5_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f5f2_re", current_omega)
    s.add_assertion(actual_f5_div_f2["definition"]); s.add_assertion(actual_f5_div_f2["constraints"])
    make_intensity(s, exp_div, "AS") 
    prove_or_find_counterexample(s, "F(5)/F(2)=Areo (Omega=7, not exact) Re-check", [], avc_equiv(actual_f5_div_f2, exp_div))
    s.pop()
    
    s.push()
    make_intensity(s, f1_div, "Finite", value=14)
    make_intensity(s, f2_div, "Finite", value=2)
    actual_f14_div_f2 = define_raw_div_result(f1_div, f2_div, "act_f14f2_re", current_omega)
    s.add_assertion(actual_f14_div_f2["definition"]); s.add_assertion(actual_f14_div_f2["constraints"])
    make_intensity(s, exp_div, "AS") 
    prove_or_find_counterexample(s, "F(14)/F(2)=Areo (Omega=7, quotient hits Omega) Re-check", [], avc_equiv(actual_f14_div_f2, exp_div))
    s.pop()

    print("\n====== AVC Unio & Division Pinnacle Scrutiny Complete ======")

