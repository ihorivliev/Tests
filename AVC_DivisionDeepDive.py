from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [3, 5, 7, 10] 
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

# --- Phase 2: Raw Operations Definitions (raw_div and raw_mul needed) ---
def build_result_definition(i1_repr, i2_repr, res_repr, op_logic_builder, current_omega_smt):
    return op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)

def raw_mul_logic_builder(i1, i2, res, current_omega_smt): # Copied for (a*b)/b tests
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
                                 print_model_on_fail: bool = True ):
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
    print("====== AVC Division Deep Dive & Algebraic Properties ======\n")
    
    # --- Loop for Parameterized Omega Tests ---
    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        current_omega_smt = Int(omega_py_val)
        print(f"\n\n===== TESTING DIVISION ALGEBRA WITH Omega_max_val_nat = {omega_py_val} =====\n")
        
        s = Solver(name="z3") # Fresh solver for each Omega

        # Symbolic Intensities for tests within this Omega loop
        a = create_intensity_representation(f"a_o{omega_py_val}")
        b = create_intensity_representation(f"b_o{omega_py_val}")
        c = create_intensity_representation(f"c_o{omega_py_val}")
        
        # Constants for Unio representation
        ZS_const = create_intensity_representation(f"ZS_o{omega_py_val}")
        AS_const = create_intensity_representation(f"AS_o{omega_py_val}")
        s.add_assertion(ZS_const["constraints"]); s.add_assertion(ZS_const["is_zero"])
        s.add_assertion(AS_const["constraints"]); s.add_assertion(AS_const["is_areo"])
        
        # Base setup for symbolic variables a, b, c to be valid intensities
        base_setup_abc = [a["constraints"], b["constraints"], c["constraints"]]
        base_setup_ab = [a["constraints"], b["constraints"]]
        base_setup_a = [a["constraints"]]

        # --- 1. Re-confirm Non-Associativity of raw_div (from AVC_DivisionAlgebra.py) ---
        res_ab_div = define_raw_div_result(a, b, f"res_ab_div_assoc_o{omega_py_val}", current_omega_smt)
        lhs_final_div = define_raw_div_result(res_ab_div, c, f"lhs_final_div_assoc_o{omega_py_val}", current_omega_smt)
        res_bc_div = define_raw_div_result(b, c, f"res_bc_div_assoc_o{omega_py_val}", current_omega_smt)
        rhs_final_div = define_raw_div_result(a, res_bc_div, f"rhs_final_div_assoc_o{omega_py_val}", current_omega_smt)
        
        associativity_setup = base_setup_abc + [
            res_ab_div["definition"], res_ab_div["constraints"],
            lhs_final_div["definition"], lhs_final_div["constraints"],
            res_bc_div["definition"], res_bc_div["constraints"],
            rhs_final_div["definition"], rhs_final_div["constraints"]
        ]
        prove_or_find_counterexample(s, 
                                     f"Associativity of raw_div (Omega={omega_py_val})",
                                     associativity_setup,
                                     avc_equiv(lhs_final_div, rhs_final_div),
                                     model_vars_to_print=[a, b, c, res_ab_div, lhs_final_div, res_bc_div, rhs_final_div],
                                     print_model_on_fail=True)

        # --- 2. Commutativity of raw_div ---
        # Property: a / b ~ b / a. Expect FAIL.
        res_a_div_b = define_raw_div_result(a, b, f"res_a_div_b_comm_o{omega_py_val}", current_omega_smt)
        res_b_div_a = define_raw_div_result(b, a, f"res_b_div_a_comm_o{omega_py_val}", current_omega_smt)
        commutativity_div_setup = base_setup_ab + [
            res_a_div_b["definition"], res_a_div_b["constraints"],
            res_b_div_a["definition"], res_b_div_a["constraints"]
        ]
        prove_or_find_counterexample(s,
                                     f"Commutativity of raw_div (Omega={omega_py_val})",
                                     commutativity_div_setup,
                                     avc_equiv(res_a_div_b, res_b_div_a),
                                     model_vars_to_print=[a,b,res_a_div_b, res_b_div_a],
                                     print_model_on_fail=True)

        # --- 3. Identity Element for raw_div ---
        # 3a. Right Identity: a / Finite(1) ~ a ?
        F1_const = create_intensity_representation(f"F1_const_o{omega_py_val}")
        s.add_assertion(F1_const["constraints"]); s.add_assertion(F1_const["is_finite"]); s.add_assertion(Equals(F1_const["val"], Int(1)))
        
        res_a_div_F1 = define_raw_div_result(a, F1_const, f"res_a_div_F1_o{omega_py_val}", current_omega_smt)
        identity_div_setup = base_setup_a + [
            F1_const["constraints"], # Already asserted but good practice for setup list
            res_a_div_F1["definition"], res_a_div_F1["constraints"]
        ]
        prove_or_find_counterexample(s,
                                     f"Right Identity F(1) for raw_div: a/F(1) ~ a (Omega={omega_py_val})",
                                     identity_div_setup,
                                     avc_equiv(res_a_div_F1, a),
                                     model_vars_to_print=[a, F1_const, res_a_div_F1],
                                     print_model_on_fail=True)

        # --- 4. Interaction of raw_div with raw_mul (Cancellation-like) ---
        # 4a. (a*b)/b ~ a (if b !~ ZeroState)? Expect FAIL.
        prod_ab_cancel = define_raw_mul_result(a,b, f"prod_ab_cancel_o{omega_py_val}", current_omega_smt)
        res_prod_div_b = define_raw_div_result(prod_ab_cancel, b, f"res_prod_div_b_o{omega_py_val}", current_omega_smt)
        
        # Premise: b is not ZeroState (and not AreoState, so b is Finite for a meaningful divisor)
        premise_b_not_unio_cancel = And(b["is_finite"]) # b.val > 0 is in b.constraints
                                         
        cancellation1_setup = base_setup_ab + [
            prod_ab_cancel["definition"], prod_ab_cancel["constraints"],
            res_prod_div_b["definition"], res_prod_div_b["constraints"],
            premise_b_not_unio_cancel
        ]
        prove_or_find_counterexample(s,
                                     f"Mul-Div Cancellation 1: (a*b)/b ~ a (b is DFI) (Omega={omega_py_val})",
                                     cancellation1_setup,
                                     avc_equiv(res_prod_div_b, a),
                                     model_vars_to_print=[a,b,prod_ab_cancel,res_prod_div_b],
                                     print_model_on_fail=True)

        # 4b. (a/b)*b ~ a (if b !~ ZeroState and a/b is Finite)? Expect FAIL.
        res_a_div_b_cancel = define_raw_div_result(a,b, f"res_a_div_b_cancel_o{omega_py_val}", current_omega_smt)
        res_div_mul_b = define_raw_mul_result(res_a_div_b_cancel, b, f"res_div_mul_b_o{omega_py_val}", current_omega_smt)

        # Premise: b is Finite AND a/b is Finite
        premise_b_and_a_div_b_finite = And(b["is_finite"], res_a_div_b_cancel["is_finite"])

        cancellation2_setup = base_setup_ab + [
            res_a_div_b_cancel["definition"], res_a_div_b_cancel["constraints"],
            res_div_mul_b["definition"], res_div_mul_b["constraints"],
            premise_b_and_a_div_b_finite
        ]
        prove_or_find_counterexample(s,
                                     f"Div-Mul Cancellation 2: (a/b)*b ~ a (b, a/b are DFI) (Omega={omega_py_val})",
                                     cancellation2_setup,
                                     avc_equiv(res_div_mul_b, a),
                                     model_vars_to_print=[a,b,res_a_div_b_cancel,res_div_mul_b],
                                     print_model_on_fail=True)

        # --- 5. More Complex Unio Interactions with Division ---
        # 5a. a / (b/ZS)  (where b/ZS becomes AS, so effectively a/AS)
        # Expected: a / AS. If a=ZS -> ZS/AS -> AS. If a=AS -> AS/AS -> AS. If a=Fp -> Fp/AS -> AS.
        # So, overall expected is AS.
        
        # temp_b_div_zs becomes AS
        temp_b_div_zs = define_raw_div_result(b, ZS_const, f"temp_b_div_zs_o{omega_py_val}", current_omega_smt)
        final_res_a_div_b_div_zs = define_raw_div_result(a, temp_b_div_zs, f"final_a_div_temp_o{omega_py_val}", current_omega_smt)

        complex_unio_setup1 = base_setup_ab + [ # a and b must be valid
            temp_b_div_zs["definition"], temp_b_div_zs["constraints"], # temp must be valid result of b/ZS
            final_res_a_div_b_div_zs["definition"], final_res_a_div_b_div_zs["constraints"] # final must be valid
        ]
        prove_or_find_counterexample(s,
                                     f"Complex Unio Div 1: a/(b/ZS) ~ AS (Omega={omega_py_val})",
                                     complex_unio_setup1,
                                     avc_equiv(final_res_a_div_b_div_zs, AS_const),
                                     model_vars_to_print=[a,b,temp_b_div_zs,final_res_a_div_b_div_zs],
                                     print_model_on_fail=True)

        del s # Release solver for this Omega value
        print("-" * 50)


    print("\n====== AVC Division Deep Dive Complete ======")

