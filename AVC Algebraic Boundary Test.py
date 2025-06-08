from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [3, 5, 7] # Can be expanded; kept smaller for reasonable runtimes
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

def make_intensity_constraints(repr_dict: Dict[str, Any], kind: str, 
                               symbolic_fp_val: FNode = None, 
                               current_omega_smt: FNode = None,
                               fixed_val: int = None) -> List[FNode]:
    """
    Returns a list of assertions to constrain repr_dict to a specific kind and optionally value/range.
    Assumes repr_dict["constraints"] will be asserted separately by the caller if this is for a base symbol.
    """
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
        if not (fixed_val > 0): # This check is for user sanity, PosNat constraint is in repr_dict["constraints"]
            print(f"WARNING for {repr_dict['name']} (in make_intensity_constraints): Fp_fixed value {fixed_val} is not > 0.")
        assertions.extend([
            repr_dict["is_finite"], Not(repr_dict["is_zero"]), Not(repr_dict["is_areo"]),
            Equals(repr_dict["val"], Int(fixed_val))
        ])
    else:
        raise ValueError(f"Unknown kind for make_intensity_constraints: {kind}")
    return assertions

# --- Phase 2: Raw Operations Definitions (Using smart_raw_add) ---
def build_result_definition(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                            res_repr: Dict[str, Any], 
                            op_logic_builder: Callable, 
                            current_omega_smt: FNode) -> FNode:
    return op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)

def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
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

def define_smart_raw_add_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                                result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder, current_omega_smt)
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
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

def define_raw_mul_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                          result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_mul_logic_builder, current_omega_smt)
    return res_repr

def raw_div_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode: 
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

def define_raw_div_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                          result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_div_logic_builder, current_omega_smt)
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
        print(f"Result: UNSAT. Property '{property_name}' is PROVED. ✅")
        proved = True
    else: 
        print(f"Result: SAT. Property '{property_name}' does NOT hold. Counterexample found: ❌")
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
    print("====== AVC Algebraic Boundary Test (Corrected) ======\n")
    
    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        current_omega_smt_loop = Int(omega_py_val)
        print(f"\n\n===== TESTING ALGEBRAIC BOUNDARIES WITH Omega_max_val_nat = {omega_py_val} =====\n")
        s = Solver(name="z3") 

        a = create_intensity_representation(f"a_ab_o{omega_py_val}")
        b = create_intensity_representation(f"b_ab_o{omega_py_val}")
        c = create_intensity_representation(f"c_ab_o{omega_py_val}")
        
        val_a_sym = Symbol(f"val_a_sym_o{omega_py_val}", solver_INT_TYPE)
        val_b_sym = Symbol(f"val_b_sym_o{omega_py_val}", solver_INT_TYPE)
        val_c_sym = Symbol(f"val_c_sym_o{omega_py_val}", solver_INT_TYPE)

        # Assert base constraints for a,b,c once per Omega loop
        s.add_assertion(a["constraints"])
        s.add_assertion(b["constraints"])
        s.add_assertion(c["constraints"])

        # --- 1. Conditional Associativity of smart_raw_add ---
        print(f"--- Conditional Associativity of smart_raw_add (Omega={omega_py_val}) ---")
        
        # Test 1.1: (a+b)+c ~ a+(b+c) IF a,b,c, a+b, b+c, (a+b)+c, a+(b+c) are ALL Fp_sym (no overflow)
        s.push()
        # Constrain a,b,c to be Fp_sym < Omega for this test block
        for constraint in make_intensity_constraints(a, "Fp_sym", val_a_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(b, "Fp_sym", val_b_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(c, "Fp_sym", val_c_sym, current_omega_smt_loop): s.add_assertion(constraint)

        sum_ab_t1 = define_smart_raw_add_result(a, b, f"s_ab_t1_sra_o{omega_py_val}", current_omega_smt_loop)
        lhs_t1 = define_smart_raw_add_result(sum_ab_t1, c, f"lhs_t1_sra_o{omega_py_val}", current_omega_smt_loop)
        sum_bc_t1 = define_smart_raw_add_result(b, c, f"s_bc_t1_sra_o{omega_py_val}", current_omega_smt_loop)
        rhs_t1 = define_smart_raw_add_result(a, sum_bc_t1, f"rhs_t1_sra_o{omega_py_val}", current_omega_smt_loop)
        
        strict_dfi_conditions_assoc = [
            sum_ab_t1["constraints"], sum_ab_t1["is_finite"], sum_ab_t1["val"] < current_omega_smt_loop,
            lhs_t1["constraints"],    lhs_t1["is_finite"],    lhs_t1["val"] < current_omega_smt_loop,
            sum_bc_t1["constraints"], sum_bc_t1["is_finite"], sum_bc_t1["val"] < current_omega_smt_loop,
            rhs_t1["constraints"],    rhs_t1["is_finite"],    rhs_t1["val"] < current_omega_smt_loop,
            sum_ab_t1["definition"], lhs_t1["definition"], sum_bc_t1["definition"], rhs_t1["definition"]
        ]
        prove_or_find_counterexample(s, f"smart_raw_add Assoc (ALL Fp_sym, no overflow) (Omega={omega_py_val})",
                                     strict_dfi_conditions_assoc, 
                                     avc_equiv(lhs_t1, rhs_t1),
                                     model_vars_to_print=[a,b,c,sum_ab_t1,lhs_t1,sum_bc_t1,rhs_t1], print_model_on_fail=True)
        s.pop()

        # Test 1.2: (a+b)+c ~ a+(b+c) IF a,b,c are Fp_sym, AND a+b -> AS (overflows)
        s.push()
        for constraint in make_intensity_constraints(a, "Fp_sym", val_a_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(b, "Fp_sym", val_b_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(c, "Fp_sym", val_c_sym, current_omega_smt_loop): s.add_assertion(constraint)

        sum_ab_t2 = define_smart_raw_add_result(a, b, f"s_ab_t2_sra_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(sum_ab_t2["definition"]); s.add_assertion(sum_ab_t2["constraints"])
        s.add_assertion(sum_ab_t2["is_areo"]) 

        lhs_t2 = define_smart_raw_add_result(sum_ab_t2, c, f"lhs_t2_sra_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(lhs_t2["definition"]); s.add_assertion(lhs_t2["constraints"])
        
        sum_bc_t2 = define_smart_raw_add_result(b, c, f"s_bc_t2_sra_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(sum_bc_t2["definition"]); s.add_assertion(sum_bc_t2["constraints"])

        rhs_t2 = define_smart_raw_add_result(a, sum_bc_t2, f"rhs_t2_sra_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(rhs_t2["definition"]); s.add_assertion(rhs_t2["constraints"])
        
        prove_or_find_counterexample(s, f"smart_raw_add Assoc (a,b,c=Fp_sym; a+b=AS) (Omega={omega_py_val})",
                                     [], 
                                     avc_equiv(lhs_t2, rhs_t2),
                                     model_vars_to_print=[a,b,c,sum_ab_t2,lhs_t2,sum_bc_t2,rhs_t2], print_model_on_fail=True)
        s.pop()
        
        # Test 1.3: The classic non-associativity: a,b,c=Fp_sym; (general symbolic search)
        s.push()
        for constraint in make_intensity_constraints(a, "Fp_sym", val_a_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(b, "Fp_sym", val_b_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(c, "Fp_sym", val_c_sym, current_omega_smt_loop): s.add_assertion(constraint)

        sum_ab_t3 = define_smart_raw_add_result(a, b, f"s_ab_t3_sra_o{omega_py_val}", current_omega_smt_loop)
        lhs_t3 = define_smart_raw_add_result(sum_ab_t3, c, f"lhs_t3_sra_o{omega_py_val}", current_omega_smt_loop)
        sum_bc_t3 = define_smart_raw_add_result(b, c, f"s_bc_t3_sra_o{omega_py_val}", current_omega_smt_loop)
        rhs_t3 = define_smart_raw_add_result(a, sum_bc_t3, f"rhs_t3_sra_o{omega_py_val}", current_omega_smt_loop)
        
        prove_or_find_counterexample(s, f"smart_raw_add Assoc (Fp,Fp,Fp - general symbolic) (Omega={omega_py_val})",
                                     [sum_ab_t3["definition"], sum_ab_t3["constraints"], lhs_t3["definition"], lhs_t3["constraints"],
                                      sum_bc_t3["definition"], sum_bc_t3["constraints"], rhs_t3["definition"], rhs_t3["constraints"]],
                                     avc_equiv(lhs_t3, rhs_t3),
                                     model_vars_to_print=[a,b,c,sum_ab_t3,lhs_t3,sum_bc_t3,rhs_t3], print_model_on_fail=True)
        s.pop()

        # --- 2. Conditional Distributivity of raw_mul over smart_raw_add ---
        print(f"\n--- Conditional Distributivity a*(b+c) (Omega={omega_py_val}) ---")
        # Test 2.1: a,b,c are Fp_sym, ALL intermediate and final results are Fp_sym (no overflow anywhere)
        s.push()
        for constraint in make_intensity_constraints(a, "Fp_sym", val_a_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(b, "Fp_sym", val_b_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(c, "Fp_sym", val_c_sym, current_omega_smt_loop): s.add_assertion(constraint)

        sum_bc_d1 = define_smart_raw_add_result(b, c, f"s_bc_d1_sra_o{omega_py_val}", current_omega_smt_loop)
        lhs_d1 = define_raw_mul_result(a, sum_bc_d1, f"lhs_d1_rm_o{omega_py_val}", current_omega_smt_loop)
        prod_ab_d1 = define_raw_mul_result(a, b, f"p_ab_d1_rm_o{omega_py_val}", current_omega_smt_loop)
        prod_ac_d1 = define_raw_mul_result(a, c, f"p_ac_d1_rm_o{omega_py_val}", current_omega_smt_loop)
        rhs_d1 = define_smart_raw_add_result(prod_ab_d1, prod_ac_d1, f"rhs_d1_sra_o{omega_py_val}", current_omega_smt_loop)

        strict_dfi_conditions_distrib = [
            sum_bc_d1["constraints"], sum_bc_d1["is_finite"], sum_bc_d1["val"] < current_omega_smt_loop,
            lhs_d1["constraints"],    lhs_d1["is_finite"],    lhs_d1["val"] < current_omega_smt_loop,
            prod_ab_d1["constraints"],prod_ab_d1["is_finite"],prod_ab_d1["val"] < current_omega_smt_loop,
            prod_ac_d1["constraints"],prod_ac_d1["is_finite"],prod_ac_d1["val"] < current_omega_smt_loop,
            rhs_d1["constraints"],    rhs_d1["is_finite"],    rhs_d1["val"] < current_omega_smt_loop,
            sum_bc_d1["definition"], lhs_d1["definition"], prod_ab_d1["definition"], prod_ac_d1["definition"], rhs_d1["definition"]
        ]
        prove_or_find_counterexample(s, f"Distributivity (ALL Fp_sym, no overflow) (Omega={omega_py_val})",
                                     strict_dfi_conditions_distrib,
                                     avc_equiv(lhs_d1, rhs_d1),
                                     model_vars_to_print=[a,b,c,sum_bc_d1,lhs_d1,prod_ab_d1,prod_ac_d1,rhs_d1], print_model_on_fail=True)
        s.pop()

        # Test 2.2: a,b,c=Fp_sym; b+c -> AS (overflows), then test a*(AS) vs (a*b)+(a*c)
        s.push()
        for constraint in make_intensity_constraints(a, "Fp_sym", val_a_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(b, "Fp_sym", val_b_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(c, "Fp_sym", val_c_sym, current_omega_smt_loop): s.add_assertion(constraint)

        sum_bc_d2 = define_smart_raw_add_result(b, c, f"s_bc_d2_sra_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(sum_bc_d2["definition"]); s.add_assertion(sum_bc_d2["constraints"])
        s.add_assertion(sum_bc_d2["is_areo"]) 

        lhs_d2 = define_raw_mul_result(a, sum_bc_d2, f"lhs_d2_rm_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(lhs_d2["definition"]); s.add_assertion(lhs_d2["constraints"])

        prod_ab_d2 = define_raw_mul_result(a, b, f"p_ab_d2_rm_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(prod_ab_d2["definition"]); s.add_assertion(prod_ab_d2["constraints"])
        prod_ac_d2 = define_raw_mul_result(a, c, f"p_ac_d2_rm_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(prod_ac_d2["definition"]); s.add_assertion(prod_ac_d2["constraints"])
        rhs_d2 = define_smart_raw_add_result(prod_ab_d2, prod_ac_d2, f"rhs_d2_sra_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(rhs_d2["definition"]); s.add_assertion(rhs_d2["constraints"])
        
        prove_or_find_counterexample(s, f"Distributivity (a,b,c=Fp_sym; b+c=AS) (Omega={omega_py_val})",
                                     [], 
                                     avc_equiv(lhs_d2, rhs_d2),
                                     model_vars_to_print=[a,b,c,sum_bc_d2,lhs_d2,prod_ab_d2,prod_ac_d2,rhs_d2], print_model_on_fail=True)
        s.pop()
        
        # Test 2.3: General Fp,Fp,Fp case for distributivity (expect fail)
        s.push()
        for constraint in make_intensity_constraints(a, "Fp_sym", val_a_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(b, "Fp_sym", val_b_sym, current_omega_smt_loop): s.add_assertion(constraint)
        for constraint in make_intensity_constraints(c, "Fp_sym", val_c_sym, current_omega_smt_loop): s.add_assertion(constraint)

        sum_bc_d3 = define_smart_raw_add_result(b, c, f"s_bc_d3_sra_o{omega_py_val}", current_omega_smt_loop)
        lhs_d3 = define_raw_mul_result(a, sum_bc_d3, f"lhs_d3_rm_o{omega_py_val}", current_omega_smt_loop)
        prod_ab_d3 = define_raw_mul_result(a, b, f"p_ab_d3_rm_o{omega_py_val}", current_omega_smt_loop)
        prod_ac_d3 = define_raw_mul_result(a, c, f"p_ac_d3_rm_o{omega_py_val}", current_omega_smt_loop)
        rhs_d3 = define_smart_raw_add_result(prod_ab_d3, prod_ac_d3, f"rhs_d3_sra_o{omega_py_val}", current_omega_smt_loop)
        
        prove_or_find_counterexample(s, f"Distributivity (Fp,Fp,Fp - general symbolic) (Omega={omega_py_val})",
                                     [sum_bc_d3["definition"], sum_bc_d3["constraints"], lhs_d3["definition"], lhs_d3["constraints"],
                                      prod_ab_d3["definition"], prod_ab_d3["constraints"], prod_ac_d3["definition"], prod_ac_d3["constraints"],
                                      rhs_d3["definition"], rhs_d3["constraints"]],
                                     avc_equiv(lhs_d3, rhs_d3),
                                     model_vars_to_print=[a,b,c,sum_bc_d3,lhs_d3,prod_ab_d3,prod_ac_d3,rhs_d3], print_model_on_fail=True)
        s.pop()

        # --- 3. Refined Cancellation Laws ---
        print(f"\n--- Refined Cancellation Laws (Omega={omega_py_val}) ---")
        # Test 3.1: (a*b)/b ~ a IF a,b are Fp_sym, a*b is Fp_sym (no overflow), 
        # AND (a*b)/b is Fp_sym and its value is a.val
        s.push()
        # a, b are Fp_sym < Omega
        for constraint_a in make_intensity_constraints(a, "Fp_sym", val_a_sym, current_omega_smt_loop): s.add_assertion(constraint_a)
        for constraint_b in make_intensity_constraints(b, "Fp_sym", val_b_sym, current_omega_smt_loop): s.add_assertion(constraint_b)
        s.add_assertion(a["constraints"]); s.add_assertion(b["constraints"])


        prod_ab_c1 = define_raw_mul_result(a,b, f"p_ab_c1_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(prod_ab_c1["definition"]); s.add_assertion(prod_ab_c1["constraints"])
        s.add_assertion(prod_ab_c1["is_finite"]); s.add_assertion(prod_ab_c1["val"] < current_omega_smt_loop) 

        res_div_b_c1 = define_raw_div_result(prod_ab_c1, b, f"res_div_c1_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(res_div_b_c1["definition"]); s.add_assertion(res_div_b_c1["constraints"])
        s.add_assertion(res_div_b_c1["is_finite"]); s.add_assertion(res_div_b_c1["val"] < current_omega_smt_loop) 
        
        s.add_assertion(Equals(res_div_b_c1["val"], a["val"])) 

        prove_or_find_counterexample(s, f"(a*b)/b ~ a (Ideal DFI conditions) (Omega={omega_py_val})",
                                     [], 
                                     avc_equiv(res_div_b_c1, a),
                                     model_vars_to_print=[a,b,prod_ab_c1,res_div_b_c1], print_model_on_fail=True)
        s.pop()

        # Test 3.2: (a*b)/b ~ a IF a,b are Fp_sym, BUT a*b -> AS (overflows)
        s.push()
        for constraint_a in make_intensity_constraints(a, "Fp_sym", val_a_sym, current_omega_smt_loop): s.add_assertion(constraint_a)
        for constraint_b in make_intensity_constraints(b, "Fp_sym", val_b_sym, current_omega_smt_loop): s.add_assertion(constraint_b)
        s.add_assertion(a["constraints"]); s.add_assertion(b["constraints"])


        prod_ab_c2 = define_raw_mul_result(a,b, f"p_ab_c2_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(prod_ab_c2["definition"]); s.add_assertion(prod_ab_c2["constraints"])
        s.add_assertion(prod_ab_c2["is_areo"]) 

        res_div_b_c2 = define_raw_div_result(prod_ab_c2, b, f"res_div_c2_o{omega_py_val}", current_omega_smt_loop)
        s.add_assertion(res_div_b_c2["definition"]); s.add_assertion(res_div_b_c2["constraints"])
        
        prove_or_find_counterexample(s, f"(a*b)/b ~ a (a*b=AS, b=Fp_sym) (Omega={omega_py_val})",
                                     [], 
                                     avc_equiv(res_div_b_c2, a), 
                                     model_vars_to_print=[a,b,prod_ab_c2,res_div_b_c2], print_model_on_fail=True)
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC Algebraic Boundary Test Complete ======")

