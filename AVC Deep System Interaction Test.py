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

# --- smart_raw_add (Primary Addition: AS+Fp -> Fp) ---
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

# --- raw_mul (Unchanged) ---
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

# --- raw_sub_from_Unio_Areo_aspect (Unchanged) ---
def raw_sub_from_Unio_Areo_aspect_logic_builder(i_unio_areo: Dict[str, Any], _i_any: Dict[str, Any], 
                                                res: Dict[str, Any], _current_omega_smt: FNode) -> FNode: 
    return And(Implies(Or(i_unio_areo["is_zero"], i_unio_areo["is_areo"], i_unio_areo["is_finite"]), 
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) 
    ))

def define_raw_sub_from_Unio_Areo_aspect_result(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any], 
                                                result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_sub_from_Unio_Areo_aspect_logic_builder, current_omega_smt)
    return res_repr

# --- raw_div (Unchanged) ---
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
    print("====== AVC Deep System Interaction Test ======\n")
    
    # === Part 1: Baseline - Re-verify _outputs_are_avc_equiv for all ops (Default Omega) ===
    print(f"--- Part 1: Baseline Respectfulness Checks (Default Omega = {DEFAULT_OMEGA_MAX_VAL_NAT_PY}) ---")
    s_base = Solver(name="z3")
    current_omega_default = DEFAULT_OMEGA_MAX_VAL_NAT_SMT

    i1_respect_base = create_intensity_representation("i1_respect_dsit") # dsit for DeepSystemInteractionTest
    j1_respect_base = create_intensity_representation("j1_respect_dsit") 
    i2_respect_base = create_intensity_representation("i2_respect_dsit")
    j2_respect_base = create_intensity_representation("j2_respect_dsit") 
    
    respect_setup_base = [
        i1_respect_base["constraints"], j1_respect_base["constraints"], 
        i2_respect_base["constraints"], j2_respect_base["constraints"],
        avc_equiv(i1_respect_base, i2_respect_base), avc_equiv(j1_respect_base, j2_respect_base)
    ]
    model_vars_respect_base = [i1_respect_base, j1_respect_base, i2_respect_base, j2_respect_base] 

    ops_to_check_respect = [
        ("smart_raw_add", define_smart_raw_add_result),
        ("raw_mul", define_raw_mul_result),
        ("raw_sub_from_Unio_Areo_aspect", define_raw_sub_from_Unio_Areo_aspect_result),
        ("raw_div", define_raw_div_result)
    ]
    for op_name, op_definer in ops_to_check_respect:
        res1 = op_definer(i1_respect_base, j1_respect_base, f"res1_{op_name}_respect_dsit", current_omega_default)
        res2 = op_definer(i2_respect_base, j2_respect_base, f"res2_{op_name}_respect_dsit", current_omega_default)
        prove_or_find_counterexample(s_base, f"{op_name}_outputs_are_avc_equiv",
                                     respect_setup_base + [res1["definition"], res1["constraints"], 
                                                          res2["definition"], res2["constraints"]],
                                     avc_equiv(res1, res2),
                                     model_vars_to_print=model_vars_respect_base + [res1, res2], 
                                     print_model_on_fail=True)
    del s_base

    # === Part 2 & onwards: Parameterized Complex Interaction Tests ===
    print("\n\n--- Part 2+: Parameterized Complex Interaction & Conditional Property Tests ---")
    
    a = create_intensity_representation("a_dsit")
    b = create_intensity_representation("b_dsit")
    c = create_intensity_representation("c_dsit")
    
    ZS = create_intensity_representation("ZS_dsit")
    AS = create_intensity_representation("AS_dsit")
    F1 = create_intensity_representation("F1_dsit") # Finite(1) constant

    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        current_omega_smt_loop = Int(omega_py_val)
        print(f"\n\n===== TESTING INTERACTIONS WITH Omega_max_val_nat = {omega_py_val} =====\n")
        s = Solver(name="z3") # Fresh solver for each Omega

        # Setup symbolic variables and constants for this Omega context
        make_intensity(s, a, "Fp", value=Symbol(f"val_a_o{omega_py_val}", solver_INT_TYPE)) 
        make_intensity(s, b, "Fp", value=Symbol(f"val_b_o{omega_py_val}", solver_INT_TYPE))
        make_intensity(s, c, "Fp", value=Symbol(f"val_c_o{omega_py_val}", solver_INT_TYPE))
        # For some tests, we might re-constrain a,b,c to be ZS or AS.
        # The make_intensity above sets them as symbolic Finite by default for general algebraic tests.

        make_intensity(s, ZS, "ZS")
        make_intensity(s, AS, "AS")
        make_intensity(s, F1, "Fp", value=1)

        base_setup_abc = [a["constraints"], b["constraints"], c["constraints"]] # Already asserted by make_intensity
        base_setup_ab = [a["constraints"], b["constraints"]]
        base_setup_a = [a["constraints"]]

        # --- 2. Complex Cancellation-like Laws ---
        print(f"--- Complex Cancellation-like Laws (Omega={omega_py_val}) ---")
        # 2a. (a * b) / b ~ a  (where b is DFI and suitable for division)
        # This is hard to make fully general due to "clean division" requirement for raw_div.
        # Let's test with b = F1 (Finite(1)), which should always divide cleanly if a*F1 is Fp.
        prod_a_F1 = define_raw_mul_result(a, F1, f"prod_aF1_cancel_o{omega_py_val}", current_omega_smt_loop)
        res_div_F1 = define_raw_div_result(prod_a_F1, F1, f"res_divF1_cancel_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s, f"(a * F(1)) / F(1) ~ a (Omega={omega_py_val})",
                                     base_setup_a + [F1["constraints"], # F1 already made
                                                     prod_a_F1["definition"], prod_a_F1["constraints"],
                                                     res_div_F1["definition"], res_div_F1["constraints"]],
                                     avc_equiv(res_div_F1, a),
                                     model_vars_to_print=[a, F1, prod_a_F1, res_div_F1], print_model_on_fail=True)

        # 2b. (a / b) * b ~ a (where b is DFI, and a/b is DFI)
        # This also requires a/b to be a "clean" DFI. Let b = F1.
        # Then (a / F1) * F1. We expect a/F1 ~ a. So, a * F1 ~ a.
        res_a_div_F1_cancel2 = define_raw_div_result(a, F1, f"res_a_div_F1_cancel2_o{omega_py_val}", current_omega_smt_loop)
        res_mul_F1 = define_raw_mul_result(res_a_div_F1_cancel2, F1, f"res_mulF1_cancel2_o{omega_py_val}", current_omega_smt_loop)
        
        # Add constraint that a/F1 is DFI for this specific test
        s.push() # Create a sub-context for this conditional test
        s.add_assertion(res_a_div_F1_cancel2["is_finite"]) # Condition: a/F1 is DFI
        prove_or_find_counterexample(s, f"(a / F(1)) * F(1) ~ a, if a/F(1) is DFI (Omega={omega_py_val})",
                                     base_setup_a + [F1["constraints"],
                                                     res_a_div_F1_cancel2["definition"], res_a_div_F1_cancel2["constraints"],
                                                     res_mul_F1["definition"], res_mul_F1["constraints"]],
                                     avc_equiv(res_mul_F1, a),
                                     model_vars_to_print=[a, F1, res_a_div_F1_cancel2, res_mul_F1], print_model_on_fail=True)
        s.pop() # Remove the is_finite constraint on res_a_div_F1_cancel2

        # --- 3. Laws Involving Multiple Operations ---
        print(f"\n--- Laws Involving Multiple Operations (Omega={omega_py_val}) ---")
        # 3a. ((a + b) * c) / c ~ (a + b) ? (if c=F1)
        # Using smart_raw_add for '+'
        sum_ab_multi = define_smart_raw_add_result(a,b, f"sum_ab_multi_o{omega_py_val}", current_omega_smt_loop)
        prod_sum_F1 = define_raw_mul_result(sum_ab_multi, F1, f"prod_sumF1_multi_o{omega_py_val}", current_omega_smt_loop)
        res_div_F1_multi = define_raw_div_result(prod_sum_F1, F1, f"res_divF1_multi_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s, f"((a+b)*F(1))/F(1) ~ (a+b) (Omega={omega_py_val})",
                                     base_setup_ab + [F1["constraints"],
                                                      sum_ab_multi["definition"], sum_ab_multi["constraints"],
                                                      prod_sum_F1["definition"], prod_sum_F1["constraints"],
                                                      res_div_F1_multi["definition"], res_div_F1_multi["constraints"]],
                                     avc_equiv(res_div_F1_multi, sum_ab_multi),
                                     model_vars_to_print=[a,b,F1,sum_ab_multi,prod_sum_F1,res_div_F1_multi], print_model_on_fail=True)

        # 3b. raw_sub_from_Unio_Areo_aspect(Unio, a*b) ~ AreoState
        # Let Unio be ZS for this test
        prod_ab_sub = define_raw_mul_result(a,b, f"prod_ab_sub_o{omega_py_val}", current_omega_smt_loop)
        res_sub_prod = define_raw_sub_from_Unio_Areo_aspect_result(ZS, prod_ab_sub, f"res_sub_prod_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s, f"raw_sub(ZS, a*b) ~ AS (Omega={omega_py_val})",
                                     base_setup_ab + [ZS["constraints"], AS["constraints"], # ZS, AS already made
                                                      prod_ab_sub["definition"], prod_ab_sub["constraints"],
                                                      res_sub_prod["definition"], res_sub_prod["constraints"]],
                                     avc_equiv(res_sub_prod, AS),
                                     model_vars_to_print=[a,b,ZS,AS,prod_ab_sub,res_sub_prod], print_model_on_fail=True)
        
        # --- 4. Exploring "Almost-Properties" for smart_raw_add Associativity ---
        print(f"\n--- Conditional Associativity for smart_raw_add (Omega={omega_py_val}) ---")
        # Test (ZS + b) + c ~ ZS + (b + c)
        s.push() # Context for this specific test
        # b and c are already symbolic Finites from the loop setup
        # ZS is globally defined in solver s for this Omega iteration
        
        sum_zs_b = define_smart_raw_add_result(ZS, b, f"sum_zsb_almost_o{omega_py_val}", current_omega_smt_loop)
        lhs_almost_assoc1 = define_smart_raw_add_result(sum_zs_b, c, f"lhs_almost1_o{omega_py_val}", current_omega_smt_loop)
        sum_b_c_almost = define_smart_raw_add_result(b, c, f"sum_bc_almost_o{omega_py_val}", current_omega_smt_loop)
        rhs_almost_assoc1 = define_smart_raw_add_result(ZS, sum_b_c_almost, f"rhs_almost1_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s, f"(ZS+b)+c ~ ZS+(b+c) (Omega={omega_py_val})",
                                     [sum_zs_b["definition"], sum_zs_b["constraints"],
                                      lhs_almost_assoc1["definition"], lhs_almost_assoc1["constraints"],
                                      sum_b_c_almost["definition"], sum_b_c_almost["constraints"],
                                      rhs_almost_assoc1["definition"], rhs_almost_assoc1["constraints"]], # b,c,ZS constraints already in s
                                     avc_equiv(lhs_almost_assoc1, rhs_almost_assoc1),
                                     model_vars_to_print=[ZS,b,c,sum_zs_b,lhs_almost_assoc1,sum_b_c_almost,rhs_almost_assoc1], print_model_on_fail=True)
        s.pop()

        # Test (AS + b) + c ~ AS + (b + c)
        s.push()
        sum_as_b = define_smart_raw_add_result(AS, b, f"sum_asb_almost_o{omega_py_val}", current_omega_smt_loop)
        lhs_almost_assoc2 = define_smart_raw_add_result(sum_as_b, c, f"lhs_almost2_o{omega_py_val}", current_omega_smt_loop)
        # sum_b_c_almost already defined if we assume b,c are same symbolic Finites
        rhs_almost_assoc2 = define_smart_raw_add_result(AS, sum_b_c_almost, f"rhs_almost2_o{omega_py_val}", current_omega_smt_loop)
        prove_or_find_counterexample(s, f"(AS+b)+c ~ AS+(b+c) (Omega={omega_py_val})",
                                     [sum_as_b["definition"], sum_as_b["constraints"],
                                      lhs_almost_assoc2["definition"], lhs_almost_assoc2["constraints"],
                                      sum_b_c_almost["definition"], sum_b_c_almost["constraints"], # Re-assert for clarity if needed, or rely on previous definition if b,c are same
                                      rhs_almost_assoc2["definition"], rhs_almost_assoc2["constraints"]],
                                     avc_equiv(lhs_almost_assoc2, rhs_almost_assoc2),
                                     model_vars_to_print=[AS,b,c,sum_as_b,lhs_almost_assoc2,sum_b_c_almost,rhs_almost_assoc2], print_model_on_fail=True)
        s.pop()
        
        del s # Release solver for this Omega value
        print("-" * 80)

    print("\n====== AVC Deep System Interaction Test Complete ======")

