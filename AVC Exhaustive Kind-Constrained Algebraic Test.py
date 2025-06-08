from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [3, 5, 7] # Reduced for typical run, can be expanded
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

def make_intensity_kind_constraints(repr_dict: Dict[str, Any], kind: str, 
                                    symbolic_fp_val: FNode = None, 
                                    current_omega_smt: FNode = None) -> List[FNode]:
    """
    Returns a list of assertions to constrain repr_dict to a specific kind.
    If kind is "Fp_sym", it uses symbolic_fp_val and constrains it < current_omega_smt.
    Does NOT assert repr_dict["constraints"] here; that's done by the caller.
    """
    assertions = []
    if kind == "ZS":
        assertions.extend([repr_dict["is_zero"], Not(repr_dict["is_areo"]), Not(repr_dict["is_finite"])])
    elif kind == "AS":
        assertions.extend([repr_dict["is_areo"], Not(repr_dict["is_zero"]), Not(repr_dict["is_finite"])])
    elif kind == "Fp_sym": # Symbolic Finite (a generic DFI < Omega)
        if symbolic_fp_val is None or current_omega_smt is None:
            raise ValueError("symbolic_fp_val and current_omega_smt must be provided for kind 'Fp_sym'")
        assertions.extend([
            repr_dict["is_finite"], Not(repr_dict["is_zero"]), Not(repr_dict["is_areo"]),
            Equals(repr_dict["val"], symbolic_fp_val),
            symbolic_fp_val > Int(0), # Already in constraints, but explicit for clarity
            symbolic_fp_val < current_omega_smt # Key constraint for "non-thresholded Fp"
        ])
    else:
        raise ValueError(f"Unknown kind for make_intensity_kind_constraints: {kind}")
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
    print("====== AVC Exhaustive Kind-Constrained Algebraic Test ======\n")
    
    # === Part 0: Baseline - Re-verify _outputs_are_avc_equiv for add & mul (Default Omega) ===
    print(f"--- Part 0: Baseline Respectfulness Checks (Default Omega = {DEFAULT_OMEGA_MAX_VAL_NAT_PY}) ---")
    s_base = Solver(name="z3")
    current_omega_default = DEFAULT_OMEGA_MAX_VAL_NAT_SMT

    i1_respect_base = create_intensity_representation("i1_respect_ekat") # ekat for ExhaustiveKindAlgebraTest
    j1_respect_base = create_intensity_representation("j1_respect_ekat") 
    i2_respect_base = create_intensity_representation("i2_respect_ekat")
    j2_respect_base = create_intensity_representation("j2_respect_ekat") 
    
    respect_setup_base = [
        i1_respect_base["constraints"], j1_respect_base["constraints"], 
        i2_respect_base["constraints"], j2_respect_base["constraints"],
        avc_equiv(i1_respect_base, i2_respect_base), avc_equiv(j1_respect_base, j2_respect_base)
    ]
    model_vars_respect_base = [i1_respect_base, j1_respect_base, i2_respect_base, j2_respect_base] 

    ops_to_check_respect = [
        ("smart_raw_add", define_smart_raw_add_result),
        ("raw_mul", define_raw_mul_result),
    ]
    for op_name, op_definer in ops_to_check_respect:
        res1 = op_definer(i1_respect_base, j1_respect_base, f"res1_{op_name}_respect_ekat", current_omega_default)
        res2 = op_definer(i2_respect_base, j2_respect_base, f"res2_{op_name}_respect_ekat", current_omega_default)
        prove_or_find_counterexample(s_base, f"{op_name}_outputs_are_avc_equiv",
                                     respect_setup_base + [res1["definition"], res1["constraints"], 
                                                          res2["definition"], res2["constraints"]],
                                     avc_equiv(res1, res2),
                                     model_vars_to_print=model_vars_respect_base + [res1, res2], 
                                     print_model_on_fail=True)
    del s_base

    # === Part 1: Exhaustive Kind-Constrained Algebraic Laws (Looping Omega) ===
    print("\n\n--- Part 1: Exhaustive Kind-Constrained Algebraic Laws ---")
    
    # Symbolic intensities for algebraic laws, kinds will be constrained in the loop
    # Unique names for each operand in each law to avoid SMT variable conflicts if reused carelessly
    a_assoc = create_intensity_representation("a_assoc_ekat")
    b_assoc = create_intensity_representation("b_assoc_ekat")
    c_assoc = create_intensity_representation("c_assoc_ekat")

    a_dist = create_intensity_representation("a_dist_ekat")
    b_dist = create_intensity_representation("b_dist_ekat")
    c_dist = create_intensity_representation("c_dist_ekat")
    
    kinds = ["ZS", "AS", "Fp_sym"]

    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        current_omega_smt_loop = Int(omega_py_val)
        print(f"\n\n===== TESTING ALGEBRAIC LAWS WITH Omega_max_val_nat = {omega_py_val} =====\n")
        s = Solver(name="z3") # Fresh solver for each Omega

        # Symbolic values for Fp_sym kind, constrained per Omega
        # These need to be unique for each symbolic Fp operand if they are distinct
        val_a_fp_sym = Symbol(f"val_a_fp_o{omega_py_val}", solver_INT_TYPE)
        val_b_fp_sym = Symbol(f"val_b_fp_o{omega_py_val}", solver_INT_TYPE)
        val_c_fp_sym = Symbol(f"val_c_fp_o{omega_py_val}", solver_INT_TYPE)

        # --- 1. Associativity of smart_raw_add: (a+b)+c ~ a+(b+c) ---
        print(f"--- Testing Associativity of smart_raw_add (Omega={omega_py_val}) ---")
        for kind_a in kinds:
            for kind_b in kinds:
                for kind_c in kinds:
                    s.push()
                    current_setup = [a_assoc["constraints"], b_assoc["constraints"], c_assoc["constraints"]]
                    current_setup.extend(make_intensity_kind_constraints(a_assoc, kind_a, val_a_fp_sym, current_omega_smt_loop))
                    current_setup.extend(make_intensity_kind_constraints(b_assoc, kind_b, val_b_fp_sym, current_omega_smt_loop))
                    current_setup.extend(make_intensity_kind_constraints(c_assoc, kind_c, val_c_fp_sym, current_omega_smt_loop))

                    sum_ab = define_smart_raw_add_result(a_assoc, b_assoc, f"s_ab_sra_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    lhs = define_smart_raw_add_result(sum_ab, c_assoc, f"lhs_sra_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    sum_bc = define_smart_raw_add_result(b_assoc, c_assoc, f"s_bc_sra_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    rhs = define_smart_raw_add_result(a_assoc, sum_bc, f"rhs_sra_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    
                    property_setup = current_setup + [
                        sum_ab["definition"], sum_ab["constraints"], lhs["definition"], lhs["constraints"],
                        sum_bc["definition"], sum_bc["constraints"], rhs["definition"], rhs["constraints"]
                    ]
                    law_name = f"smart_raw_add Assoc ({kind_a},{kind_b},{kind_c}) (Omega={omega_py_val})"
                    prove_or_find_counterexample(s, law_name, property_setup, avc_equiv(lhs, rhs),
                                                 model_vars_to_print=[a_assoc,b_assoc,c_assoc,sum_ab,lhs,sum_bc,rhs], print_model_on_fail=True)
                    s.pop()

        # --- 2. Associativity of raw_mul: (a*b)*c ~ a*(b*c) ---
        print(f"\n--- Testing Associativity of raw_mul (Omega={omega_py_val}) ---")
        for kind_a in kinds:
            for kind_b in kinds:
                for kind_c in kinds:
                    s.push()
                    current_setup = [a_assoc["constraints"], b_assoc["constraints"], c_assoc["constraints"]] # Reusing a_assoc,b_assoc,c_assoc symbols
                    current_setup.extend(make_intensity_kind_constraints(a_assoc, kind_a, val_a_fp_sym, current_omega_smt_loop))
                    current_setup.extend(make_intensity_kind_constraints(b_assoc, kind_b, val_b_fp_sym, current_omega_smt_loop))
                    current_setup.extend(make_intensity_kind_constraints(c_assoc, kind_c, val_c_fp_sym, current_omega_smt_loop))

                    prod_ab = define_raw_mul_result(a_assoc, b_assoc, f"p_ab_rm_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    lhs = define_raw_mul_result(prod_ab, c_assoc, f"lhs_rm_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    prod_bc = define_raw_mul_result(b_assoc, c_assoc, f"p_bc_rm_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    rhs = define_raw_mul_result(a_assoc, prod_bc, f"rhs_rm_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    
                    property_setup = current_setup + [
                        prod_ab["definition"], prod_ab["constraints"], lhs["definition"], lhs["constraints"],
                        prod_bc["definition"], prod_bc["constraints"], rhs["definition"], rhs["constraints"]
                    ]
                    law_name = f"raw_mul Assoc ({kind_a},{kind_b},{kind_c}) (Omega={omega_py_val})"
                    prove_or_find_counterexample(s, law_name, property_setup, avc_equiv(lhs, rhs),
                                                 model_vars_to_print=[a_assoc,b_assoc,c_assoc,prod_ab,lhs,prod_bc,rhs], print_model_on_fail=True)
                    s.pop()

        # --- 3. Distributivity (Left): a*(b+c) ~ (a*b)+(a*c) ---
        # Using smart_raw_add for '+' and raw_mul for '*'
        print(f"\n--- Testing Distributivity (Left) a*(b+c) (Omega={omega_py_val}) ---")
        for kind_a in kinds:
            for kind_b in kinds:
                for kind_c in kinds:
                    s.push()
                    current_setup = [a_dist["constraints"], b_dist["constraints"], c_dist["constraints"]] # Using a_dist,b_dist,c_dist symbols
                    current_setup.extend(make_intensity_kind_constraints(a_dist, kind_a, val_a_fp_sym, current_omega_smt_loop))
                    current_setup.extend(make_intensity_kind_constraints(b_dist, kind_b, val_b_fp_sym, current_omega_smt_loop))
                    current_setup.extend(make_intensity_kind_constraints(c_dist, kind_c, val_c_fp_sym, current_omega_smt_loop))

                    sum_bc = define_smart_raw_add_result(b_dist, c_dist, f"s_bc_dist_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    lhs = define_raw_mul_result(a_dist, sum_bc, f"lhs_dist_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    
                    prod_ab = define_raw_mul_result(a_dist, b_dist, f"p_ab_dist_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    prod_ac = define_raw_mul_result(a_dist, c_dist, f"p_ac_dist_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    rhs = define_smart_raw_add_result(prod_ab, prod_ac, f"rhs_dist_o{omega_py_val}_{kind_a}{kind_b}{kind_c}", current_omega_smt_loop)
                    
                    property_setup = current_setup + [
                        sum_bc["definition"], sum_bc["constraints"], lhs["definition"], lhs["constraints"],
                        prod_ab["definition"], prod_ab["constraints"], prod_ac["definition"], prod_ac["constraints"],
                        rhs["definition"], rhs["constraints"]
                    ]
                    law_name = f"Distributivity Left ({kind_a},{kind_b},{kind_c}) (Omega={omega_py_val})"
                    prove_or_find_counterexample(s, law_name, property_setup, avc_equiv(lhs, rhs),
                                                 model_vars_to_print=[a_dist,b_dist,c_dist,sum_bc,lhs,prod_ab,prod_ac,rhs], print_model_on_fail=True)
                    s.pop()
        
        del s # Release solver for this Omega value
        print("-" * 80)

    print("\n====== AVC Exhaustive Kind-Constrained Algebraic Test Complete ======")

