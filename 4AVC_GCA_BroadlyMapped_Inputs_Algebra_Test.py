from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
GLOBAL_CANONICAL_OMEGA_PY_VARIANTS = [3, 7] # Test with GCA Omegas where non-standard behavior is expected

# --- Phase 1: Foundational Definitions (Canonical AVC) ---
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

def avc_equiv_canonical(i1_repr: Dict[str, Any], i2_repr: Dict[str, Any]) -> FNode:
    zs_zs = And(i1_repr["is_zero"], i2_repr["is_zero"])
    as_as = And(i1_repr["is_areo"], i2_repr["is_areo"])
    zs_as = And(i1_repr["is_zero"], i2_repr["is_areo"])
    as_zs = And(i1_repr["is_areo"], i2_repr["is_zero"])
    finite_finite_equal_val = And(i1_repr["is_finite"], 
                                  i2_repr["is_finite"], 
                                  Equals(i1_repr["val"], i2_repr["val"]))
    return Or(zs_zs, as_as, zs_as, as_zs, finite_finite_equal_val)

# --- Phase 2: Canonical Raw Operations (Parameterized by Global Omega) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = [] 
    val_sum = i1["val"] + i2["val"] 
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))
    )))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),  
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"]))
    )))
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), 
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
                            Ite(val_sum >= current_omega_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) 
                            )))
    return And(formulas)

def define_smart_raw_add_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any], 
                                       result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
    # Ensure AS_C results have their val conceptually as global_omega_smt
    # This should be intrinsic to the AS_C state representation when is_areo is true.
    # The logic_builder sets is_areo; the create_intensity_representation doesn't know omega.
    # The mapping functions (when mapping *to* AS_C) set the val.
    # For results of operations, if res becomes AS_C, its val should be global_omega_smt.
    # Add constraint: Implies(res_repr["is_areo"], Equals(res_repr["val"], global_omega_smt))
    # This should be added to the list of constraints for res_repr AFTER its definition.
    # Or, more cleanly, handled when an AS_C type is constructed/asserted.
    # For now, let's rely on the fact that val for AS_C is only relevant if it were treated as Fp_C.
    # The primary definer of AS_C value is when it's created/mapped.
    # The logic builders above correctly use current_omega_smt for thresholding.
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"] 
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]), And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]), 
                            Ite(i2["val"] > Int(0), And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])))))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]), 
                            Ite(i1["val"] > Int(0), And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), 
                            Ite(val_prod >= current_omega_smt, And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
    return And(formulas)

def define_raw_mul_global_result(i1_global_repr: Dict[str, Any], i2_global_repr: Dict[str, Any], 
                                 result_name_prefix: str, global_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_global_repr, i2_global_repr, res_repr, global_omega_smt)
    return res_repr

# --- Phase 3: Helper to Constrain Inputs to "Broadly Mapped" Global Forms ---
def constrain_to_broadly_mapped_global_forms(solver: Solver, intensity_repr: Dict[str, Any], 
                                              current_omega_smt: FNode, current_omega_py: int):
    """
    Constrains an intensity_repr to be ZS_G, AS_G, or Fp_G(v) where 1 <= v < Omega_G.
    This simulates the possible outputs of map_local_to_global_archetype_repr_BROADER.
    """
    is_ZS_G = intensity_repr["is_zero"]
    is_AS_G = And(intensity_repr["is_areo"], Equals(intensity_repr["val"], current_omega_smt))
    
    is_valid_Fp_G = And(
        intensity_repr["is_finite"],
        intensity_repr["val"] > Int(0),
        intensity_repr["val"] < current_omega_smt
    )
    # If Omega_G is 1, no Fp_G is possible.
    # If Omega_G is 2, Fp_G must be Fp_G(1).
    # If Omega_G >= 3, Fp_G can be Fp_G(1)...Fp_G(Omega_G-1).
    
    if current_omega_py == 1: # No DFI possible
        solver.add_assertion(Or(is_ZS_G, is_AS_G))
    elif current_omega_py == 2: # DFI can only be Fp_G(1)
        is_Fp_G_val_1 = And(intensity_repr["is_finite"], Equals(intensity_repr["val"], Int(1)))
        solver.add_assertion(Or(is_ZS_G, is_AS_G, is_Fp_G_val_1))
        solver.add_assertion(Implies(is_Fp_G_val_1, And(intensity_repr["val"] > Int(0), intensity_repr["val"] < current_omega_smt))) # Redundant but safe
    else: # Omega_G >= 3
        solver.add_assertion(Or(is_ZS_G, is_AS_G, is_valid_Fp_G))
        # The val for Fp_G is already constrained by its own create_intensity_representation + is_valid_Fp_G

# --- Phase 4: Generic Property Prover ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode], 
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True):
    print(f"--- Testing Property: {property_name} ---")
    solver.push() 
    for assertion in setup_assertions: solver.add_assertion(assertion)
    solver.add_assertion(Not(property_to_prove_true))
        
    proved_universally = False
    if not solver.solve(): 
        print(f"Result: UNSAT. Property '{property_name}' is PROVED universally. ✅")
        proved_universally = True
    else: 
        print(f"Result: SAT. Property '{property_name}' does NOT hold universally. Counterexample found: ❌")
        if print_model_on_fail:
            for var_item in model_vars_to_print:
                if isinstance(var_item, dict) and "name" in var_item : 
                    val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                    is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                    is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode):
                    name_to_print = var_item.symbol_name() if var_item.is_symbol() else f"Expression({str(var_item)})"
                    value_str = "?"
                    try: value_str = str(solver.get_value(var_item))
                    except Exception: value_str = "(Error getting value)"
                    print(f"  {name_to_print}: {value_str}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC GCA Broadly Mapped Inputs Algebra Test ======\n")
    
    for global_omega_py in GLOBAL_CANONICAL_OMEGA_PY_VARIANTS:
        if global_omega_py < 2: # Laws are trivial or DFI doesn't exist for Omega=1
            print(f"\n\n===== SKIPPING GCA OMEGA = {global_omega_py} (Tests more meaningful for Omega >= 2) =====\n")
            continue

        s = Solver(name="z3")
        current_global_omega_smt = Int(global_omega_py)
        print(f"\n\n===== TESTING GCA ALGEBRA WITH BROADLY MAPPED-LIKE INPUTS (GLOBAL OMEGA = {global_omega_py}) =====\n")

        Glob_A = create_intensity_representation(f"Glob_A_G{global_omega_py}bm") # bm for BroadlyMapped
        Glob_B = create_intensity_representation(f"Glob_B_G{global_omega_py}bm")
        Glob_C = create_intensity_representation(f"Glob_C_G{global_omega_py}bm")

        base_setup = [
            Glob_A["constraints"], Glob_B["constraints"], Glob_C["constraints"],
            Implies(Glob_A["is_areo"], Equals(Glob_A["val"], current_global_omega_smt)), # Ensure AS val = Omega
            Implies(Glob_B["is_areo"], Equals(Glob_B["val"], current_global_omega_smt)),
            Implies(Glob_C["is_areo"], Equals(Glob_C["val"], current_global_omega_smt)),
        ]
        s.add_assertions(base_setup)

        # Constrain Glob_A, Glob_B, Glob_C to forms resulting from "Broader" mapping
        constrain_to_broadly_mapped_global_forms(s, Glob_A, current_global_omega_smt, global_omega_py)
        constrain_to_broadly_mapped_global_forms(s, Glob_B, current_global_omega_smt, global_omega_py)
        constrain_to_broadly_mapped_global_forms(s, Glob_C, current_global_omega_smt, global_omega_py)

        # --- Test GCA-BM-1: Additive Associativity ---
        sum_ab_G_bm1 = define_smart_raw_add_global_result(Glob_A, Glob_B, f"sumAB_G{global_omega_py}bm1", current_global_omega_smt)
        lhs_G_bm1 = define_smart_raw_add_global_result(sum_ab_G_bm1, Glob_C, f"lhs_G{global_omega_py}bm1", current_global_omega_smt)
        sum_bc_G_bm1 = define_smart_raw_add_global_result(Glob_B, Glob_C, f"sumBC_G{global_omega_py}bm1", current_global_omega_smt)
        rhs_G_bm1 = define_smart_raw_add_global_result(Glob_A, sum_bc_G_bm1, f"rhs_G{global_omega_py}bm1", current_global_omega_smt)
        
        all_op_assertions_bm1 = [
            sum_ab_G_bm1["definition"], sum_ab_G_bm1["constraints"], Implies(sum_ab_G_bm1["is_areo"], Equals(sum_ab_G_bm1["val"], current_global_omega_smt)),
            lhs_G_bm1["definition"], lhs_G_bm1["constraints"], Implies(lhs_G_bm1["is_areo"], Equals(lhs_G_bm1["val"], current_global_omega_smt)),
            sum_bc_G_bm1["definition"], sum_bc_G_bm1["constraints"], Implies(sum_bc_G_bm1["is_areo"], Equals(sum_bc_G_bm1["val"], current_global_omega_smt)),
            rhs_G_bm1["definition"], rhs_G_bm1["constraints"], Implies(rhs_G_bm1["is_areo"], Equals(rhs_G_bm1["val"], current_global_omega_smt)),
        ]
        property_add_assoc_bm = avc_equiv_canonical(lhs_G_bm1, rhs_G_bm1)
        prove_or_find_counterexample(s, f"GCA-BM-1 Add Assoc with BroadlyMapped Inputs (Omega_G={global_omega_py})",
                                     all_op_assertions_bm1, property_add_assoc_bm,
                                     model_vars_to_print=[Glob_A, Glob_B, Glob_C, sum_ab_G_bm1, lhs_G_bm1, sum_bc_G_bm1, rhs_G_bm1])

        # --- Test GCA-BM-2: Distributivity (Mul over Add) ---
        sum_bc_G_bm2 = define_smart_raw_add_global_result(Glob_B, Glob_C, f"sumBC_G{global_omega_py}bm2", current_global_omega_smt)
        lhs_G_bm2 = define_raw_mul_global_result(Glob_A, sum_bc_G_bm2, f"lhs_G{global_omega_py}bm2", current_global_omega_smt)
        prod_ab_G_bm2 = define_raw_mul_global_result(Glob_A, Glob_B, f"prodAB_G{global_omega_py}bm2", current_global_omega_smt)
        prod_ac_G_bm2 = define_raw_mul_global_result(Glob_A, Glob_C, f"prodAC_G{global_omega_py}bm2", current_global_omega_smt)
        rhs_G_bm2 = define_smart_raw_add_global_result(prod_ab_G_bm2, prod_ac_G_bm2, f"rhs_G{global_omega_py}bm2", current_global_omega_smt)
        
        all_op_assertions_bm2 = [
            sum_bc_G_bm2["definition"], sum_bc_G_bm2["constraints"], Implies(sum_bc_G_bm2["is_areo"], Equals(sum_bc_G_bm2["val"], current_global_omega_smt)),
            lhs_G_bm2["definition"], lhs_G_bm2["constraints"], Implies(lhs_G_bm2["is_areo"], Equals(lhs_G_bm2["val"], current_global_omega_smt)),
            prod_ab_G_bm2["definition"], prod_ab_G_bm2["constraints"], Implies(prod_ab_G_bm2["is_areo"], Equals(prod_ab_G_bm2["val"], current_global_omega_smt)),
            prod_ac_G_bm2["definition"], prod_ac_G_bm2["constraints"], Implies(prod_ac_G_bm2["is_areo"], Equals(prod_ac_G_bm2["val"], current_global_omega_smt)),
            rhs_G_bm2["definition"], rhs_G_bm2["constraints"], Implies(rhs_G_bm2["is_areo"], Equals(rhs_G_bm2["val"], current_global_omega_smt)),
        ]
        property_distrib_bm = avc_equiv_canonical(lhs_G_bm2, rhs_G_bm2)
        prove_or_find_counterexample(s, f"GCA-BM-2 Distrib with BroadlyMapped Inputs (Omega_G={global_omega_py})",
                                     all_op_assertions_bm2, property_distrib_bm,
                                     model_vars_to_print=[Glob_A, Glob_B, Glob_C, sum_bc_G_bm2, lhs_G_bm2, prod_ab_G_bm2, prod_ac_G_bm2, rhs_G_bm2])
        
        del s
        print("-" * 80)

    print("\n====== AVC GCA Broadly Mapped Inputs Algebra Test Complete ======")