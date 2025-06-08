from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any

# --- Configuration ---
GLOBAL_CANONICAL_OMEGA_PY_VARIANTS = [2, 3, 7] # Test with GCA Omegas where behavior might change

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

# --- Phase 3: Helper to Constrain Inputs to Mapped Global Forms ---
def constrain_to_mapped_global_forms(solver: Solver, intensity_repr: Dict[str, Any], 
                                     current_omega_smt: FNode, current_omega_py: int):
    """
    Constrains an intensity_repr to be one of the forms that can result from
    the map_local_to_global_archetype_repr function.
    These are: ZS_G, AS_G, Fp_G(1), Fp_G(2) (if Omega_G >=3), Fp_G(Omega_G-1) (if Omega_G >=2).
    """
    is_ZS_G = intensity_repr["is_zero"]
    is_AS_G = And(intensity_repr["is_areo"], Equals(intensity_repr["val"], current_omega_smt))
    
    possible_fp_conditions = []
    # Fp_G(1)
    if current_omega_py >= 2: # Fp_G(1) is a valid DFI if Omega_G >= 2
        possible_fp_conditions.append(Equals(intensity_repr["val"], Int(1)))
    
    # Fp_G(2)
    if current_omega_py >= 3: # Fp_G(2) is a valid DFI if Omega_G >= 3
        possible_fp_conditions.append(Equals(intensity_repr["val"], Int(2)))
        
    # Fp_G(Omega_G - 1)
    # This value must be > 0. If Omega_G=1, Omega_G-1=0 (not DFI). If Omega_G=2, Omega_G-1=1.
    if current_omega_py >= 2 :
        val_omega_minus_1 = current_omega_py - 1
        if val_omega_minus_1 > 0 : # Ensure it's a potential PosNat DFI value
            # Add only if it's distinct from 1 and 2 already added (or if 1 or 2 are not possible)
            is_distinct_from_1 = (val_omega_minus_1 != 1) if current_omega_py >=2 else True
            is_distinct_from_2 = (val_omega_minus_1 != 2) if current_omega_py >=3 else True
            
            if val_omega_minus_1 == 1 and current_omega_py >= 2: # Already covered by Fp_G(1)
                pass
            elif val_omega_minus_1 == 2 and current_omega_py >= 3: # Already covered by Fp_G(2)
                pass
            else:
                 possible_fp_conditions.append(Equals(intensity_repr["val"], current_omega_smt - Int(1)))

    # Remove duplicates from possible_fp_conditions by converting to string representation then back to FNode
    # This is a bit hacky for SMT but ensures Or is not redundant for identical conditions.
    # A simpler way: build a list of unique integer values, then create Equals conditions.
    unique_fp_values = []
    if current_omega_py >= 2: unique_fp_values.append(1)
    if current_omega_py >= 3 and 2 not in unique_fp_values: unique_fp_values.append(2)
    if current_omega_py >= 2 and (current_omega_py - 1) > 0 and (current_omega_py - 1) not in unique_fp_values:
        unique_fp_values.append(current_omega_py - 1)
    
    final_fp_value_conditions = [Equals(intensity_repr["val"], Int(v)) for v in sorted(list(set(unique_fp_values)))]


    if final_fp_value_conditions:
        is_Specific_Fp_G = And(intensity_repr["is_finite"], Or(final_fp_value_conditions))
        # Also ensure the general finite constraints (val > 0 and val < omega)
        is_Specific_Fp_G = And(is_Specific_Fp_G, 
                               intensity_repr["val"] > Int(0), 
                               intensity_repr["val"] < current_omega_smt)
        solver.add_assertion(Or(is_ZS_G, is_AS_G, is_Specific_Fp_G))
    else: # Only ZS or AS are possible (e.g. Omega_G = 1)
        solver.add_assertion(Or(is_ZS_G, is_AS_G))

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
                     print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC GCA Restricted Input Distributivity Test ======\n")
    
    for global_omega_py in GLOBAL_CANONICAL_OMEGA_PY_VARIANTS:
        if global_omega_py < 2: # Distributivity tests are not meaningful for Omega=1
            continue

        s = Solver(name="z3")
        current_global_omega_smt = Int(global_omega_py)
        print(f"\n\n===== TESTING GCA DISTRIBUTIVITY WITH RESTRICTED INPUTS (GLOBAL OMEGA = {global_omega_py}) =====\n")

        Glob_A = create_intensity_representation(f"Glob_A_G{global_omega_py}")
        Glob_B = create_intensity_representation(f"Glob_B_G{global_omega_py}")
        Glob_C = create_intensity_representation(f"Glob_C_G{global_omega_py}")

        base_setup = [
            Glob_A["constraints"], Glob_B["constraints"], Glob_C["constraints"]
        ]
        s.add_assertions(base_setup) # Assert basic validity once

        # Constrain Glob_A, Glob_B, Glob_C to forms resulting from mapping
        constrain_to_mapped_global_forms(s, Glob_A, current_global_omega_smt, global_omega_py)
        constrain_to_mapped_global_forms(s, Glob_B, current_global_omega_smt, global_omega_py)
        constrain_to_mapped_global_forms(s, Glob_C, current_global_omega_smt, global_omega_py)

        # Define LHS: Glob_A * (Glob_B + Glob_C)
        Sum_BC_G = define_smart_raw_add_global_result(Glob_B, Glob_C, f"sumBC_G{global_omega_py}", current_global_omega_smt)
        LHS_G = define_raw_mul_global_result(Glob_A, Sum_BC_G, f"lhs_G{global_omega_py}", current_global_omega_smt)

        # Define RHS: (Glob_A * Glob_B) + (Glob_A * Glob_C)
        Prod_AB_G = define_raw_mul_global_result(Glob_A, Glob_B, f"prodAB_G{global_omega_py}", current_global_omega_smt)
        Prod_AC_G = define_raw_mul_global_result(Glob_A, Glob_C, f"prodAC_G{global_omega_py}", current_global_omega_smt)
        RHS_G = define_smart_raw_add_global_result(Prod_AB_G, Prod_AC_G, f"rhs_G{global_omega_py}", current_global_omega_smt)
        
        all_operational_assertions = [
            Sum_BC_G["definition"], Sum_BC_G["constraints"],
            LHS_G["definition"], LHS_G["constraints"],
            Prod_AB_G["definition"], Prod_AB_G["constraints"],
            Prod_AC_G["definition"], Prod_AC_G["constraints"],
            RHS_G["definition"], RHS_G["constraints"]
        ]
        
        property_distrib = avc_equiv_canonical(LHS_G, RHS_G)
        
        prove_or_find_counterexample(s, f"GCA Distributivity with Mapped-Like Inputs (Omega_G={global_omega_py})",
                                     all_operational_assertions, # Base setup and input form constraints already added to s
                                     property_distrib,
                                     model_vars_to_print=[Glob_A, Glob_B, Glob_C, Sum_BC_G, LHS_G, Prod_AB_G, Prod_AC_G, RHS_G],
                                     print_model_on_fail=True)
        del s
        print("-" * 80)

    print("\n====== AVC GCA Restricted Input Distributivity Test Complete ======")