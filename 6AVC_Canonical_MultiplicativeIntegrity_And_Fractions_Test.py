# Script Name: AVC_Canonical_MultiplicativeIntegrity_And_Fractions_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple, Optional

# --- Configuration ---
OMEGA_VARIANTS_TO_TEST = [2, 3, 5, 7, 12] 

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

# --- Phase 2: Canonical Raw Operations Definitions ---
def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"]
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]),
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]),
                            Ite(i2["val"] > Int(0),
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))
                               )))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]),
                            Ite(i1["val"] > Int(0),
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))
                               )))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_prod >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                Ite(val_prod <= Int(0), 
                                    And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
                                    And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod))
                                   )
                               )))
    return And(formulas)

def raw_div_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    q_sym = Symbol(f"{res['name']}_q_div", solver_INT_TYPE)
    rem_sym = Symbol(f"{res['name']}_rem_div", solver_INT_TYPE)
    divisor_is_unio = Or(i2["is_zero"], i2["is_areo"])
    formulas.append(Implies(divisor_is_unio,
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt))
    ))
    formulas.append(Implies(And(Not(divisor_is_unio), i2["is_finite"]),
        Or(
            And(i1["is_zero"],
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            And(i1["is_areo"],
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
            And(i1["is_finite"],
                And(Equals(i1["val"], q_sym * i2["val"] + rem_sym),
                    rem_sym >= Int(0),
                    rem_sym < i2["val"]),
                Ite(And(Equals(rem_sym, Int(0)), q_sym > Int(0)),
                    Ite(q_sym >= current_omega_smt,
                        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], q_sym))
                    ),
                    And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt))
                )
            )
        )
    ))
    return And(formulas)

def define_canonical_op_result(op_logic_builder_func: Callable,
                               i1_canon_repr: Dict[str, Any], i2_canon_repr: Optional[Dict[str, Any]], 
                               result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    # Ensure i2_canon_repr is not None for binary operations.
    # This check is basic; a more robust way might involve inspecting op_logic_builder_func's signature if possible,
    # or having separate definers for unary/binary. For this script, all ops are binary.
    if i2_canon_repr is None:
        raise ValueError(f"i2_canon_repr cannot be None for binary operation builder {op_logic_builder_func.__name__}")
        
    res_repr["definition"] = op_logic_builder_func(i1_canon_repr, i2_canon_repr, res_repr, current_omega_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_smt)))
    return res_repr

# --- Phase 3: Generic Property Prover ---
def prove_or_find_counterexample(solver: Solver, property_name: str, setup_assertions: List[FNode],
                                 property_to_prove_true: FNode, model_vars_to_print: List[Any] = [],
                                 print_model_on_fail: bool = True,
                                 op_result_dicts_for_debug: List[Dict[str,Any]] = []):
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
            printed_item_names = set() # To avoid re-printing the same FNode or dict via op_result_dicts_for_debug
            
            for var_item in model_vars_to_print:
                if isinstance(var_item, FNode) and var_item.is_symbol():
                    if var_item.symbol_name() not in printed_item_names:
                        try: print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
                        except Exception: print(f"  {var_item.symbol_name()}: (Error getting value or not in model)")
                        printed_item_names.add(var_item.symbol_name())
                elif isinstance(var_item, dict) and "name" in var_item:
                    if var_item['name'] not in printed_item_names:
                        val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                        is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                        is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                        is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                        print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                        printed_item_names.add(var_item['name'])

            if op_result_dicts_for_debug:
                print("  DEBUG Intermediate Canonical Operation Results in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "name" in op_res_dict:
                        if op_res_dict['name'] not in printed_item_names: # Avoid re-printing
                            val_str_node = f"V={solver.get_value(op_res_dict['val'])}" if op_res_dict['val'] in solver.get_model() else "V=?"
                            is_z_str_node = f"Z={solver.get_value(op_res_dict['is_zero'])}" if op_res_dict['is_zero'] in solver.get_model() else "Z=?"
                            is_a_str_node = f"A={solver.get_value(op_res_dict['is_areo'])}" if op_res_dict['is_areo'] in solver.get_model() else "A=?"
                            is_f_str_node = f"F={solver.get_value(op_res_dict['is_finite'])}" if op_res_dict['is_finite'] in solver.get_model() else "F=?"
                            print(f"    {op_res_dict['name']} (Canon_Res): {is_z_str_node}, {is_a_str_node}, {is_f_str_node}, {val_str_node}")
                            # printed_item_names.add(op_res_dict['name']) # Optionally add here if these are primary objects of interest
    solver.pop()
    print("-" * 70)
    return proved_universally

# --- Phase 4: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Canonical Multiplicative Integrity and Fractions Test ======\n")

    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        s = Solver(name="z3")
        current_omega_smt = Int(omega_py_val)
        print(f"\n\n===== CANONICAL MULTIPLICATIVE INTEGRITY TESTS WITH OMEGA = {omega_py_val} =====\n")

        A = create_intensity_representation(f"A_O{omega_py_val}")
        B = create_intensity_representation(f"B_O{omega_py_val}")
        C = create_intensity_representation(f"C_O{omega_py_val}")
        D = create_intensity_representation(f"D_O{omega_py_val}")

        all_inputs = [A, B, C, D]
        base_constraints = []
        for inp_repr in all_inputs:
            base_constraints.append(inp_repr["constraints"])
            base_constraints.append(Implies(inp_repr["is_areo"], Equals(inp_repr["val"], current_omega_smt)))
            if omega_py_val > 1:
                base_constraints.append(Implies(inp_repr["is_finite"], And(inp_repr["val"] > Int(0), inp_repr["val"] < current_omega_smt)))
            else: 
                base_constraints.append(Not(inp_repr["is_finite"]))
        
        s.add_assertions(base_constraints)

        # --- MICF-1: (A * B) / B ~ A ---
        s.push()
        s.add_assertion(B["is_finite"]) # B must be Fp for division
        if omega_py_val == 1: s.add_assertion(FALSE()) # Cannot satisfy B is Fp if omega=1

        prod_ab_micf1 = define_canonical_op_result(raw_mul_logic_builder, A, B, f"pAB_micf1", current_omega_smt)
        lhs_micf1 = define_canonical_op_result(raw_div_logic_builder, prod_ab_micf1, B, f"lhs_micf1", current_omega_smt)
        prop_micf1 = avc_equiv_canonical(lhs_micf1, A)
        setup_micf1 = [prod_ab_micf1["definition"], prod_ab_micf1["constraints"], 
                       lhs_micf1["definition"], lhs_micf1["constraints"]]
        prove_or_find_counterexample(s, f"MICF-1 (A*B_fp)/B_fp ~ A (Omega={omega_py_val})", setup_micf1, prop_micf1,
                                     [A,B,prod_ab_micf1,lhs_micf1]) # op_result_dicts_for_debug not needed if they are in model_vars
        s.pop()

        # --- MICF-2a: (A / B) * B ~ A (General A) ---
        s.push()
        s.add_assertion(B["is_finite"])
        if omega_py_val == 1: s.add_assertion(FALSE())

        div_ab_micf2a = define_canonical_op_result(raw_div_logic_builder, A, B, f"dAB_micf2a", current_omega_smt)
        lhs_micf2a = define_canonical_op_result(raw_mul_logic_builder, div_ab_micf2a, B, f"lhs_micf2a", current_omega_smt)
        prop_micf2a = avc_equiv_canonical(lhs_micf2a, A)
        setup_micf2a = [div_ab_micf2a["definition"], div_ab_micf2a["constraints"], 
                        lhs_micf2a["definition"], lhs_micf2a["constraints"]]
        prove_or_find_counterexample(s, f"MICF-2a (A/B_fp)*B_fp ~ A (Omega={omega_py_val})", setup_micf2a, prop_micf2a,
                                     [A,B,div_ab_micf2a,lhs_micf2a])
        s.pop()

        # --- MICF-2b: (A / B) * B ~ A (IF A/B is Fp_C) ---
        s.push()
        s.add_assertion(B["is_finite"])
        if omega_py_val == 1: s.add_assertion(FALSE())
        
        div_ab_micf2b = define_canonical_op_result(raw_div_logic_builder, A, B, f"dAB_micf2b", current_omega_smt)
        s.add_assertion(div_ab_micf2b["is_finite"]) # Premise: A/B is Fp
        if omega_py_val == 1 : s.add_assertion(FALSE()) 
        elif omega_py_val > 1: s.add_assertion(div_ab_micf2b["val"] < current_omega_smt)

        lhs_micf2b = define_canonical_op_result(raw_mul_logic_builder, div_ab_micf2b, B, f"lhs_micf2b", current_omega_smt)
        prop_micf2b = avc_equiv_canonical(lhs_micf2b, A)
        setup_micf2b = [div_ab_micf2b["definition"], div_ab_micf2b["constraints"], 
                        lhs_micf2b["definition"], lhs_micf2b["constraints"]]
        prove_or_find_counterexample(s, f"MICF-2b (A/B_fp)*B_fp ~ A IF A/B_fp is Fp (Omega={omega_py_val})", setup_micf2b, prop_micf2b,
                                     [A,B,div_ab_micf2b,lhs_micf2b])
        s.pop()

        # --- MICF-3: A * (B / C) ~ (A * B) / C ---
        s.push()
        s.add_assertion(C["is_finite"]) 
        if omega_py_val == 1: s.add_assertion(FALSE())

        div_bc_micf3 = define_canonical_op_result(raw_div_logic_builder, B, C, f"dBC_micf3", current_omega_smt)
        lhs_micf3 = define_canonical_op_result(raw_mul_logic_builder, A, div_bc_micf3, f"lhs_micf3", current_omega_smt)
        prod_ab_micf3 = define_canonical_op_result(raw_mul_logic_builder, A, B, f"pAB_micf3", current_omega_smt)
        rhs_micf3 = define_canonical_op_result(raw_div_logic_builder, prod_ab_micf3, C, f"rhs_micf3", current_omega_smt)
        prop_micf3 = avc_equiv_canonical(lhs_micf3, rhs_micf3)
        setup_micf3 = ([div_bc_micf3["definition"], div_bc_micf3["constraints"], lhs_micf3["definition"], lhs_micf3["constraints"],
                       prod_ab_micf3["definition"], prod_ab_micf3["constraints"], rhs_micf3["definition"], rhs_micf3["constraints"]])
        prove_or_find_counterexample(s, f"MICF-3 A*(B/C_fp) ~ (A*B)/C_fp (Omega={omega_py_val})", setup_micf3, prop_micf3,
                                     [A,B,C,lhs_micf3,rhs_micf3,div_bc_micf3,prod_ab_micf3])
        s.pop()

        # --- MICF-5: A / (B / C) ~ (A * C) / B --- 
        s.push()
        s.add_assertion(B["is_finite"]) 
        s.add_assertion(C["is_finite"]) 
        if omega_py_val == 1: s.add_assertion(FALSE())

        div_bc_micf5 = define_canonical_op_result(raw_div_logic_builder, B, C, f"dBC_micf5", current_omega_smt)
        s.add_assertion(div_bc_micf5["is_finite"]) # Premise: B/C is Fp for non-trivial outer division
        if omega_py_val == 1: s.add_assertion(FALSE())
        elif omega_py_val > 1 : s.add_assertion(div_bc_micf5["val"] < current_omega_smt)

        lhs_micf5 = define_canonical_op_result(raw_div_logic_builder, A, div_bc_micf5, f"lhs_micf5", current_omega_smt)
        prod_ac_micf5 = define_canonical_op_result(raw_mul_logic_builder, A, C, f"pAC_micf5", current_omega_smt)
        rhs_micf5 = define_canonical_op_result(raw_div_logic_builder, prod_ac_micf5, B, f"rhs_micf5", current_omega_smt)
        prop_micf5 = avc_equiv_canonical(lhs_micf5, rhs_micf5)
        setup_micf5 = ([div_bc_micf5["definition"], div_bc_micf5["constraints"], lhs_micf5["definition"], lhs_micf5["constraints"],
                       prod_ac_micf5["definition"], prod_ac_micf5["constraints"], rhs_micf5["definition"], rhs_micf5["constraints"]])
        prove_or_find_counterexample(s, f"MICF-5 A/(B/C) ~ (A*C)/B (B,C,B/C are Fp) (Omega={omega_py_val})", setup_micf5, prop_micf5,
                                     [A,B,C,lhs_micf5,rhs_micf5,div_bc_micf5,prod_ac_micf5])
        s.pop()

        # --- MICF-6: (A/B) * (C/D) ~ (A*C) / (B*D) ---
        s.push()
        s.add_assertion(B["is_finite"]) 
        s.add_assertion(D["is_finite"]) 
        if omega_py_val == 1: s.add_assertion(FALSE())

        div_ab_micf6 = define_canonical_op_result(raw_div_logic_builder, A, B, f"dAB_micf6", current_omega_smt)
        div_cd_micf6 = define_canonical_op_result(raw_div_logic_builder, C, D, f"dCD_micf6", current_omega_smt)
        lhs_micf6 = define_canonical_op_result(raw_mul_logic_builder, div_ab_micf6, div_cd_micf6, f"lhs_micf6", current_omega_smt)

        prod_ac_micf6 = define_canonical_op_result(raw_mul_logic_builder, A, C, f"pAC_micf6", current_omega_smt)
        prod_bd_micf6 = define_canonical_op_result(raw_mul_logic_builder, B, D, f"pBD_micf6", current_omega_smt)
        s.add_assertion(prod_bd_micf6["is_finite"]) # Premise: B*D is Fp for RHS denominator
        if omega_py_val == 1: s.add_assertion(FALSE())
        elif omega_py_val > 1: s.add_assertion(prod_bd_micf6["val"] < current_omega_smt)

        rhs_micf6 = define_canonical_op_result(raw_div_logic_builder, prod_ac_micf6, prod_bd_micf6, f"rhs_micf6", current_omega_smt)
        prop_micf6 = avc_equiv_canonical(lhs_micf6, rhs_micf6)
        setup_micf6 = ([div_ab_micf6["definition"], div_ab_micf6["constraints"], div_cd_micf6["definition"], div_cd_micf6["constraints"], lhs_micf6["definition"], lhs_micf6["constraints"],
                       prod_ac_micf6["definition"], prod_ac_micf6["constraints"], prod_bd_micf6["definition"], prod_bd_micf6["constraints"], rhs_micf6["definition"], rhs_micf6["constraints"]])
        prove_or_find_counterexample(s, f"MICF-6 (A/B_fp)*(C/D_fp) ~ (A*C)/(B_fp*D_fp) (B*D is Fp) (Omega={omega_py_val})", setup_micf6, prop_micf6,
                                     [A,B,C,D,lhs_micf6,rhs_micf6], op_result_dicts_for_debug=[div_ab_micf6,div_cd_micf6,prod_ac_micf6,prod_bd_micf6])
        s.pop()
        
        del s
        print("-" * 80)

    print("\n====== AVC Canonical Multiplicative Integrity and Fractions Test Complete ======")