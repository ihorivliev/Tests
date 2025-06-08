# Script Name: AVC_Canonical_OmegaSweep_Integrity_Test.py
from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
# Requirement 1: Parameterized Omega Stress Test
OMEGA_VARIANTS_TO_TEST = [1, 2, 3, 4, 5, 7, 12, 13] # Strategic range

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

# --- Phase 2: Canonical Raw Operations Definitions (Parameterized by current_omega_smt) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_sum = i1["val"] + i2["val"]
    formulas.append(Implies(i1["is_zero"], Or(
        And(i2["is_zero"], res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])))))
    formulas.append(Implies(i1["is_areo"], Or(
        And(i2["is_zero"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
        And(i2["is_areo"], Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
        And(i2["is_finite"], Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i2["val"])))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]),
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]),
                            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], i1["val"]))))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_sum >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum))
                            )))
    return And(formulas)

def define_op_canonical_result(op_logic_builder: Callable, i1_repr: Dict[str, Any], i2_repr: Dict[str, Any],
                               result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = op_logic_builder(i1_repr, i2_repr, res_repr, current_omega_smt)
    res_repr["constraints"] = And(res_repr["constraints"], Implies(res_repr["is_areo"], Equals(res_repr["val"], current_omega_smt)))
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                          res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    formulas = []
    val_prod = i1["val"] * i2["val"]
    formulas.append(Implies(i1["is_zero"], And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), i2["is_zero"]), And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_areo"]),
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i1["is_areo"], i2["is_finite"]), # AS * Fp(>0) -> AS
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(Not(i1["is_zero"]), Not(i2["is_zero"]), i2["is_areo"], i1["is_finite"]), # Fp(>0) * AS -> AS
                            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)) ))
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
                            Ite(val_prod >= current_omega_smt,
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt)),
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
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

def raw_sub_from_Unio_Areo_aspect_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any],
                                                res: Dict[str, Any], current_omega_smt: FNode) -> FNode:
    is_i1_unio_component = Or(i1["is_zero"], i1["is_areo"])
    result_as_AS_C = And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]), Equals(res["val"], current_omega_smt))
    return Ite(
        And(is_i1_unio_component, i2["is_finite"]),
        result_as_AS_C,
        result_as_AS_C
    )

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
            printed_debug_info_ids = set()
            for var_item in model_vars_to_print:
                if isinstance(var_item, dict) and "name" in var_item :
                    val_str = f"V={solver.get_value(var_item['val'])}" if var_item['val'] in solver.get_model() else "V=?"
                    is_z_str = f"Z={solver.get_value(var_item['is_zero'])}" if var_item['is_zero'] in solver.get_model() else "Z=?"
                    is_a_str = f"A={solver.get_value(var_item['is_areo'])}" if var_item['is_areo'] in solver.get_model() else "A=?"
                    is_f_str = f"F={solver.get_value(var_item['is_finite'])}" if var_item['is_finite'] in solver.get_model() else "F=?"
                    print(f"  {var_item['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
                elif isinstance(var_item, FNode):
                    name_to_print = var_item.symbol_name() if var_item.is_symbol() else f"Expression({str(var_item)})"
                    value_str = "?"
                    try: value_str = str(solver.get_value(var_item))
                    except Exception: value_str = "(Error getting value)"
                    print(f"  {name_to_print}: {value_str}")

            if op_result_dicts_for_debug:
                print("  DEBUG Canonical Operation Results in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "name" in op_res_dict:
                        if id(op_res_dict) not in printed_debug_info_ids:
                            printed_debug_info_ids.add(id(op_res_dict))
                            val_str_node = f"V={solver.get_value(op_res_dict['val'])}" if op_res_dict['val'] in solver.get_model() else "V=?"
                            is_z_str_node = f"Z={solver.get_value(op_res_dict['is_zero'])}" if op_res_dict['is_zero'] in solver.get_model() else "Z=?"
                            is_a_str_node = f"A={solver.get_value(op_res_dict['is_areo'])}" if op_res_dict['is_areo'] in solver.get_model() else "A=?"
                            is_f_str_node = f"F={solver.get_value(op_res_dict['is_finite'])}" if op_res_dict['is_finite'] in solver.get_model() else "F=?"
                            print(f"    {op_res_dict['name']} (Canon_Res): {is_z_str_node}, {is_a_str_node}, {is_f_str_node}, {val_str_node}")
    solver.pop()
    print("-" * 70)
    return proved_universally

# --- Phase 4: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Canonical Omega Sweep Integrity Test ======\n")

    for omega_py_val in OMEGA_VARIANTS_TO_TEST:
        s = Solver(name="z3")
        current_omega_smt = Int(omega_py_val)
        print(f"\n\n===== TESTING CANONICAL AVC WITH OMEGA = {omega_py_val} =====\n")

        i1 = create_intensity_representation(f"i1_O{omega_py_val}")
        i2 = create_intensity_representation(f"i2_O{omega_py_val}")
        i3 = create_intensity_representation(f"i3_O{omega_py_val}")

        # Base assertions for i1, i2, i3 to be valid AVC states for the current_omega_smt
        base_input_setup_i123 = [
            i1["constraints"], Implies(i1["is_areo"], Equals(i1["val"], current_omega_smt)),
            i2["constraints"], Implies(i2["is_areo"], Equals(i2["val"], current_omega_smt)),
            i3["constraints"], Implies(i3["is_areo"], Equals(i3["val"], current_omega_smt)),
        ]
        if omega_py_val > 1:
            base_input_setup_i123.extend([
                Implies(i1["is_finite"], i1["val"] < current_omega_smt),
                Implies(i2["is_finite"], i2["val"] < current_omega_smt),
                Implies(i3["is_finite"], i3["val"] < current_omega_smt),
            ])
        else: # Omega == 1, no Finites possible
             base_input_setup_i123.extend([
                Not(i1["is_finite"]), Not(i2["is_finite"]), Not(i3["is_finite"])
            ])
        s.add_assertions(base_input_setup_i123) # Assert these globally for the solver 's' for this omega loop

        # --- C0: Well-Definedness of Operations ---
        i4 = create_intensity_representation(f"i4_O{omega_py_val}")
        i5 = create_intensity_representation(f"i5_O{omega_py_val}")

        # Collect all necessary constraints for i1, i2, i4, i5 for well-definedness tests
        # i1, i2 constraints are already asserted on 's'
        # We need to assert i4, i5 constraints for the duration of each C0.x test locally
        i4_full_constraints = [i4["constraints"], Implies(i4["is_areo"], Equals(i4["val"], current_omega_smt))]
        i5_full_constraints = [i5["constraints"], Implies(i5["is_areo"], Equals(i5["val"], current_omega_smt))]
        if omega_py_val > 1:
            i4_full_constraints.append(Implies(i4["is_finite"], i4["val"] < current_omega_smt))
            i5_full_constraints.append(Implies(i5["is_finite"], i5["val"] < current_omega_smt))
        else:
            i4_full_constraints.append(Not(i4["is_finite"]))
            i5_full_constraints.append(Not(i5["is_finite"]))

        # C0.1: Well-Defined smart_raw_add
        prem_c0_add = And(avc_equiv_canonical(i1, i2), avc_equiv_canonical(i4, i5))
        res1_c0_add = define_op_canonical_result(smart_raw_add_logic_builder, i1, i4, f"r1_c0add_O{omega_py_val}", current_omega_smt)
        res2_c0_add = define_op_canonical_result(smart_raw_add_logic_builder, i2, i5, f"r2_c0add_O{omega_py_val}", current_omega_smt)
        conc_c0_add = avc_equiv_canonical(res1_c0_add, res2_c0_add)
        c0_1_setup_assertions = i4_full_constraints + i5_full_constraints + \
                                [prem_c0_add,
                                 res1_c0_add["constraints"], res1_c0_add["definition"],
                                 res2_c0_add["constraints"], res2_c0_add["definition"]]
        prove_or_find_counterexample(s, f"C0.1 Well-Defined smart_raw_add (Omega={omega_py_val})",
                                     c0_1_setup_assertions, conc_c0_add, [i1,i2,i4,i5,res1_c0_add,res2_c0_add])

        # C0.2: Well-Defined raw_mul
        res1_c0_mul = define_op_canonical_result(raw_mul_logic_builder, i1, i4, f"r1_c0mul_O{omega_py_val}", current_omega_smt)
        res2_c0_mul = define_op_canonical_result(raw_mul_logic_builder, i2, i5, f"r2_c0mul_O{omega_py_val}", current_omega_smt)
        conc_c0_mul = avc_equiv_canonical(res1_c0_mul, res2_c0_mul)
        c0_2_setup_assertions = i4_full_constraints + i5_full_constraints + \
                                [prem_c0_add, # Reusing prem_c0_add as premise for i1~i2, i4~i5
                                 res1_c0_mul["constraints"], res1_c0_mul["definition"],
                                 res2_c0_mul["constraints"], res2_c0_mul["definition"]]
        prove_or_find_counterexample(s, f"C0.2 Well-Defined raw_mul (Omega={omega_py_val})",
                                     c0_2_setup_assertions, conc_c0_mul, [i1,i2,i4,i5,res1_c0_mul,res2_c0_mul])

        # C0.3: Well-Defined raw_div
        res1_c0_div = define_op_canonical_result(raw_div_logic_builder, i1, i4, f"r1_c0div_O{omega_py_val}", current_omega_smt)
        res2_c0_div = define_op_canonical_result(raw_div_logic_builder, i2, i5, f"r2_c0div_O{omega_py_val}", current_omega_smt)
        conc_c0_div = avc_equiv_canonical(res1_c0_div, res2_c0_div)
        c0_3_setup_assertions = i4_full_constraints + i5_full_constraints + \
                                [prem_c0_add, # Reusing prem_c0_add
                                 res1_c0_div["constraints"], res1_c0_div["definition"],
                                 res2_c0_div["constraints"], res2_c0_div["definition"]]
        prove_or_find_counterexample(s, f"C0.3 Well-Defined raw_div (Omega={omega_py_val})",
                                     c0_3_setup_assertions, conc_c0_div, [i1,i2,i4,i5,res1_c0_div,res2_c0_div])

        # C0.4: Well-Defined raw_sub_UnioAreo
        res1_c0_sub = define_op_canonical_result(raw_sub_from_Unio_Areo_aspect_logic_builder, i1, i4, f"r1_c0sub_O{omega_py_val}", current_omega_smt)
        res2_c0_sub = define_op_canonical_result(raw_sub_from_Unio_Areo_aspect_logic_builder, i2, i5, f"r2_c0sub_O{omega_py_val}", current_omega_smt)
        conc_c0_sub = avc_equiv_canonical(res1_c0_sub, res2_c0_sub)
        c0_4_setup_assertions = i4_full_constraints + i5_full_constraints + \
                                [prem_c0_add, # Reusing prem_c0_add
                                 res1_c0_sub["constraints"], res1_c0_sub["definition"],
                                 res2_c0_sub["constraints"], res2_c0_sub["definition"]]
        prove_or_find_counterexample(s, f"C0.4 Well-Defined raw_sub_UnioAreo (Omega={omega_py_val})",
                                     c0_4_setup_assertions, conc_c0_sub, [i1,i2,i4,i5,res1_c0_sub,res2_c0_sub])

        # --- C1: Commutativity (uses i1, i2) ---
        add_ab = define_op_canonical_result(smart_raw_add_logic_builder, i1, i2, f"addAB_O{omega_py_val}", current_omega_smt)
        add_ba = define_op_canonical_result(smart_raw_add_logic_builder, i2, i1, f"addBA_O{omega_py_val}", current_omega_smt)
        prop_add_comm = avc_equiv_canonical(add_ab, add_ba)
        prove_or_find_counterexample(s, f"C1.1 Add Commutativity (Omega={omega_py_val})",
                                     [add_ab["constraints"], add_ab["definition"], add_ba["constraints"], add_ba["definition"]], # i1,i2 constraints already on s
                                     prop_add_comm, [i1, i2, add_ab, add_ba], op_result_dicts_for_debug=[add_ab,add_ba])

        mul_ab = define_op_canonical_result(raw_mul_logic_builder, i1, i2, f"mulAB_O{omega_py_val}", current_omega_smt)
        mul_ba = define_op_canonical_result(raw_mul_logic_builder, i2, i1, f"mulBA_O{omega_py_val}", current_omega_smt)
        prop_mul_comm = avc_equiv_canonical(mul_ab, mul_ba)
        prove_or_find_counterexample(s, f"C1.2 Mul Commutativity (Omega={omega_py_val})",
                                     [mul_ab["constraints"], mul_ab["definition"], mul_ba["constraints"], mul_ba["definition"]],
                                     prop_mul_comm, [i1, i2, mul_ab, mul_ba], op_result_dicts_for_debug=[mul_ab,mul_ba])

        # --- C2: Associativity (uses i1, i2, i3) ---
        sum_ab_c2 = define_op_canonical_result(smart_raw_add_logic_builder, i1, i2, f"sAB_c2_O{omega_py_val}", current_omega_smt)
        lhs_add_assoc = define_op_canonical_result(smart_raw_add_logic_builder, sum_ab_c2, i3, f"lhsAA_O{omega_py_val}", current_omega_smt)
        sum_bc_c2 = define_op_canonical_result(smart_raw_add_logic_builder, i2, i3, f"sBC_c2_O{omega_py_val}", current_omega_smt)
        rhs_add_assoc = define_op_canonical_result(smart_raw_add_logic_builder, i1, sum_bc_c2, f"rhsAA_O{omega_py_val}", current_omega_smt)
        prop_add_assoc = avc_equiv_canonical(lhs_add_assoc, rhs_add_assoc)
        c2_1_setup_assertions = [sum_ab_c2["constraints"], sum_ab_c2["definition"], lhs_add_assoc["constraints"], lhs_add_assoc["definition"],
                                 sum_bc_c2["constraints"], sum_bc_c2["definition"], rhs_add_assoc["constraints"], rhs_add_assoc["definition"]]
        prove_or_find_counterexample(s, f"C2.1 Add Associativity (Omega={omega_py_val})",
                                     c2_1_setup_assertions, prop_add_assoc, [i1,i2,i3,lhs_add_assoc,rhs_add_assoc], op_result_dicts_for_debug=[sum_ab_c2,lhs_add_assoc,sum_bc_c2,rhs_add_assoc])

        prod_ab_c2 = define_op_canonical_result(raw_mul_logic_builder, i1, i2, f"pAB_c2_O{omega_py_val}", current_omega_smt)
        lhs_mul_assoc = define_op_canonical_result(raw_mul_logic_builder, prod_ab_c2, i3, f"lhsMA_O{omega_py_val}", current_omega_smt)
        prod_bc_c2 = define_op_canonical_result(raw_mul_logic_builder, i2, i3, f"pBC_c2_O{omega_py_val}", current_omega_smt)
        rhs_mul_assoc = define_op_canonical_result(raw_mul_logic_builder, i1, prod_bc_c2, f"rhsMA_O{omega_py_val}", current_omega_smt)
        prop_mul_assoc = avc_equiv_canonical(lhs_mul_assoc, rhs_mul_assoc)
        c2_2_setup_assertions = [prod_ab_c2["constraints"], prod_ab_c2["definition"], lhs_mul_assoc["constraints"], lhs_mul_assoc["definition"],
                                 prod_bc_c2["constraints"], prod_bc_c2["definition"], rhs_mul_assoc["constraints"], rhs_mul_assoc["definition"]]
        prove_or_find_counterexample(s, f"C2.2 Mul Associativity (Omega={omega_py_val})",
                                     c2_2_setup_assertions, prop_mul_assoc, [i1,i2,i3,lhs_mul_assoc,rhs_mul_assoc],op_result_dicts_for_debug=[prod_ab_c2,lhs_mul_assoc,prod_bc_c2,rhs_mul_assoc])

        # --- C3: Distributivity (Mul over smart_raw_add) ---
        sum_bc_c3 = define_op_canonical_result(smart_raw_add_logic_builder, i2, i3, f"sBC_c3_O{omega_py_val}", current_omega_smt)
        lhs_distrib = define_op_canonical_result(raw_mul_logic_builder, i1, sum_bc_c3, f"lhsD_O{omega_py_val}", current_omega_smt)
        prod_ab_c3 = define_op_canonical_result(raw_mul_logic_builder, i1, i2, f"pAB_c3_O{omega_py_val}", current_omega_smt)
        prod_ac_c3 = define_op_canonical_result(raw_mul_logic_builder, i1, i3, f"pAC_c3_O{omega_py_val}", current_omega_smt)
        rhs_distrib = define_op_canonical_result(smart_raw_add_logic_builder, prod_ab_c3, prod_ac_c3, f"rhsD_O{omega_py_val}", current_omega_smt)
        prop_distrib = avc_equiv_canonical(lhs_distrib, rhs_distrib)
        c3_1_setup_assertions = [sum_bc_c3["constraints"], sum_bc_c3["definition"], lhs_distrib["constraints"], lhs_distrib["definition"],
                                 prod_ab_c3["constraints"], prod_ab_c3["definition"], prod_ac_c3["constraints"], prod_ac_c3["definition"],
                                 rhs_distrib["constraints"], rhs_distrib["definition"]]
        prove_or_find_counterexample(s, f"C3.1 Distributivity (Omega={omega_py_val})",
                                     c3_1_setup_assertions, prop_distrib, [i1,i2,i3,lhs_distrib,rhs_distrib], op_result_dicts_for_debug=[sum_bc_c3,lhs_distrib,prod_ab_c3,prod_ac_c3,rhs_distrib])

        # --- C4: Basic Unio Additive Interactions (already part of smart_raw_add logic) ---
        if omega_py_val > 1:
            s.push() # Create a local scope for these specific input constraints
            # i1 = ZS, i2 = Fp
            temp_i1_zs_constr = i1["is_zero"]
            temp_i2_fp_constr = And(i2["is_finite"], i2["val"] < current_omega_smt) # Ensure Fp is valid for this Omega
            s.add_assertion(temp_i1_zs_constr)
            s.add_assertion(temp_i2_fp_constr)

            res_zs_fp = define_op_canonical_result(smart_raw_add_logic_builder, i1, i2, f"resZSFp_O{omega_py_val}", current_omega_smt)
            prop_zs_fp = avc_equiv_canonical(res_zs_fp, i2)
            prove_or_find_counterexample(s, f"C4.1 ZS + Fp ~ Fp (Omega={omega_py_val})",
                                         [res_zs_fp["constraints"], res_zs_fp["definition"]], prop_zs_fp, [i1,i2,res_zs_fp], op_result_dicts_for_debug=[res_zs_fp])
            s.pop() # Restore solver state

            s.push()
            # i1 = AS, i2 = Fp
            temp_i1_as_constr = And(i1["is_areo"], Equals(i1["val"], current_omega_smt))
            # temp_i2_fp_constr is same as above
            s.add_assertion(temp_i1_as_constr)
            s.add_assertion(temp_i2_fp_constr) # i2 is Fp

            res_as_fp = define_op_canonical_result(smart_raw_add_logic_builder, i1, i2, f"resASFp_O{omega_py_val}", current_omega_smt)
            prop_as_fp = avc_equiv_canonical(res_as_fp, i2)
            prove_or_find_counterexample(s, f"C4.2 AS + Fp ~ Fp (Omega={omega_py_val})",
                                         [res_as_fp["constraints"], res_as_fp["definition"]], prop_as_fp, [i1,i2,res_as_fp], op_result_dicts_for_debug=[res_as_fp])
            s.pop()

        # --- C5: Basic Subtraction from Unio (Postulate 6.3 / P2.2.iv) ---
        if omega_py_val > 1:
            s.push()
            # i1 = AS, i2 = Fp
            temp_i1_as_constr = And(i1["is_areo"], Equals(i1["val"], current_omega_smt))
            temp_i2_fp_constr = And(i2["is_finite"], i2["val"] < current_omega_smt)
            s.add_assertion(temp_i1_as_constr)
            s.add_assertion(temp_i2_fp_constr)

            res_as_sub_fp = define_op_canonical_result(raw_sub_from_Unio_Areo_aspect_logic_builder, i1, i2, f"resASsubFp_O{omega_py_val}", current_omega_smt)
            prop_as_sub_fp = avc_equiv_canonical(res_as_sub_fp, i1) # Expect AS
            prove_or_find_counterexample(s, f"C5.1 AS - Fp ~ AS (Omega={omega_py_val})",
                                         [res_as_sub_fp["constraints"], res_as_sub_fp["definition"]], prop_as_sub_fp, [i1,i2,res_as_sub_fp], op_result_dicts_for_debug=[res_as_sub_fp])
            s.pop()

            s.push()
            # i1 = ZS, i2 = Fp
            temp_i1_zs_constr = i1["is_zero"]
            # temp_i2_fp_constr is same as above
            s.add_assertion(temp_i1_zs_constr)
            s.add_assertion(temp_i2_fp_constr)

            i1_areo_equiv = create_intensity_representation(f"i1areo_O{omega_py_val}") # Create an AS to compare with
            # These constraints must be added for i1_areo_equiv too for this specific check
            s.add_assertion(i1_areo_equiv["constraints"])
            s.add_assertion(i1_areo_equiv["is_areo"])
            s.add_assertion(Equals(i1_areo_equiv["val"], current_omega_smt))
            if omega_py_val == 1: s.add_assertion(Not(i1_areo_equiv["is_finite"])) # Should not be Fp if Omega=1

            res_zs_sub_fp = define_op_canonical_result(raw_sub_from_Unio_Areo_aspect_logic_builder, i1, i2, f"resZSsubFp_O{omega_py_val}", current_omega_smt)
            prop_zs_sub_fp = avc_equiv_canonical(res_zs_sub_fp, i1_areo_equiv) # Expect AS
            prove_or_find_counterexample(s, f"C5.2 ZS - Fp ~ AS (Omega={omega_py_val})",
                                         [res_zs_sub_fp["constraints"], res_zs_sub_fp["definition"]], prop_zs_sub_fp, [i1,i2,res_zs_sub_fp, i1_areo_equiv], op_result_dicts_for_debug=[res_zs_sub_fp])
            s.pop()

        del s
        print("-" * 80)

    print("\n====== AVC Canonical Omega Sweep Integrity Test Complete ======")