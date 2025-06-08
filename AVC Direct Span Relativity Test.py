from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7] 
DEFAULT_P_A_OFFSET = 0 

# --- Phase 1: Foundational Definitions (Canonical AVC - used by local model) ---
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

# --- Phase 2: Canonical Raw Operations (Parameterized by current_omega_smt) ---
# These are the standard AVC operations we've been using.
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

def define_smart_raw_add_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                          result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_smt)
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

def define_raw_mul_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                    result_name_prefix: str, current_omega_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_smt)
    return res_repr

# --- Phase 3: Local Frame Definitions and Mappings (Direct Span as Omega) ---

def is_local_ZS(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    # Span S = PB - PA. For DFI to exist, S must be > 1.
    # If S=1 (e.g. PA=0, PB=1), then PA < val_L < PB is never true for integers.
    return And(val_L_sym > P_A_val_sym, val_L_sym < P_B_val_sym)

def avc_equiv_local(X1_L_val_sym: FNode, X2_L_val_sym: FNode, 
                    P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Or(
        And(is_local_ZS(X1_L_val_sym, P_A_val_sym), is_local_ZS(X2_L_val_sym, P_A_val_sym)),
        And(is_local_AS(X1_L_val_sym, P_B_val_sym), is_local_AS(X2_L_val_sym, P_B_val_sym)),
        And(is_local_ZS(X1_L_val_sym, P_A_val_sym), is_local_AS(X2_L_val_sym, P_B_val_sym)),
        And(is_local_AS(X1_L_val_sym, P_B_val_sym), is_local_ZS(X2_L_val_sym, P_A_val_sym)),
        And(is_local_DFI(X1_L_val_sym, P_A_val_sym, P_B_val_sym), 
            is_local_DFI(X2_L_val_sym, P_A_val_sym, P_B_val_sym), 
            Equals(X1_L_val_sym, X2_L_val_sym)))

def map_local_to_direct_span_archetype_input_repr(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, # S_sym is PB_sym - PA_sym, the canonical Omega
    canon_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    """
    Maps a local value to a canonical Intensity representation for an archetype [0, S_sym].
    """
    canon_repr = create_intensity_representation(canon_name_prefix)
    assertions = [canon_repr["constraints"]] 

    val_for_canon_calc = Local_val_sym - PA_sym 

    is_L_ZS_cond = is_local_ZS(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS(Local_val_sym, PB_sym)
    is_L_DFI_cond = is_local_DFI(Local_val_sym, PA_sym, PB_sym)

    assertions.append(
        Ite(is_L_ZS_cond, And(canon_repr["is_zero"], Not(canon_repr["is_areo"]), Not(canon_repr["is_finite"])),
        Ite(is_L_AS_cond, And(Not(canon_repr["is_zero"]), canon_repr["is_areo"], Not(canon_repr["is_finite"])),
                          And(Not(canon_repr["is_zero"]), Not(canon_repr["is_areo"]), canon_repr["is_finite"]))))
    
    assertions.append(Implies(canon_repr["is_areo"], Equals(canon_repr["val"], S_sym)))
    assertions.append(Implies(canon_repr["is_finite"], Equals(canon_repr["val"], val_for_canon_calc)))
    
    # Ensure canonical Fp value is valid for its archetype [0, S_sym]
    # val > 0 is in create_intensity_representation. We need val < S_sym.
    assertions.append(Implies(canon_repr["is_finite"], canon_repr["val"] < S_sym))
    
    return canon_repr, assertions

def map_direct_span_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], 
    PA_sym: FNode, PB_sym: FNode # S_sym is implicit in Arch_Res_Repr if AS
) -> FNode:
    """ Maps a result from the direct span canonical archetype back to a local value. """
    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
               PA_sym + Arch_Res_Repr["val"] 
           ))

def define_local_op_direct_span_result(
    op_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    
    S_val_sym = P_B_val_sym - P_A_val_sym # This IS the Omega for canonical operations

    X_canon_repr, x_canon_assertions = map_local_to_direct_span_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, f"{result_name_prefix_local}_xc"
    )
    defining_assertions_for_local_op.extend(x_canon_assertions)

    Y_canon_repr, y_canon_assertions = map_local_to_direct_span_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, f"{result_name_prefix_local}_yc"
    )
    defining_assertions_for_local_op.extend(y_canon_assertions)

    Res_canon_repr = op_canonical_result_definer( 
        X_canon_repr, Y_canon_repr, 
        f"{result_name_prefix_local}_resc", 
        S_val_sym # Pass the local span S as the Omega for the canonical operation
    )
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])

    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_direct_span_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym
    )
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))

    debug_info = {
        "X_canon_repr_dbg": X_canon_repr, "Y_canon_repr_dbg": Y_canon_repr,
        "Res_canon_repr_dbg": Res_canon_repr, 
        "S_val_sym_dbg": S_val_sym, # Store the span used as Omega_C
        "parent_dict_name_for_debug": result_name_prefix_local 
    }
    return {
        "val_L_sym": Res_L_val_sym, 
        "defining_assertions": defining_assertions_for_local_op,
        "debug_info": debug_info
    }

# --- Generic Property Prover (Copied and enhanced for debug_info) ---
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
                     print(f"  {var_item.symbol_name()}: {solver.get_value(var_item)}")
            
            if op_result_dicts_for_debug:
                print("  DEBUG Canonical Mappings in Counterexample:")
                for op_res_dict in op_result_dicts_for_debug:
                    if op_res_dict and isinstance(op_res_dict, dict) and "debug_info" in op_res_dict:
                        debug_info = op_res_dict["debug_info"]
                        if isinstance(debug_info, dict) and id(debug_info) not in printed_debug_info_ids:
                            printed_debug_info_ids.add(id(debug_info)) 
                            op_name_for_print = debug_info.get("parent_dict_name_for_debug", "UnknownOp")
                            print(f"    Context for Local Result '{op_name_for_print}':")
                            s_val_dbg = debug_info.get('S_val_sym_dbg')
                            s_val_str = f"{solver.get_value(s_val_dbg)}" if s_val_dbg and s_val_dbg in solver.get_model() else "?"
                            # For this script, Omega_eff_C is S_val, so we can just print S_val as Omega_C
                            print(f"      Local Span S_val (used as Omega_C)={s_val_str}")
                            for repr_key in ["X_canon_repr_dbg", "Y_canon_repr_dbg", "Res_canon_repr_dbg"]:
                                repr_dict = debug_info.get(repr_key)
                                if repr_dict and isinstance(repr_dict, dict) and "name" in repr_dict:
                                    val_str = f"V={solver.get_value(repr_dict['val'])}" if repr_dict['val'] in solver.get_model() else "V=?"
                                    is_z_str = f"Z={solver.get_value(repr_dict['is_zero'])}" if repr_dict['is_zero'] in solver.get_model() else "Z=?"
                                    is_a_str = f"A={solver.get_value(repr_dict['is_areo'])}" if repr_dict['is_areo'] in solver.get_model() else "A=?"
                                    is_f_str = f"F={solver.get_value(repr_dict['is_finite'])}" if repr_dict['is_finite'] in solver.get_model() else "F=?"
                                    print(f"        {repr_dict['name']}: {is_z_str}, {is_a_str}, {is_f_str}, {val_str}")
    solver.pop() 
    print("-" * 70)
    return proved_universally

# --- Phase 5: Main Testing Logic ---
if __name__ == "__main__":
    print("====== AVC Direct Span Relativity Test ======\n")

    P_A_val_sym = Symbol("PA_val_dsr", solver_INT_TYPE) # dsr for DirectSpanRelativity
    P_B_val_sym = Symbol("PB_val_dsr", solver_INT_TYPE)
    
    La_val_sym = Symbol("La_val_dsr", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val_dsr", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val_dsr", solver_INT_TYPE)

    Li1_val_sym = Symbol("Li1_val_dsr", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val_dsr", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val_dsr", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val_dsr", solver_INT_TYPE)

    # Symbolic integer values for DFI Haven tests (these are local DFI values)
    val_La_dfi_sym = Symbol("val_La_dfi_dsr", solver_INT_TYPE)
    val_Lb_dfi_sym = Symbol("val_Lb_dfi_dsr", solver_INT_TYPE)
    val_Lc_dfi_sym = Symbol("val_Lc_dfi_dsr", solver_INT_TYPE)

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S_py} (Direct Span as Omega) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) 

        # --- L0_DSR: Sanity of avc_equiv_local ---
        print(f"--- Test L0_DSR (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        prove_or_find_counterexample(s, f"L0.1DSR Reflexivity (S={current_local_span_S_py})", [], avc_equiv_local(La_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym])
        s.pop(); s.push(); s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)); s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        prop_L0_2 = Implies(avc_equiv_local(La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym), avc_equiv_local(Lb_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym))
        prove_or_find_counterexample(s, f"L0.2DSR Symmetry (S={current_local_span_S_py})", [], prop_L0_2, model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym])
        s.pop(); s.push(); s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)); s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym)); s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))
        prem_L0_3 = And(avc_equiv_local(La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym), avc_equiv_local(Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym))
        conc_L0_3 = avc_equiv_local(La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L0.3DSR Transitivity (S={current_local_span_S_py})", [prem_L0_3], conc_L0_3, model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym])
        s.pop()

        # --- L1_DSR: Well-Definedness of Local Direct Span Operations ---
        print(f"\n--- Test L1_DSR (S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym)); s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym)); s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))
        premise_L1DSR = And(avc_equiv_local(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym), avc_equiv_local(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        
        op_L1DSR_add_r1 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1DSR_add_r1")
        op_L1DSR_add_r2 = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1DSR_add_r2")
        conc_L1DSR_add = avc_equiv_local(op_L1DSR_add_r1["val_L_sym"], op_L1DSR_add_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.1DSR Add respects avc_equiv_local (S={current_local_span_S_py})", [premise_L1DSR] + op_L1DSR_add_r1["defining_assertions"] + op_L1DSR_add_r2["defining_assertions"], conc_L1DSR_add, model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L1DSR_add_r1["val_L_sym"],op_L1DSR_add_r2["val_L_sym"]], op_result_dicts_for_debug=[op_L1DSR_add_r1, op_L1DSR_add_r2])
        
        op_L1DSR_mul_r1 = define_local_op_direct_span_result(define_raw_mul_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1DSR_mul_r1")
        op_L1DSR_mul_r2 = define_local_op_direct_span_result(define_raw_mul_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1DSR_mul_r2")
        conc_L1DSR_mul = avc_equiv_local(op_L1DSR_mul_r1["val_L_sym"], op_L1DSR_mul_r2["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.2DSR Mul respects avc_equiv_local (S={current_local_span_S_py})", [premise_L1DSR] + op_L1DSR_mul_r1["defining_assertions"] + op_L1DSR_mul_r2["defining_assertions"], conc_L1DSR_mul, model_vars_to_print=[P_A_val_sym,P_B_val_sym,Li1_val_sym,Lj1_val_sym,Li2_val_sym,Lj2_val_sym,op_L1DSR_mul_r1["val_L_sym"],op_L1DSR_mul_r2["val_L_sym"]], op_result_dicts_for_debug=[op_L1DSR_mul_r1, op_L1DSR_mul_r2])
        s.pop()

        # General setup for algebraic laws: La, Lb, Lc are symbolic local values
        general_setup_L_abc = [ And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym),
                                And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym),
                                And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym) ]
        
        # --- L2_DSR: Associativity of smart_raw_add_local_direct ---
        print(f"\n--- Test L2_DSR Add Assoc (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        sum_ab_L2DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2DSR_sum_ab")
        lhs_L2DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, sum_ab_L2DSR["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2DSR_lhs")
        sum_bc_L2DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2DSR_sum_bc")
        rhs_L2DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_val_sym, sum_bc_L2DSR["val_L_sym"], P_A_val_sym, P_B_val_sym, "L2DSR_rhs")
        all_L2DSR_asserts = sum_ab_L2DSR["defining_assertions"] + lhs_L2DSR["defining_assertions"] + sum_bc_L2DSR["defining_assertions"] + rhs_L2DSR["defining_assertions"]
        prove_or_find_counterexample(s, f"L2DSR Add Assoc (S={current_local_span_S_py})", all_L2DSR_asserts, avc_equiv_local(lhs_L2DSR["val_L_sym"], rhs_L2DSR["val_L_sym"], P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,sum_ab_L2DSR["val_L_sym"],lhs_L2DSR["val_L_sym"],sum_bc_L2DSR["val_L_sym"],rhs_L2DSR["val_L_sym"]], op_result_dicts_for_debug=[sum_ab_L2DSR, lhs_L2DSR, sum_bc_L2DSR, rhs_L2DSR])
        s.pop()
        
        # --- L3_DSR: Associativity of raw_mul_local_direct ---
        print(f"\n--- Test L3_DSR Mul Assoc (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        prod_ab_L3DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3DSR_prod_ab")
        lhs_mul_L3DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, prod_ab_L3DSR["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3DSR_lhs_mul")
        prod_bc_L3DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3DSR_prod_bc")
        rhs_mul_L3DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, prod_bc_L3DSR["val_L_sym"], P_A_val_sym, P_B_val_sym, "L3DSR_rhs_mul")
        all_L3DSR_asserts = prod_ab_L3DSR["defining_assertions"] + lhs_mul_L3DSR["defining_assertions"] + prod_bc_L3DSR["defining_assertions"] + rhs_mul_L3DSR["defining_assertions"]
        prove_or_find_counterexample(s, f"L3DSR Mul Assoc (S={current_local_span_S_py})", all_L3DSR_asserts, avc_equiv_local(lhs_mul_L3DSR["val_L_sym"], rhs_mul_L3DSR["val_L_sym"], P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym], op_result_dicts_for_debug=[prod_ab_L3DSR, lhs_mul_L3DSR, prod_bc_L3DSR, rhs_mul_L3DSR])
        s.pop()

        # --- L4_DSR: Distributivity ---
        print(f"\n--- Test L4_DSR Distributivity (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        sum_bc_L4DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L4DSR_sum_bc")
        lhs_dist_L4DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, sum_bc_L4DSR["val_L_sym"], P_A_val_sym, P_B_val_sym, "L4DSR_lhs_dist")
        prod_ab_L4DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4DSR_prod_ab")
        prod_ac_L4DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L4DSR_prod_ac")
        rhs_dist_L4DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ab_L4DSR["val_L_sym"], prod_ac_L4DSR["val_L_sym"], P_A_val_sym, P_B_val_sym, "L4DSR_rhs_dist")
        all_L4DSR_asserts = sum_bc_L4DSR["defining_assertions"] + lhs_dist_L4DSR["defining_assertions"] + prod_ab_L4DSR["defining_assertions"] + prod_ac_L4DSR["defining_assertions"] + rhs_dist_L4DSR["defining_assertions"]
        op_results_L4DSR_debug = [sum_bc_L4DSR, lhs_dist_L4DSR, prod_ab_L4DSR, prod_ac_L4DSR, rhs_dist_L4DSR]
        prove_or_find_counterexample(s, f"L4DSR Distributivity (S={current_local_span_S_py})", all_L4DSR_asserts, avc_equiv_local(lhs_dist_L4DSR["val_L_sym"], rhs_dist_L4DSR["val_L_sym"], P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,sum_bc_L4DSR["val_L_sym"],lhs_dist_L4DSR["val_L_sym"],prod_ab_L4DSR["val_L_sym"],prod_ac_L4DSR["val_L_sym"],rhs_dist_L4DSR["val_L_sym"]], op_result_dicts_for_debug=op_results_L4DSR_debug)
        s.pop()
        
        # --- L5_DSR: Additive Cancellation ---
        print(f"\n--- Test L5_DSR Additive Cancellation (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        add_ab_L5DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L5DSR_add_ab")
        add_ac_L5DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L5DSR_add_ac")
        premise_L5DSR = And(avc_equiv_local(add_ab_L5DSR["val_L_sym"], add_ac_L5DSR["val_L_sym"], P_A_val_sym, P_B_val_sym))
        conclusion_L5DSR = avc_equiv_local(Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym)
        all_L5DSR_asserts = add_ab_L5DSR["defining_assertions"] + add_ac_L5DSR["defining_assertions"]
        prove_or_find_counterexample(s, f"L5DSR Additive Cancellation (S={current_local_span_S_py})", [premise_L5DSR] + all_L5DSR_asserts, conclusion_L5DSR, model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,add_ab_L5DSR["val_L_sym"],add_ac_L5DSR["val_L_sym"]], op_result_dicts_for_debug=[add_ab_L5DSR, add_ac_L5DSR])
        s.pop()

        # --- L6_DSR: Additive Idempotence ---
        print(f"\n--- Test L6_DSR Additive Idempotence (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym)) # La can be ZS, AS, or DFI
        add_aa_L6DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L6DSR_add_aa")
        prove_or_find_counterexample(s, f"L6DSR Additive Idempotence La+La ~ La (S={current_local_span_S_py})", add_aa_L6DSR["defining_assertions"], avc_equiv_local(add_aa_L6DSR["val_L_sym"], La_val_sym, P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,add_aa_L6DSR["val_L_sym"]], op_result_dicts_for_debug=[add_aa_L6DSR])
        s.pop()
        
        # --- L7_DSR: Multiplicative Cancellation ---
        print(f"\n--- Test L7_DSR Multiplicative Cancellation (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(general_setup_L_abc)
        mul_ab_L7DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L7DSR_mul_ab")
        mul_ac_L7DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L7DSR_mul_ac")
        premise_L7DSR = And(avc_equiv_local(mul_ab_L7DSR["val_L_sym"], mul_ac_L7DSR["val_L_sym"], P_A_val_sym, P_B_val_sym), Not(is_local_ZS(La_val_sym, P_A_val_sym)))
        conclusion_L7DSR = avc_equiv_local(Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym)
        all_L7DSR_asserts = mul_ab_L7DSR["defining_assertions"] + mul_ac_L7DSR["defining_assertions"]
        prove_or_find_counterexample(s, f"L7DSR Multiplicative Cancellation (S={current_local_span_S_py})", [premise_L7DSR] + all_L7DSR_asserts, conclusion_L7DSR, model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,mul_ab_L7DSR["val_L_sym"],mul_ac_L7DSR["val_L_sym"]], op_result_dicts_for_debug=[mul_ab_L7DSR, mul_ac_L7DSR])
        s.pop()

        # --- L8_DSR: Multiplicative Idempotence ---
        print(f"\n--- Test L8_DSR Multiplicative Idempotence (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        mul_aa_L8DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, La_val_sym, P_A_val_sym, P_B_val_sym, "L8DSR_mul_aa")
        prove_or_find_counterexample(s, f"L8DSR Multiplicative Idempotence La*La ~ La (S={current_local_span_S_py})", mul_aa_L8DSR["defining_assertions"], avc_equiv_local(mul_aa_L8DSR["val_L_sym"], La_val_sym, P_A_val_sym, P_B_val_sym), model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,mul_aa_L8DSR["val_L_sym"]], op_result_dicts_for_debug=[mul_aa_L8DSR])
        s.pop()

        # --- DFI Haven Tests ---
        # Setup for DFI Haven: La, Lb, Lc are strictly local DFIs
        dfi_haven_setup_assertions = [
            is_local_DFI(La_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI(Lb_val_sym, P_A_val_sym, P_B_val_sym),
            is_local_DFI(Lc_val_sym, P_A_val_sym, P_B_val_sym)
        ]
        # For DFI Haven, map local DFI values to symbolic canonical DFI values
        # This requires the canonical DFI values to be constrained 0 < val_canon < S_val_sym
        # The map_local_to_direct_span_archetype_input_repr already does this.

        # --- L9_DSR_DFI_Haven_Assoc_Add ---
        print(f"\n--- Test L9_DSR DFI Haven Add Assoc (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(dfi_haven_setup_assertions)
        sum_ab_L9DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L9DSR_sum_ab")
        lhs_L9DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, sum_ab_L9DSR["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L9DSR_lhs")
        sum_bc_L9DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L9DSR_sum_bc")
        rhs_L9DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, La_val_sym, sum_bc_L9DSR["val_L_sym"], P_A_val_sym, P_B_val_sym, "L9DSR_rhs")
        all_L9DSR_defs = sum_ab_L9DSR["defining_assertions"] + lhs_L9DSR["defining_assertions"] + sum_bc_L9DSR["defining_assertions"] + rhs_L9DSR["defining_assertions"]
        dfi_haven_conds_L9DSR = [ 
            is_local_DFI(sum_ab_L9DSR["val_L_sym"], P_A_val_sym, P_B_val_sym), is_local_DFI(lhs_L9DSR["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(sum_bc_L9DSR["val_L_sym"], P_A_val_sym, P_B_val_sym), is_local_DFI(rhs_L9DSR["val_L_sym"], P_A_val_sym, P_B_val_sym)
        ]
        prove_or_find_counterexample(s, f"L9DSR Add Assoc (DFI Haven, S={current_local_span_S_py})", all_L9DSR_defs + dfi_haven_conds_L9DSR, 
                                     avc_equiv_local(lhs_L9DSR["val_L_sym"], rhs_L9DSR["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,sum_ab_L9DSR["val_L_sym"],lhs_L9DSR["val_L_sym"],sum_bc_L9DSR["val_L_sym"],rhs_L9DSR["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_L9DSR, lhs_L9DSR, sum_bc_L9DSR, rhs_L9DSR])
        s.pop()

        # --- L10_DSR_DFI_Haven_Dist ---
        print(f"\n--- Test L10_DSR DFI Haven Distributivity (S={current_local_span_S_py}) ---")
        s.push(); s.add_assertions(dfi_haven_setup_assertions)
        sum_bc_L10DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L10DSR_sum_bc")
        lhs_dist_L10DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, sum_bc_L10DSR["val_L_sym"], P_A_val_sym, P_B_val_sym, "L10DSR_lhs_dist")
        prod_ab_L10DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L10DSR_prod_ab")
        prod_ac_L10DSR = define_local_op_direct_span_result(define_raw_mul_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L10DSR_prod_ac")
        rhs_dist_L10DSR = define_local_op_direct_span_result(define_smart_raw_add_canonical_result, prod_ab_L10DSR["val_L_sym"], prod_ac_L10DSR["val_L_sym"], P_A_val_sym, P_B_val_sym, "L10DSR_rhs_dist")
        all_L10DSR_defs = sum_bc_L10DSR["defining_assertions"] + lhs_dist_L10DSR["defining_assertions"] + prod_ab_L10DSR["defining_assertions"] + prod_ac_L10DSR["defining_assertions"] + rhs_dist_L10DSR["defining_assertions"]
        dfi_haven_conds_L10DSR = [
            is_local_DFI(sum_bc_L10DSR["val_L_sym"], P_A_val_sym, P_B_val_sym), is_local_DFI(lhs_dist_L10DSR["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(prod_ab_L10DSR["val_L_sym"], P_A_val_sym, P_B_val_sym), is_local_DFI(prod_ac_L10DSR["val_L_sym"], P_A_val_sym, P_B_val_sym),
            is_local_DFI(rhs_dist_L10DSR["val_L_sym"], P_A_val_sym, P_B_val_sym)
        ]
        op_results_L10DSR_debug = [sum_bc_L10DSR, lhs_dist_L10DSR, prod_ab_L10DSR, prod_ac_L10DSR, rhs_dist_L10DSR]
        prove_or_find_counterexample(s, f"L10DSR Distributivity (DFI Haven, S={current_local_span_S_py})", all_L10DSR_defs + dfi_haven_conds_L10DSR, 
                                     avc_equiv_local(lhs_dist_L10DSR["val_L_sym"], rhs_dist_L10DSR["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym,P_B_val_sym,La_val_sym,Lb_val_sym,Lc_val_sym,sum_bc_L10DSR["val_L_sym"],lhs_dist_L10DSR["val_L_sym"],prod_ab_L10DSR["val_L_sym"],prod_ac_L10DSR["val_L_sym"],rhs_dist_L10DSR["val_L_sym"]],
                                     op_result_dicts_for_debug=op_results_L10DSR_debug)
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC Direct Span Relativity Test Complete ======")

