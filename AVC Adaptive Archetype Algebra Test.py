from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE, FALSE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE
from pysmt.fnode import FNode 
from typing import Callable, List, Dict, Any, Tuple

# --- Configuration ---
OMEGA_VARIANTS_FOR_LOCAL_SPAN_S = [1, 2, 3, 5, 7] 
DEFAULT_P_A_OFFSET = 0 

# --- Phase 1: Foundational Definitions (Canonical AVC - used by adaptive model) ---
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

# --- Phase 2: Canonical Raw Operations (Parameterized by an effective Omega_C) ---
def smart_raw_add_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                                res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode:
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
                            Ite(val_sum >= current_omega_eff_c_smt, 
                                And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_sum)) 
                            )))
    return And(formulas)

def define_smart_raw_add_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                          result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = smart_raw_add_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

def raw_mul_logic_builder(i1: Dict[str, Any], i2: Dict[str, Any], 
                          res: Dict[str, Any], current_omega_eff_c_smt: FNode) -> FNode:
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
                            Ite(val_prod >= current_omega_eff_c_smt, And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), 
                                And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"], Equals(res["val"], val_prod)))))
    return And(formulas)

def define_raw_mul_canonical_result(i1_canon_repr: Dict[str, Any], i2_canon_repr: Dict[str, Any], 
                                    result_name_prefix: str, current_omega_eff_c_smt: FNode) -> Dict[str, Any]:
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = raw_mul_logic_builder(i1_canon_repr, i2_canon_repr, res_repr, current_omega_eff_c_smt)
    return res_repr

# --- Phase 3: Local Frame, Adaptive Omega, and Mappings ---

def is_local_ZS(val_L_sym: FNode, P_A_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_A_val_sym)

def is_local_AS(val_L_sym: FNode, P_B_val_sym: FNode) -> FNode:
    return Equals(val_L_sym, P_B_val_sym)

def is_local_DFI(val_L_sym: FNode, P_A_val_sym: FNode, P_B_val_sym: FNode) -> FNode:
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

def determine_effective_canonical_omega(S_val_sym: FNode) -> FNode:
    return Ite(Equals(S_val_sym, Int(1)), Int(1),
           Ite(Equals(S_val_sym, Int(2)), Int(2),
                                           Int(3))) 

def map_local_to_adaptive_archetype_input_repr(
    Local_val_sym: FNode, 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode, 
    arch_name_prefix: str
) -> Tuple[Dict[str, Any], List[FNode]]:
    arch_repr = create_intensity_representation(arch_name_prefix)
    
    is_L_ZS_cond = is_local_ZS(Local_val_sym, PA_sym)
    is_L_AS_cond = is_local_AS(Local_val_sym, PB_sym)
    is_L_DFI_cond = is_local_DFI(Local_val_sym, PA_sym, PB_sym)

    # --- Define Canonical Kind ---
    # This logic needs to be robust for S_sym=1 where is_L_DFI_cond would be false.
    # If local is DFI (so S_sym >= 2), map to canonical Fp, unless Omega_eff_C is 1 (which it won't be if S_sym >=2).
    kind_assertions = [
        arch_repr["constraints"],
        Implies(is_L_ZS_cond, 
                And(arch_repr["is_zero"], Not(arch_repr["is_areo"]), Not(arch_repr["is_finite"]))),
        Implies(is_L_AS_cond,
                And(Not(arch_repr["is_zero"]), arch_repr["is_areo"], Not(arch_repr["is_finite"]))),
        Implies(is_L_DFI_cond, # This implies S_sym >= 2
                # Since S_sym >= 2, Omega_eff_C_sym will be >= 2, so canonical DFI exists.
                And(Not(arch_repr["is_zero"]), Not(arch_repr["is_areo"]), arch_repr["is_finite"]))
    ]
    
    # --- Define Canonical Value ---
    val_assertions = [Implies(arch_repr["is_areo"], Equals(arch_repr["val"], Omega_eff_C_sym))] # Canon AS val is Omega_eff_C_sym

    # Canon Fp val mapping:
    val_if_omega_eff_is_2 = Int(1) # If Omega_eff_C is 2, Canon Fp val is 1.
    val_if_omega_eff_is_3 = Ite(Equals(Local_val_sym, PA_sym + Int(1)), # If Omega_eff_C is 3:
                                Int(1),                                  # Local P_A+1 -> Canon Fp(1)
                                Int(2))                                  # Other Local DFIs -> Canon Fp(2)
                                 
    val_assertions.append(
        Implies(arch_repr["is_finite"], 
            # Omega_eff_C cannot be 1 if arch_repr is finite because is_L_DFI_cond implies S_sym >= 2
            Ite(Equals(Omega_eff_C_sym, Int(2)),
                Equals(arch_repr["val"], val_if_omega_eff_is_2),
                # Else Omega_eff_C_sym must be 3 if arch_repr is_finite
                Equals(arch_repr["val"], val_if_omega_eff_is_3) 
            )
        )
    )
    # Ensure canonical Fp value is valid for its archetype (val > 0 and val < Omega_eff_C_sym)
    val_assertions.append(Implies(arch_repr["is_finite"], 
                            And(arch_repr["val"] > Int(0), arch_repr["val"] < Omega_eff_C_sym)))

    return arch_repr, kind_assertions + val_assertions

def map_adaptive_archetype_result_to_local(
    Arch_Res_Repr: Dict[str, Any], 
    PA_sym: FNode, PB_sym: FNode, S_sym: FNode, 
    Omega_eff_C_sym: FNode 
) -> FNode:
    # Default mapping for Fp_C if Omega_eff_C_sym is 1 (Arch_Res_Repr should not be Fp_C then)
    val_from_fp_if_omega_eff_is_1 = PB_sym # Fallback to local AS
    
    # Mapping for Fp_C if Omega_eff_C_sym is 2 (Arch_Res_Repr.val must be 1)
    # If local span S=1, Fp_C(1) from Omega_eff_C=2 means "one step in a 2-step system".
    # For S=1 (local ZS, local AS only), this "one step" means hitting local AS.
    val_from_fp_if_omega_eff_is_2 = Ite(Equals(S_sym, Int(1)), PB_sym, PA_sym + Int(1))

    # Mapping for Fp_C if Omega_eff_C_sym is 3 (Arch_Res_Repr.val is 1 or 2)
    val_from_fp_if_omega_eff_is_3 = \
        Ite(Equals(S_sym, Int(1)), PB_sym, # No local DFI, map any Fp_C to local AS
        Ite(Equals(S_sym, Int(2)), # Local DFI is {PA+1}
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), # Canon Fp(1) -> PA+1
                                                    PB_sym),          # Canon Fp(2) -> Local AS (P_B)
            # Else S_sym >= 3 (Local DFI has at least PA+1, and PB-1 if S_sym >=2)
            Ite(Equals(Arch_Res_Repr["val"], Int(1)), PA_sym + Int(1), # Canon Fp(1) -> PA+1
                                                    PB_sym - Int(1))  # Canon Fp(2) -> PB-1
           ))
                                           
    fp_result_val = Ite(Equals(Omega_eff_C_sym, Int(1)), val_from_fp_if_omega_eff_is_1,
                    Ite(Equals(Omega_eff_C_sym, Int(2)), val_from_fp_if_omega_eff_is_2,
                                                        val_from_fp_if_omega_eff_is_3))

    return Ite(Arch_Res_Repr["is_zero"], PA_sym,
           Ite(Arch_Res_Repr["is_areo"], PB_sym,
               fp_result_val 
           ))

def define_local_op_adaptive_archetype_result(
    op_canonical_result_definer: Callable, 
    X_L_val_sym: FNode, Y_L_val_sym: FNode, 
    P_A_val_sym: FNode, P_B_val_sym: FNode, 
    result_name_prefix_local: str
) -> Dict[str, Any]:
    defining_assertions_for_local_op = []
    
    S_val_sym = P_B_val_sym - P_A_val_sym
    Omega_eff_C_sym = determine_effective_canonical_omega(S_val_sym)

    X_canon_repr, x_canon_assertions = map_local_to_adaptive_archetype_input_repr(
        X_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_xc"
    )
    defining_assertions_for_local_op.extend(x_canon_assertions)

    Y_canon_repr, y_canon_assertions = map_local_to_adaptive_archetype_input_repr(
        Y_L_val_sym, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym, f"{result_name_prefix_local}_yc"
    )
    defining_assertions_for_local_op.extend(y_canon_assertions)

    Res_canon_repr = op_canonical_result_definer( 
        X_canon_repr, Y_canon_repr, 
        f"{result_name_prefix_local}_resc", 
        Omega_eff_C_sym 
    )
    defining_assertions_for_local_op.append(Res_canon_repr["definition"])
    defining_assertions_for_local_op.append(Res_canon_repr["constraints"])

    Res_L_val_sym = Symbol(f"{result_name_prefix_local}_ResL_val", solver_INT_TYPE)
    local_result_value_formula = map_adaptive_archetype_result_to_local(
        Res_canon_repr, P_A_val_sym, P_B_val_sym, S_val_sym, Omega_eff_C_sym
    )
    defining_assertions_for_local_op.append(Equals(Res_L_val_sym, local_result_value_formula))

    debug_info = { 
        "X_canon_repr_dbg": X_canon_repr, "Y_canon_repr_dbg": Y_canon_repr,
        "Res_canon_repr_dbg": Res_canon_repr, "Omega_eff_C_sym_dbg": Omega_eff_C_sym,
        "S_val_sym_dbg": S_val_sym,
        # Store the name of the top-level dict for easier access if needed
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
            printed_debug_info_ids = set() # Use id() of debug_info dicts to track printing
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
                    # Check if the dict has 'debug_info' and if that specific debug_info object hasn't been printed
                    if op_res_dict and isinstance(op_res_dict, dict) and "debug_info" in op_res_dict:
                        debug_info = op_res_dict["debug_info"]
                        if isinstance(debug_info, dict) and id(debug_info) not in printed_debug_info_ids:
                            printed_debug_info_ids.add(id(debug_info)) # Mark as printed
                            
                            op_name_for_print = debug_info.get("parent_dict_name_for_debug", "UnknownOp")
                            print(f"    Context for Local Result '{op_name_for_print}':")
                            
                            s_val_dbg = debug_info.get('S_val_sym_dbg')
                            o_eff_dbg = debug_info.get('Omega_eff_C_sym_dbg')

                            s_val_str = f"{solver.get_value(s_val_dbg)}" if s_val_dbg and s_val_dbg in solver.get_model() else "?"
                            o_eff_str = f"{solver.get_value(o_eff_dbg)}" if o_eff_dbg and o_eff_dbg in solver.get_model() else "?"
                            print(f"      Local Span S_val={s_val_str}, Effective Canon. Omega_eff_C={o_eff_str}")
                            
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
    print("====== AVC Adaptive Archetype Algebra Test ======\n")

    P_A_val_sym = Symbol("PA_val", solver_INT_TYPE)
    P_B_val_sym = Symbol("PB_val", solver_INT_TYPE)
    
    La_val_sym = Symbol("La_val_adapt", solver_INT_TYPE)
    Lb_val_sym = Symbol("Lb_val_adapt", solver_INT_TYPE)
    Lc_val_sym = Symbol("Lc_val_adapt", solver_INT_TYPE)

    Li1_val_sym = Symbol("Li1_val_adapt", solver_INT_TYPE)
    Lj1_val_sym = Symbol("Lj1_val_adapt", solver_INT_TYPE)
    Li2_val_sym = Symbol("Li2_val_adapt", solver_INT_TYPE)
    Lj2_val_sym = Symbol("Lj2_val_adapt", solver_INT_TYPE)

    for current_local_span_S_py in OMEGA_VARIANTS_FOR_LOCAL_SPAN_S:
        s = Solver(name="z3")
        current_local_span_S_smt = Int(current_local_span_S_py)
        print(f"\n\n===== LOCAL FRAME SPAN S = {current_local_span_S_py} (Maps to Adaptive Canonical Omega) =====\n")

        s.add_assertion(Equals(P_A_val_sym, Int(DEFAULT_P_A_OFFSET)))
        s.add_assertion(Equals(P_B_val_sym, P_A_val_sym + current_local_span_S_smt))
        s.add_assertion(current_local_span_S_smt > Int(0)) # Span must be positive

        # --- Test L1_Adapt: Well-Definedness of Local Adaptive Operations ---
        print(f"--- Test L1_Adapt: Well-Definedness (Adaptive Arch, Local Span S={current_local_span_S_py}) ---")
        s.push()
        # Assert inputs are valid local values
        s.add_assertion(And(Li1_val_sym >= P_A_val_sym, Li1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj1_val_sym >= P_A_val_sym, Lj1_val_sym <= P_B_val_sym))
        s.add_assertion(And(Li2_val_sym >= P_A_val_sym, Li2_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lj2_val_sym >= P_A_val_sym, Lj2_val_sym <= P_B_val_sym))
        premise_L1A = And(avc_equiv_local(Li1_val_sym, Li2_val_sym, P_A_val_sym, P_B_val_sym),
                          avc_equiv_local(Lj1_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym))
        
        op_L1A_add_r1_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1A_add_r1")
        op_L1A_add_r2_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1A_add_r2")
        conclusion_L1A_add = avc_equiv_local(op_L1A_add_r1_dict["val_L_sym"], op_L1A_add_r2_dict["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.1A smart_raw_add_local_adaptive respects avc_equiv_local (S={current_local_span_S_py})",
                                     [premise_L1A] + op_L1A_add_r1_dict["defining_assertions"] + op_L1A_add_r2_dict["defining_assertions"],
                                     conclusion_L1A_add,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, Li1_val_sym, Lj1_val_sym, Li2_val_sym, Lj2_val_sym, 
                                                          op_L1A_add_r1_dict["val_L_sym"], op_L1A_add_r2_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L1A_add_r1_dict, op_L1A_add_r2_dict])
        
        op_L1A_mul_r1_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, Li1_val_sym, Lj1_val_sym, P_A_val_sym, P_B_val_sym, "L1A_mul_r1")
        op_L1A_mul_r2_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, Li2_val_sym, Lj2_val_sym, P_A_val_sym, P_B_val_sym, "L1A_mul_r2")
        conclusion_L1A_mul = avc_equiv_local(op_L1A_mul_r1_dict["val_L_sym"], op_L1A_mul_r2_dict["val_L_sym"], P_A_val_sym, P_B_val_sym)
        prove_or_find_counterexample(s, f"L1.2A raw_mul_local_adaptive respects avc_equiv_local (S={current_local_span_S_py})",
                                     [premise_L1A] + op_L1A_mul_r1_dict["defining_assertions"] + op_L1A_mul_r2_dict["defining_assertions"],
                                     conclusion_L1A_mul,
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, Li1_val_sym, Lj1_val_sym, Li2_val_sym, Lj2_val_sym, op_L1A_mul_r1_dict["val_L_sym"], op_L1A_mul_r2_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[op_L1A_mul_r1_dict, op_L1A_mul_r2_dict])
        s.pop()

        # --- Test L2_Adapt: Associativity of smart_raw_add_local_adaptive ---
        print(f"\n--- Test L2_Adapt: Associativity of smart_raw_add_local_adaptive (Local Span S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))

        sum_ab_L2A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L2A_sum_ab")
        lhs_L2A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, sum_ab_L2A_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2A_lhs")
        sum_bc_L2A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L2A_sum_bc")
        rhs_L2A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, La_val_sym, sum_bc_L2A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L2A_rhs")
        
        all_L2A_assertions = sum_ab_L2A_dict["defining_assertions"] + lhs_L2A_dict["defining_assertions"] + \
                               sum_bc_L2A_dict["defining_assertions"] + rhs_L2A_dict["defining_assertions"]
        
        prove_or_find_counterexample(s, f"L2A Assoc. smart_raw_add_local_adaptive (S={current_local_span_S_py})",
                                     all_L2A_assertions,
                                     avc_equiv_local(lhs_L2A_dict["val_L_sym"], rhs_L2A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym, 
                                                          sum_ab_L2A_dict["val_L_sym"], lhs_L2A_dict["val_L_sym"], 
                                                          sum_bc_L2A_dict["val_L_sym"], rhs_L2A_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=[sum_ab_L2A_dict, lhs_L2A_dict, sum_bc_L2A_dict, rhs_L2A_dict])
        s.pop()

        # --- Test L3_Adapt: Associativity of raw_mul_local_adaptive ---
        print(f"\n--- Test L3_Adapt: Associativity of raw_mul_local_adaptive (Local Span S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))

        prod_ab_L3A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L3A_prod_ab")
        lhs_mul_L3A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, prod_ab_L3A_dict["val_L_sym"], Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3A_lhs_mul")
        prod_bc_L3A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L3A_prod_bc")
        rhs_mul_L3A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, prod_bc_L3A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L3A_rhs_mul")

        all_L3A_assertions = prod_ab_L3A_dict["defining_assertions"] + lhs_mul_L3A_dict["defining_assertions"] + \
                               prod_bc_L3A_dict["defining_assertions"] + rhs_mul_L3A_dict["defining_assertions"]

        prove_or_find_counterexample(s, f"L3A Assoc. raw_mul_local_adaptive (S={current_local_span_S_py})",
                                     all_L3A_assertions,
                                     avc_equiv_local(lhs_mul_L3A_dict["val_L_sym"], rhs_mul_L3A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym],
                                     op_result_dicts_for_debug=[prod_ab_L3A_dict, lhs_mul_L3A_dict, prod_bc_L3A_dict, rhs_mul_L3A_dict])
        s.pop()

        # --- Test L4_Adapt: Distributivity (Local Adaptive Archetype) ---
        print(f"\n--- Test L4_Adapt: Distributivity (Local Adaptive Arch, Local Span S={current_local_span_S_py}) ---")
        s.push()
        s.add_assertion(And(La_val_sym >= P_A_val_sym, La_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lb_val_sym >= P_A_val_sym, Lb_val_sym <= P_B_val_sym))
        s.add_assertion(And(Lc_val_sym >= P_A_val_sym, Lc_val_sym <= P_B_val_sym))

        sum_bc_L4A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, Lb_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L4A_sum_bc")
        lhs_dist_L4A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, sum_bc_L4A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L4A_lhs_dist")
        prod_ab_L4A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, Lb_val_sym, P_A_val_sym, P_B_val_sym, "L4A_prod_ab")
        prod_ac_L4A_dict = define_local_op_adaptive_archetype_result(define_raw_mul_canonical_result, La_val_sym, Lc_val_sym, P_A_val_sym, P_B_val_sym, "L4A_prod_ac")
        rhs_dist_L4A_dict = define_local_op_adaptive_archetype_result(define_smart_raw_add_canonical_result, prod_ab_L4A_dict["val_L_sym"], prod_ac_L4A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym, "L4A_rhs_dist")

        all_L4A_definitions = sum_bc_L4A_dict["defining_assertions"] + lhs_dist_L4A_dict["defining_assertions"] + \
                               prod_ab_L4A_dict["defining_assertions"] + prod_ac_L4A_dict["defining_assertions"] + \
                               rhs_dist_L4A_dict["defining_assertions"]
        
        op_results_for_L4A_debug = [sum_bc_L4A_dict, lhs_dist_L4A_dict, prod_ab_L4A_dict, prod_ac_L4A_dict, rhs_dist_L4A_dict]

        prove_or_find_counterexample(s, f"L4A Distributivity (Local Adaptive Arch, S={current_local_span_S_py})",
                                     all_L4A_definitions,
                                     avc_equiv_local(lhs_dist_L4A_dict["val_L_sym"], rhs_dist_L4A_dict["val_L_sym"], P_A_val_sym, P_B_val_sym),
                                     model_vars_to_print=[P_A_val_sym, P_B_val_sym, La_val_sym, Lb_val_sym, Lc_val_sym,
                                                          sum_bc_L4A_dict["val_L_sym"], lhs_dist_L4A_dict["val_L_sym"],
                                                          prod_ab_L4A_dict["val_L_sym"], prod_ac_L4A_dict["val_L_sym"],
                                                          rhs_dist_L4A_dict["val_L_sym"]],
                                     op_result_dicts_for_debug=op_results_for_L4A_debug)
        s.pop()
        
        del s 
        print("-" * 80)

    print("\n====== AVC Adaptive Archetype Algebra Test Complete ======")

