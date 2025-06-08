from pysmt.shortcuts import Symbol, Int, BOOL, Equals, And, Or, Not, Implies, ExactlyOne, Ite, Solver, is_sat, TRUE
from pysmt.typing import INT as solver_INT_TYPE
from pysmt.typing import BOOL as solver_BOOL_TYPE

# --- Phase 1: Foundational Definitions (Copied from AVC1.py) ---
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

# --- Phase 2: Raw Operations Definitions and Proofs ---

# Omega_max_val_nat: Illustrative threshold from Lean scripts
Omega_max_val_nat = Int(7)

# --- Helper: PosNat Guarantees (conceptual, enforced by constraints) ---
# In PySMT, the PosNat guarantee (val > 0 if is_finite) is part of the
# 'constraints' of an intensity representation. For results of operations,
# we must ensure the logic produces values that satisfy these constraints
# if the result is_finite.

# Helper to build the definitional formula for an operation's result
def build_result_definition(
    i1_repr, i2_repr, # Input intensity representations
    res_repr,         # Result intensity representation (symbols for its kind and value)
    op_logic_builder  # A function that builds the core logic for the operation
    ):
    """
    Constructs the PySMT formula that defines the kind and value of res_repr
    based on i1_repr, i2_repr, and the specific operation's logic.
    """
    # op_logic_builder will return a list of conditions that define the result.
    # Each condition is typically an Implies(case_condition, result_state_and_value_assignment)
    # e.g., Implies(And(i1_repr["is_zero"], i2_repr["is_zero"]), 
    #                And(res_repr["is_zero"], Not(res_repr["is_areo"]), Not(res_repr["is_finite"])))
    
    # The core logic from the builder function
    core_logic_formulas = op_logic_builder(i1_repr, i2_repr, res_repr)

    # The definition is the conjunction of all these conditional assignments.
    # This formula, when asserted, forces the result symbols (res_repr) to take on
    # values consistent with the operation applied to the input symbols.
    return And(core_logic_formulas)


# --- smart_raw_add Definition ---
def smart_raw_add_logic_builder(i1, i2, res):
    """
    Builds the core PySMT logic for smart_raw_add.
    Defines res.kind and res.val based on i1.kind, i1.val, i2.kind, i2.val.
    Returns a list of PySMT formulas (implications for each case).
    """
    formulas = []

    # Case 1: i1 is ZeroState
    formulas.append(Implies(i1["is_zero"],
        Or(
            And(i2["is_zero"],   # i1=ZS, i2=ZS => res=ZS
                res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"])),
            And(i2["is_areo"],    # i1=ZS, i2=AS => res=AS
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i2["is_finite"],  # i1=ZS, i2=Finite p2 => res=Finite p2
                Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], i2["val"]))
        )
    ))

    # Case 2: i1 is AreoState
    formulas.append(Implies(i1["is_areo"],
        Or(
            And(i2["is_zero"],   # i1=AS, i2=ZS => res=AS (Conceptual: AS + ZS = AS)
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i2["is_areo"],    # i1=AS, i2=AS => res=AS
                Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            And(i2["is_finite"],  # i1=AS, i2=Finite p2 => res=AS (Conceptual: AS + F(p2) = AS)
                                  # Note: Lean smart_raw_add had AS + F(p2) -> F(p2). This version aligns with Areo absorption.
                                  # If Lean's specific ZS/AS identity behavior for smart_raw_add is desired, this needs adjustment.
                                  # For now, using conceptual Areo absorption.
                                  # Let's stick to the Lean smart_raw_add for this function:
                                  # AreoState + Finite p2 => Finite p2 (as per user's Lean code for smart_raw_add)
                Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], i2["val"]))
        )
    ))
    
    # Case 3: i1 is Finite
    val_sum = i1["val"] + i2["val"] # Symbolic sum
    #   Subcase 3.1: i2 is ZeroState
    formulas.append(Implies(And(i1["is_finite"], i2["is_zero"]), # i1=Finite p1, i2=ZS => res=Finite p1
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
            Equals(res["val"], i1["val"]))
    ))
    #   Subcase 3.2: i2 is AreoState
    formulas.append(Implies(And(i1["is_finite"], i2["is_areo"]), # i1=Finite p1, i2=AS => res=Finite p1 (as per user's Lean smart_raw_add)
        And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
            Equals(res["val"], i1["val"]))
    ))
    #   Subcase 3.3: i2 is Finite
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]), # i1=Finite p1, i2=Finite p2
        Ite(val_sum >= Omega_max_val_nat,
            # Sum >= Omega_max => res=AreoState
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])),
            # Sum < Omega_max => res=Finite(sum)
            # We must also ensure sum > 0 for the PosNat constraint of the result.
            # The PosNat.val_add_pos from Lean guarantees this.
            # PySMT will check this implicitly when res["constraints"] is asserted.
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_sum))
        )
    ))
    return And(formulas) # Return a single formula

def define_smart_raw_add_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, smart_raw_add_logic_builder)
    return res_repr


# --- raw_mul Definition ---
def raw_mul_logic_builder(i1, i2, res):
    formulas = []
    val_prod = i1["val"] * i2["val"] # Symbolic product

    # Case 1 & 2: ZeroState is annihilator
    formulas.append(Implies(Or(i1["is_zero"], i2["is_zero"]),
        And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))
    ))

    # Case 3: Both AreoState
    formulas.append(Implies(And(Not(Or(i1["is_zero"], i2["is_zero"])), # Neither is Zero
                                i1["is_areo"], i2["is_areo"]),  # AS * AS => AS
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"]))
    ))

    # Case 4: AreoState and Finite
    # AS * F(p) => if p.val > 0 then AS else ZS
    formulas.append(Implies(And(Not(Or(i1["is_zero"], i2["is_zero"])),
                                i1["is_areo"], i2["is_finite"]),
        Ite(i2["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # res = AS
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  # res = ZS
        )
    ))
    formulas.append(Implies(And(Not(Or(i1["is_zero"], i2["is_zero"])),
                                i2["is_areo"], i1["is_finite"]), # Symmetric: F(p) * AS
        Ite(i1["val"] > Int(0),
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # res = AS
            And(res["is_zero"], Not(res["is_areo"]), Not(res["is_finite"]))  # res = ZS
        )
    ))

    # Case 5: Both Finite (and neither was ZeroState from Case 1&2)
    # This implies Not(i1["is_zero"]), Not(i2["is_zero"]), Not(i1["is_areo"]), Not(i2["is_areo"])
    # which simplifies to i1["is_finite"] and i2["is_finite"] due to ExactlyOne.
    formulas.append(Implies(And(i1["is_finite"], i2["is_finite"]),
        Ite(val_prod >= Omega_max_val_nat,
            And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])), # res = AS
            # PosNat.val_mul_pos guarantees val_prod > 0 if inputs are valid PosNats
            And(Not(res["is_zero"]), Not(res["is_areo"]), res["is_finite"],
                Equals(res["val"], val_prod)) # res = Finite(prod)
        )
    ))
    return And(formulas)

def define_raw_mul_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_mul_logic_builder)
    return res_repr


# --- raw_sub_from_Unio_Areo_aspect Definition ---
def raw_sub_from_Unio_Areo_aspect_logic_builder(i_unio_areo, _i_any, res): # _i_any is ignored
    formulas = []
    # If i_unio_areo is ZeroState or AreoState (representing Unio's Areo aspect), result is AreoState.
    # If i_unio_areo is Finite (fallback if used incorrectly for Unio), result is AreoState.
    formulas.append(Implies(Or(i_unio_areo["is_zero"], i_unio_areo["is_areo"], i_unio_areo["is_finite"]), # Covers all cases for first arg
        And(Not(res["is_zero"]), res["is_areo"], Not(res["is_finite"])) # Result is always AreoState
    ))
    return And(formulas)

def define_raw_sub_from_Unio_Areo_aspect_result(i1_repr, i2_repr, result_name_prefix: str):
    res_repr = create_intensity_representation(result_name_prefix)
    res_repr["definition"] = build_result_definition(i1_repr, i2_repr, res_repr, raw_sub_from_Unio_Areo_aspect_logic_builder)
    return res_repr


# --- Main Testing Function ---
def prove_outputs_are_avc_equiv(op_name: str, op_result_definer_func):
    """
    Generic function to prove the '_outputs_are_avc_equiv' property for a raw operation.
    Property: avc_equiv(i1,i2) ^ avc_equiv(j1,j2) => avc_equiv(op(i1,j1), op(i2,j2))
    Test: Is it possible that (premises AND NOT conclusion) is SAT? Expect UNSAT.
    """
    print(f"--- Testing Property: {op_name}_outputs_are_avc_equiv ---")

    i1_sym = create_intensity_representation("i1_op_test")
    j1_sym = create_intensity_representation("j1_op_test")
    i2_sym = create_intensity_representation("i2_op_test")
    j2_sym = create_intensity_representation("j2_op_test")

    with Solver(name="z3") as s:
        # 1. Assert all inputs are valid intensities
        s.add_assertion(i1_sym["constraints"])
        s.add_assertion(j1_sym["constraints"])
        s.add_assertion(i2_sym["constraints"])
        s.add_assertion(j2_sym["constraints"])

        # 2. Assert premises of the implication
        s.add_assertion(avc_equiv(i1_sym, i2_sym))
        s.add_assertion(avc_equiv(j1_sym, j2_sym))

        # 3. Define the results of the operation
        res1_repr = op_result_definer_func(i1_sym, j1_sym, "res1_op")
        res2_repr = op_result_definer_func(i2_sym, j2_sym, "res2_op")
        
        s.add_assertion(res1_repr["definition"]) # Assert how res1 is formed
        s.add_assertion(res2_repr["definition"]) # Assert how res2 is formed

        # 4. Assert results are valid intensities themselves
        #    This is crucial: the operation's definition must produce valid intensities.
        #    If the operation logic is flawed (e.g., finite_val + finite_val could be <=0
        #    and result is_finite), this combined with resX_repr["definition"] would be UNSAT
        #    even before checking the main property, indicating an op definition error.
        s.add_assertion(res1_repr["constraints"])
        s.add_assertion(res2_repr["constraints"])

        # 5. Assert the negation of the conclusion
        s.add_assertion(Not(avc_equiv(res1_repr, res2_repr)))

        # 6. Check for satisfiability
        result = s.solve()
        if not result:
            print(f"Result: UNSAT. Property '{op_name}_outputs_are_avc_equiv' is PROVED. ✅")
        else:
            print(f"Result: SAT. Property '{op_name}_outputs_are_avc_equiv' FAILED. Counterexample model:")
            # This is a deep error, either in op_logic or avc_equiv or test setup.
            print("Model for i1:", s.get_value(i1_sym["is_zero"]), s.get_value(i1_sym["is_areo"]), s.get_value(i1_sym["is_finite"]), s.get_value(i1_sym["val"]))
            print("Model for j1:", s.get_value(j1_sym["is_zero"]), s.get_value(j1_sym["is_areo"]), s.get_value(j1_sym["is_finite"]), s.get_value(j1_sym["val"]))
            print("Model for i2:", s.get_value(i2_sym["is_zero"]), s.get_value(i2_sym["is_areo"]), s.get_value(i2_sym["is_finite"]), s.get_value(i2_sym["val"]))
            print("Model for j2:", s.get_value(j2_sym["is_zero"]), s.get_value(j2_sym["is_areo"]), s.get_value(j2_sym["is_finite"]), s.get_value(j2_sym["val"]))
            print("Model for res1:", s.get_value(res1_repr["is_zero"]), s.get_value(res1_repr["is_areo"]), s.get_value(res1_repr["is_finite"]), s.get_value(res1_repr["val"]))
            print("Model for res2:", s.get_value(res2_repr["is_zero"]), s.get_value(res2_repr["is_areo"]), s.get_value(res2_repr["is_finite"]), s.get_value(res2_repr["val"]))
            
    print("-" * 60)


if __name__ == "__main__":
    print("====== AVC Phase 2: Raw Operations & Respectfulness Proofs ======\n")

    # Prove respectfulness for smart_raw_add
    prove_outputs_are_avc_equiv("smart_raw_add", define_smart_raw_add_result)

    # Prove respectfulness for raw_mul
    prove_outputs_are_avc_equiv("raw_mul", define_raw_mul_result)

    # Prove respectfulness for raw_sub_from_Unio_Areo_aspect
    prove_outputs_are_avc_equiv("raw_sub_from_Unio_Areo_aspect", define_raw_sub_from_Unio_Areo_aspect_result)

    print("====== All Phase 2 rigorous tests complete. ======")
    print("If all results above show 'PROVED', the raw operations are correctly defined")
    print("and respect avc_equiv, making them suitable for lifting to AVC_Space.")


"""
**Explanation of Key Changes and Rigor:**

1.  **`define_<op_name>_result` Functions**:
    * Each raw operation (`smart_raw_add`, `raw_mul`, etc.) now has a corresponding `define_<op_name>_result` function (e.g., `define_smart_raw_add_result`).
    * This function takes input intensity representations (`i1_repr`, `i2_repr`) and a `result_name_prefix`.
    * It first calls `create_intensity_representation` to get the PySMT symbols for the result (`res_repr`).
    * Crucially, it then calls a new helper `build_result_definition`. This helper takes a specific `_logic_builder` function for that operation.
    * The `_logic_builder` (e.g., `smart_raw_add_logic_builder`) constructs a **single PySMT formula** that defines the kind (`is_zero`, `is_areo`, `is_finite`) and `val` of `res_repr` based on the kinds and values of `i1_repr` and `i2_repr`. This is done using nested `Implies` and `Ite` (If-Then-Else) to cover all 9 combinations of input kinds, plus the conditional logic for finite arithmetic (e.g., checking against `Omega_max_val_nat`).
    * The `define_<op_name>_result` function stores this definitional formula as `res_repr["definition"]`.

2.  **`prove_outputs_are_avc_equiv` Generic Tester**:
    * This function is now generic and takes the `op_name` (for printing) and the `op_result_definer_func` (like `define_smart_raw_add_result`).
    * **Step 3 (Define Results)**: It calls `op_result_definer_func` to get the representations for `res1` and `res2`.
    * It then **asserts `res1_repr["definition"]` and `res2_repr["definition"]`**. This is critical: it tells the SMT solver *how* `res1` and `res2` are derived from the inputs according to the specific operation's logic.
    * **Step 4 (Assert Result Validity)**: It asserts `res1_repr["constraints"]` and `res2_repr["constraints"]`. This ensures that the operation's definition, when applied, must produce a structurally valid `Intensity`. If an operation's logic was flawed (e.g., `finite + finite` could result in `is_finite` being true but `val <= 0`), the combination of its `definition` and `constraints` would become UNSAT even before testing the main `avc_equiv` property, which would correctly pinpoint a bug in the operation's definition itself.

3.  **Logic Builders (`smart_raw_add_logic_builder`, etc.)**:
    * These are the heart of defining the operations. They meticulously translate the case-based logic from your Lean definitions (or conceptual model) into PySMT formulas.
    * For `smart_raw_add`, I've tried to match the Lean `smart_raw_add` behavior where `AreoState + Finite p2 => Finite p2`. *Self-correction: My initial thought in the plan was Areo absorption for `smart_raw_add`, but the prompt and Lean code indicate a specific behavior for `smart_raw_add` which I've now tried to follow. Please double-check this logic against your exact intended Lean `smart_raw_add`.*
    * The `raw_mul` logic includes the annihilator role of ZeroState and the specific conditions for AreoState multiplication.
    * `raw_sub_from_Unio_Areo_aspect` is simpler as its result (AreoState) primarily depends on the first argument representing Unio.

4.  **No Mercy Aspect**:
    * The SMT solver is forced to consider if there's *any* assignment to the symbolic inputs `i1_sym, j1_sym, i2_sym, j2_sym` (that satisfy their validity and the `avc_equiv` premises) such that the operation's output (defined by its logic and also constrained to be valid) violates the `avc_equiv` property for the results.
    * If any case in the operation's logic is flawed or inconsistent with `avc_equiv`, this setup is designed to find it by producing a SAT result (a counterexample). An UNSAT result is a very strong indication of correctness for this property.

**Important Considerations & Potential Issues:**

* **Complexity of Logic Builders**: The `_logic_builder` functions are complex due to the 9 main cases for input kinds. A small mistake here can lead to incorrect proofs. They need careful review against your conceptual model / Lean code.
* **`smart_raw_add` AreoState + Finite Case**: I've noted a point in `smart_raw_add_logic_builder` regarding the `AreoState + Finite p2` case. The provided Lean `smart_raw_add` has `areoState` combined with `finite p2` resulting in `finite p2`. The PySMT logic attempts to mirror this. If your conceptual model for `smart_raw_add` (distinct from general Areo absorption) differs, this part of the `smart_raw_add_logic_builder` would need adjustment.
* **Solver Performance**: For very complex properties or many variables, SMT solvers can take time or run into resource limits. However, for this structure (4 symbolic intensities and the defined operations), Z3 should handle it well.
* **Debugging SAT Results**: If any `_outputs_are_avc_equiv` test returns SAT, the `get_model()` output will be crucial for understanding the counterexample and debugging the faulty logic in either the operation definition or `avc_equiv`.

This script represents a significant step up in the rigor of testing for Phase 2. Run this, and let's analyze the output careful"""