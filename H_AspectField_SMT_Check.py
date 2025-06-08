from pysmt.shortcuts import Symbol, Int, Equals, And, Or, Solver, get_model
from pysmt.typing import INT as SMT_INT_TYPE
from typing import Dict, Tuple

def run_aspect_algebra_check():
    print("--- H_AspectField: SMT Sanity Check for Underlying Aspect Algebra ---")

    Z_aspect = Int(0) # Representing ZERO_UNIO aspect
    A_aspect = Int(1) # Representing AREO_UNIO aspect
    aspect_domain = [Z_aspect, A_aspect]
    aspect_py_domain = [0, 1] # For iterating

    # --- Symbolic operation for Multiplication Aspects ---
    # op_mul_aspect(in1, in2) -> out
    # Table cells: m_zz, m_za, m_az, m_aa
    m_zz = Symbol("m_zz", SMT_INT_TYPE)
    m_za = Symbol("m_za", SMT_INT_TYPE)
    m_az = Symbol("m_az", SMT_INT_TYPE)
    m_aa = Symbol("m_aa", SMT_INT_TYPE)
    mul_aspect_table_vars = [m_zz, m_za, m_az, m_aa]

    mul_assertions = []
    # Constrain output aspects to be 0 or 1
    for var in mul_aspect_table_vars:
        mul_assertions.append(Or(Equals(var, Z_aspect), Equals(var, A_aspect)))

    # avc_mul_v1.2 ("Areo Dominates") rules for Unio @ Unio:
    # ZU @ ZU -> ZU
    # ZU @ AU -> AU
    # AU @ ZU -> AU
    # AU @ AU -> AU
    mul_assertions.append(Equals(m_zz, Z_aspect))
    mul_assertions.append(Equals(m_za, A_aspect))
    mul_assertions.append(Equals(m_az, A_aspect))
    mul_assertions.append(Equals(m_aa, A_aspect))

    print("\n--- Checking for Multiplication Aspect Algebra (avc_mul_v1.2) ---")
    with Solver(name="z3") as s:
        for an_assertion in mul_assertions:
            s.add_assertion(an_assertion)
        
        result_mul = s.solve()
        if result_mul:
            print("  SAT: A consistent multiplication aspect operation exists.")
            model = s.get_model()
            print("    Multiplication Aspect Table (0=Z, 1=A):")
            print(f"      Z @ Z -> {model.get_value(m_zz).constant_value()}")
            print(f"      Z @ A -> {model.get_value(m_za).constant_value()}")
            print(f"      A @ Z -> {model.get_value(m_az).constant_value()}")
            print(f"      A @ A -> {model.get_value(m_aa).constant_value()}")
            # This table (00->0, 01->1, 10->1, 11->1) is MAX(a,b) or OR(a,b)
            print("    This corresponds to MAX(aspect1, aspect2) or Logical OR if Z=False, A=True.")
        else:
            print("  UNSAT: No consistent multiplication aspect operation found (UNEXPECTED).")

    # --- Symbolic operation for Division Aspects (Unio/Unio cases) ---
    # op_div_aspect(dividend_aspect, divisor_aspect) -> out
    # Table cells: d_zz, d_za, d_az, d_aa
    d_zz = Symbol("d_zz", SMT_INT_TYPE)
    d_za = Symbol("d_za", SMT_INT_TYPE)
    d_az = Symbol("d_az", SMT_INT_TYPE)
    d_aa = Symbol("d_aa", SMT_INT_TYPE)
    div_aspect_table_vars = [d_zz, d_za, d_az, d_aa]

    div_assertions = []
    for var in div_aspect_table_vars:
        div_assertions.append(Or(Equals(var, Z_aspect), Equals(var, A_aspect)))

    # avc_div_AltD_Balanced rules for Unio/Unio:
    # ZU / ZU -> ZU  (Preserve dividend aspect if divisor is ZU)
    # ZU / AU -> AU  (Areo divisor dominates -> AU)
    # AU / ZU -> AU  (Preserve dividend aspect if divisor is ZU)
    # AU / AU -> AU  (Areo divisor dominates -> AU)
    div_assertions.append(Equals(d_zz, Z_aspect)) # ZU / ZU -> ZU
    div_assertions.append(Equals(d_za, A_aspect)) # ZU / AU -> AU
    div_assertions.append(Equals(d_az, A_aspect)) # AU / ZU -> AU (Mistake here in my rule recap, AltD: AU/ZU -> AU)
    # Let's fix d_az for AltD: if divisor is ZU, preserve dividend. So AU/ZU -> AU.
    # This was correctly stated in my reasoning for AltD derivation (Y.2 Proposition): S7(AU/ZU) -> AU (by MI)
    # So, the rules based on "preserve dividend if divisor Z; Areo if divisor A" are:
    # ZU / ZU -> ZU
    # ZU / AU -> AU
    # AU / ZU -> AU
    # AU / AU -> AU
    # This set of rules is identical to multiplication aspects.

    div_assertions.append(Equals(d_aa, A_aspect)) # AU / AU -> AU

    print("\n--- Checking for Division Aspect Algebra (avc_div_AltD_Balanced Unio/Unio cases) ---")
    print("    Rules: ZU/ZU->ZU; ZU/AU->AU; AU/ZU->AU; AU/AU->AU") # Clarifying applied rules
    with Solver(name="z3") as s:
        for an_assertion in div_assertions:
            s.add_assertion(an_assertion)
        
        result_div = s.solve()
        if result_div:
            print("  SAT: A consistent division aspect operation for Unio/Unio exists.")
            model = s.get_model()
            print("    Division Aspect Table for Unio/Unio (0=Z, 1=A):")
            print(f"      Z / Z -> {model.get_value(d_zz).constant_value()}")
            print(f"      Z / A -> {model.get_value(d_za).constant_value()}")
            print(f"      A / Z -> {model.get_value(d_az).constant_value()}")
            print(f"      A / A -> {model.get_value(d_aa).constant_value()}")
            if (model.get_value(m_zz) == model.get_value(d_zz) and
                model.get_value(m_za) == model.get_value(d_za) and
                model.get_value(m_az) == model.get_value(d_az) and
                model.get_value(m_aa) == model.get_value(d_aa)):
                print("    This division aspect table for U/U is IDENTICAL to the multiplication aspect table.")
                print("    It also corresponds to MAX(dividend_aspect, divisor_aspect) or Logical OR.")
            else:
                print("    This division aspect table for U/U DIFFERS from the multiplication aspect table.")

        else:
            print("  UNSAT: No consistent division aspect operation found (UNEXPECTED).")

if __name__ == "__main__":
    run_aspect_algebra_check()
