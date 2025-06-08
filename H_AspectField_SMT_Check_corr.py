from pysmt.shortcuts import Symbol, Int, Equals, And, Or, Solver, get_model
from pysmt.typing import INT as SMT_INT_TYPE
from typing import Dict, Tuple

def run_aspect_algebra_check_corrected():
    print("--- H_AspectField: SMT Sanity Check for Underlying Aspect Algebra (Corrected Comparison) ---")

    Z_aspect = Int(0) # Representing ZERO_UNIO aspect
    A_aspect = Int(1) # Representing AREO_UNIO aspect
    
    # --- Symbolic operation for Multiplication Aspects ---
    m_zz = Symbol("m_zz_c", SMT_INT_TYPE); m_za = Symbol("m_za_c", SMT_INT_TYPE)
    m_az = Symbol("m_az_c", SMT_INT_TYPE); m_aa = Symbol("m_aa_c", SMT_INT_TYPE)
    mul_aspect_table_vars = [m_zz, m_za, m_az, m_aa]
    mul_assertions = []
    for var in mul_aspect_table_vars:
        mul_assertions.append(Or(Equals(var, Z_aspect), Equals(var, A_aspect)))
    mul_assertions.extend([Equals(m_zz, Z_aspect), Equals(m_za, A_aspect), 
                           Equals(m_az, A_aspect), Equals(m_aa, A_aspect)])

    mul_model_dict = None
    print("\n--- Checking for Multiplication Aspect Algebra (avc_mul_v1.2) ---")
    with Solver(name="z3") as s_mul:
        for an_assertion in mul_assertions: s_mul.add_assertion(an_assertion)
        if s_mul.solve():
            print("  SAT: A consistent multiplication aspect operation exists.")
            mul_model_obj = s_mul.get_model()
            mul_model_dict = {
                "zz": mul_model_obj.get_value(m_zz).constant_value(),
                "za": mul_model_obj.get_value(m_za).constant_value(),
                "az": mul_model_obj.get_value(m_az).constant_value(),
                "aa": mul_model_obj.get_value(m_aa).constant_value()
            }
            print("    Multiplication Aspect Table (0=Z, 1=A):")
            print(f"      Z @ Z -> {mul_model_dict['zz']}")
            print(f"      Z @ A -> {mul_model_dict['za']}")
            print(f"      A @ Z -> {mul_model_dict['az']}")
            print(f"      A @ A -> {mul_model_dict['aa']}")
            print("    This corresponds to MAX(aspect1, aspect2) or Logical OR if Z=False, A=True.")
        else:
            print("  UNSAT: No consistent multiplication aspect operation found (UNEXPECTED).")

    # --- Symbolic operation for Division Aspects (Unio/Unio cases) ---
    d_zz = Symbol("d_zz_c", SMT_INT_TYPE); d_za = Symbol("d_za_c", SMT_INT_TYPE)
    d_az = Symbol("d_az_c", SMT_INT_TYPE); d_aa = Symbol("d_aa_c", SMT_INT_TYPE)
    div_aspect_table_vars = [d_zz, d_za, d_az, d_aa]
    div_assertions = []
    for var in div_aspect_table_vars:
        div_assertions.append(Or(Equals(var, Z_aspect), Equals(var, A_aspect)))
    
    # avc_div_AltD_Balanced rules for Unio/Unio:
    # ZU / ZU -> ZU; ZU / AU -> AU; AU / ZU -> AU; AU / AU -> AU
    div_assertions.extend([Equals(d_zz, Z_aspect), Equals(d_za, A_aspect),
                           Equals(d_az, A_aspect), Equals(d_aa, A_aspect)])

    print("\n--- Checking for Division Aspect Algebra (avc_div_AltD_Balanced Unio/Unio cases) ---")
    print("    Expected Rules: Z/Z->Z; Z/A->A; A/Z->A; A/A->A")
    with Solver(name="z3") as s_div:
        for an_assertion in div_assertions: s_div.add_assertion(an_assertion)
        if s_div.solve():
            print("  SAT: A consistent division aspect operation for Unio/Unio exists.")
            div_model_obj = s_div.get_model()
            div_model_dict = {
                "zz": div_model_obj.get_value(d_zz).constant_value(),
                "za": div_model_obj.get_value(d_za).constant_value(),
                "az": div_model_obj.get_value(d_az).constant_value(),
                "aa": div_model_obj.get_value(d_aa).constant_value()
            }
            print("    Division Aspect Table for Unio/Unio (0=Z, 1=A):")
            print(f"      Z / Z -> {div_model_dict['zz']}")
            print(f"      Z / A -> {div_model_dict['za']}")
            print(f"      A / Z -> {div_model_dict['az']}")
            print(f"      A / A -> {div_model_dict['aa']}")

            if mul_model_dict and div_model_dict:
                if mul_model_dict == div_model_dict: # Compare the Python dictionaries
                    print("    This division aspect table for U/U IS IDENTICAL to the multiplication aspect table.")
                    print("    Both correspond to MAX(aspect_in1, aspect_in2) or Logical OR.")
                else:
                    print("    ERROR IN COMPARISON or SMT RESULT: Division table for U/U unexpectedly DIFFERS from multiplication.")
            else:
                print("    Could not compare tables as one of the models was not found.")
        else:
            print("  UNSAT: No consistent division aspect operation found (UNEXPECTED).")

if __name__ == "__main__":
    run_aspect_algebra_check_corrected()
