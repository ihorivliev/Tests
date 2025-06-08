import itertools
from typing import Union, List, Any, Tuple, Callable, Dict

# --- Revised Core AVCA Specification ---
# Global Omega, needs to be set by the test runner for each iteration
Omega: int = 0

class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: str):
        assert aspect in ("zero","areo")
        self.aspect = aspect
    def __eq__(self, other): # All Unio objects are algebraically the same
        return isinstance(other, Unio)
    def __hash__(self): # For use in sets/dict keys if needed
        return hash(Unio) 
    def __repr__(self):
        return f"Unio({self.aspect!r})"

ZERO_UNIO = Unio("zero")
AREO_UNIO = Unio("areo")

AVCVal = Union[int, Unio]

def _check_val(x: AVCVal):
    global Omega
    if Omega == 0:
        raise ValueError("Omega must be set before _check_val can be used.")
    if isinstance(x, Unio):
        return
    if not isinstance(x, int):
        raise TypeError(f"AVC value must be int or Unio, got {type(x)}")
    if Omega == 1 and isinstance(x, int): # No DFI if Omega is 1
         raise ValueError(f"DFI ints not allowed when Omega=1, got {x}")
    if Omega > 1 and not (1 <= x < Omega): # DFI is {1, ..., Omega-1}
        raise ValueError(f"DFI ints must lie in [1...{Omega-1}], got {x} for Omega={Omega}")

def avc_add(a: AVCVal, b: AVCVal) -> AVCVal:
    """⊕ : S × S → S (cyclic addition, “360° loop”)"""
    global Omega
    _check_val(a); _check_val(b)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    s = a + b
    return s if s < Omega else ZERO_UNIO

def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal:
    """⊖ : S × S → S (stuck-at-Areo subtraction)"""
    global Omega
    _check_val(a); _check_val(b)
    if isinstance(b, Unio): return a
    if isinstance(a, Unio): return AREO_UNIO
    return (a - b) if a > b else AREO_UNIO

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal:
    """⊗ : S × S → S (cyclic multiplication)"""
    global Omega
    _check_val(a); _check_val(b)
    if isinstance(a, Unio):
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    if isinstance(b, Unio): # a must be DFI here
        return ZERO_UNIO if b.aspect=="zero" else AREO_UNIO
    p = a * b
    return p if p < Omega else AREO_UNIO

def avc_div(a: AVCVal, b: AVCVal) -> AVCVal:
    """⊘ : S × S → S (cyclic division)"""
    global Omega
    _check_val(a); _check_val(b)
    if isinstance(a, Unio):
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    if isinstance(b, Unio): # a must be DFI here
        return AREO_UNIO
    # Both a, b are DFI ints. b cannot be 0 if it's a DFI (1 <= b < Omega)
    # Python's divmod(a,0) raises ZeroDivisionError. _check_val ensures b >= 1 for DFI.
    q, r = divmod(a, b)
    return q if (r == 0 and 1 <= q < Omega) else AREO_UNIO

# --- Testing Harness ---
S_test: List[AVCVal] = []

def generate_s_test():
    global S_test, Omega
    if Omega == 0:
        raise ValueError("Omega must be set before S_test can be generated.")
    S_test = [ZERO_UNIO, AREO_UNIO] 
    if Omega > 1:
        S_test.extend(list(range(1, Omega)))

test_results_summary: Dict[int, Dict[str, int]] = {}
test_failures_details: List[Dict[str, Any]] = []

def initialize_omega_results(omega_val: int):
    if omega_val not in test_results_summary:
        test_results_summary[omega_val] = {"passed": 0, "failed": 0}

def record_test(property_name: str, omega_val: int, success: bool, message: str = "", counterexample_data: Any = None):
    status_emoji = "✅" if success else "❌"
    full_message = f"{status_emoji} Omega={omega_val}: Property '{property_name}' {'PASSED' if success else 'FAILED'}."
    if message:
        full_message += f" {message}"
    print(full_message)
    
    initialize_omega_results(omega_val)
    if success:
        test_results_summary[omega_val]["passed"] += 1
    else:
        test_results_summary[omega_val]["failed"] += 1
        failure_detail = {
            "property": property_name,
            "omega": omega_val,
            "message": message,
            "counterexample": counterexample_data
        }
        test_failures_details.append(failure_detail)
        if counterexample_data:
            # Ensure counterexample data is also using repr for Unio objects
            if isinstance(counterexample_data, dict):
                ce_str_parts = []
                for k, v in counterexample_data.items():
                    ce_str_parts.append(f"{k}={v!r}")
                print(f"    Counterexample: {{{', '.join(ce_str_parts)}}}")
            else:
                print(f"    Counterexample: {counterexample_data!r}")


def is_dfi(val: AVCVal) -> bool:
    global Omega
    if Omega == 1: return False 
    return isinstance(val, int) and 1 <= val < Omega

# --- Test Functions for Core AVCA Properties ---

def test_totality():
    property_name = "Operation Totality"
    ops = {"add": avc_add, "sub": avc_sub, "mul": avc_mul, "div": avc_div}
    all_total = True
    ce_info = None
    for op_name, op_func in ops.items():
        for a in S_test:
            for b in S_test:
                try:
                    res = op_func(a, b)
                    is_valid_member_of_S = isinstance(res, Unio) or \
                                           (Omega > 1 and isinstance(res, int) and 1 <= res < Omega) or \
                                           (Omega == 1 and isinstance(res, Unio)) # For Omega=1, S only has Unio aspects
                    if not is_valid_member_of_S:
                        all_total = False
                        ce_info = {"op": op_name, "a": a, "b": b, "res": res, "Omega": Omega, "reason": "Result not in S_test"}
                        break
                except ValueError as ve: # Expected from _check_val if inputs are bad (should not happen with S_test)
                    all_total = False
                    ce_info = {"op": op_name, "a": a, "b": b, "Omega": Omega, "error": f"ValueError: {ve}"}
                    break
                except TypeError as te:
                     all_total = False
                     ce_info = {"op": op_name, "a": a, "b": b, "Omega": Omega, "error": f"TypeError: {te}"}
                     break
                except Exception as e: # Catch any other unexpected errors
                    all_total = False
                    ce_info = {"op": op_name, "a": a, "b": b, "Omega": Omega, "error": f"Unexpected {type(e).__name__}: {e}"}
                    break
            if not all_total: break
        if not all_total: break
    record_test(property_name, Omega, all_total, "" if all_total else "Operation resulted in value outside S or raised error.", ce_info)

def test_commutativity(op_func: Callable, op_name: str):
    property_name = f"Commutativity of {op_name} (a op b == b op a)"
    all_commutative = True
    ce_info = None
    for a in S_test:
        for b in S_test:
            res1 = op_func(a,b)
            res2 = op_func(b,a)
            if res1 != res2: 
                all_commutative = False
                ce_info = {"a":a, "b":b, "res1":res1, "res2":res2}
                break
        if not all_commutative: break
    record_test(property_name, Omega, all_commutative, "" if all_commutative else f"{op_name} not commutative.", ce_info)

def test_associativity(op_func: Callable, op_name: str, expected_to_hold: bool):
    property_name = f"Associativity of {op_name} ((a op b) op c == a op (b op c))"
    holds_universally = True
    found_counterexample_when_expected_not_to_hold = False
    ce_info = None

    # For Omega=1, S_test effectively has one algebraic value (Unio). Associativity is trivial.
    if Omega == 1:
        record_test(property_name, Omega, expected_to_hold, "(Trivially holds for Omega=1)" if expected_to_hold else "(Cannot find counterexample for Omega=1, trivially holds)")
        return

    for a in S_test:
        for b in S_test:
            for c in S_test:
                lhs = op_func(op_func(a,b),c)
                rhs = op_func(a,op_func(b,c))
                if lhs != rhs:
                    holds_universally = False
                    found_counterexample_when_expected_not_to_hold = True
                    ce_info = {"a":a, "b":b, "c":c, "lhs":lhs, "rhs":rhs}
                    break
            if not holds_universally and expected_to_hold: break 
            if found_counterexample_when_expected_not_to_hold and not expected_to_hold: break 
        if not holds_universally and expected_to_hold: break
        if found_counterexample_when_expected_not_to_hold and not expected_to_hold: break
    
    if expected_to_hold:
        record_test(property_name, Omega, holds_universally, "" if holds_universally else f"{op_name} FAILED associativity.", ce_info)
    else: # Expected NOT to hold (i.e., expect non-associativity)
        record_test(property_name, Omega, found_counterexample_when_expected_not_to_hold, 
                    f"Non-associativity of {op_name} CONFIRMED as expected." if found_counterexample_when_expected_not_to_hold 
                    else f"Non-associativity of {op_name} NOT found (unexpectedly associative).", 
                    ce_info if found_counterexample_when_expected_not_to_hold else "No counterexample found.")

def test_distributivity_mul_over_add(expected_to_hold: bool):
    property_name = "Distributivity of Mul over Add (a*(b+c) == (a*b)+(a*c))"
    holds_universally = True
    found_counterexample_when_expected_not_to_hold = False
    ce_info = None

    if Omega == 1:
        record_test(property_name, Omega, expected_to_hold, "(Trivially holds for Omega=1)" if expected_to_hold else "(Cannot find counterexample for Omega=1, trivially holds)")
        return

    for a in S_test:
        for b in S_test:
            for c in S_test:
                lhs = avc_mul(a, avc_add(b,c))
                rhs = avc_add(avc_mul(a,b), avc_mul(a,c))
                if lhs != rhs:
                    holds_universally = False
                    found_counterexample_when_expected_not_to_hold = True
                    ce_info = {"a":a, "b":b, "c":c, "lhs":lhs, "rhs":rhs}
                    break
            if not holds_universally and expected_to_hold: break
            if found_counterexample_when_expected_not_to_hold and not expected_to_hold: break
        if not holds_universally and expected_to_hold: break
        if found_counterexample_when_expected_not_to_hold and not expected_to_hold: break

    if expected_to_hold:
        record_test(property_name, Omega, holds_universally, "" if holds_universally else "FAILED distributivity.", ce_info)
    else: # Expected NOT to hold
        record_test(property_name, Omega, found_counterexample_when_expected_not_to_hold,
                    "Non-distributivity CONFIRMED as expected." if found_counterexample_when_expected_not_to_hold
                    else "Non-distributivity NOT found (unexpectedly distributive).",
                    ce_info if found_counterexample_when_expected_not_to_hold else "No counterexample found.")

def test_subtraction_asymmetry():
    property_name = "Subtraction Asymmetry"
    holds = True
    ce_info = None
    for x in S_test:
        # Test x - Unio == x
        if avc_sub(x, ZERO_UNIO) != x:
            holds=False; ce_info={"op":f"{x!r} - {ZERO_UNIO!r}", "got":avc_sub(x,ZERO_UNIO), "exp":x}; break
        if avc_sub(x, AREO_UNIO) != x:
            holds=False; ce_info={"op":f"{x!r} - {AREO_UNIO!r}", "got":avc_sub(x,AREO_UNIO), "exp":x}; break

        # Test Unio - x 
        if is_dfi(x):
            if avc_sub(ZERO_UNIO, x) != AREO_UNIO:
                holds=False; ce_info={"op":f"{ZERO_UNIO!r} - {x!r}", "got":avc_sub(ZERO_UNIO,x), "exp":AREO_UNIO}; break
            if avc_sub(AREO_UNIO, x) != AREO_UNIO:
                holds=False; ce_info={"op":f"{AREO_UNIO!r} - {x!r}", "got":avc_sub(AREO_UNIO,x), "exp":AREO_UNIO}; break
        elif isinstance(x, Unio): # Unio - Unio
            # avc_sub(Unio(aspect1), Unio(aspect2)) returns Unio(aspect1)
            if avc_sub(ZERO_UNIO, x) != ZERO_UNIO: 
                holds=False; ce_info={"op":f"{ZERO_UNIO!r} - {x!r}", "got":avc_sub(ZERO_UNIO,x), "exp":ZERO_UNIO}; break
            if avc_sub(AREO_UNIO, x) != AREO_UNIO: 
                holds=False; ce_info={"op":f"{AREO_UNIO!r} - {x!r}", "got":avc_sub(AREO_UNIO,x), "exp":AREO_UNIO}; break
    record_test(property_name, Omega, holds, "" if holds else "Asymmetry rules violated.", ce_info)

def test_dfi_haven():
    property_name = "DFI-Haven (Standard ops if no wrap/overflow)"
    if Omega <= 1:
        record_test(property_name, Omega, True, "Holds (vacuously, no DFI).")
        return
    
    dfi_elements = [i for i in S_test if is_dfi(i)] # Correctly get DFI elements
    if not dfi_elements: # Should only happen if Omega = 1, already handled
        record_test(property_name, Omega, True, "Holds (vacuously, DFI list empty).")
        return

    all_match = True
    ce_info = None

    for a in dfi_elements:
        for b in dfi_elements:
            # Addition
            s_std = a + b
            s_avc = avc_add(a, b)
            if s_std < Omega:
                if s_avc != s_std: all_match = False; ce_info = {"op":"add", "a":a, "b":b, "std":s_std, "avc":s_avc, "cond":"<Omega"}; break
            else: # s_std >= Omega
                if s_avc != ZERO_UNIO: all_match = False; ce_info = {"op":"add", "a":a, "b":b, "std_overflow":s_std, "avc":s_avc, "exp_ovfl":ZERO_UNIO}; break
            
            # Subtraction
            sub_avc = avc_sub(a,b)
            if a > b:
                sub_std = a - b
                if sub_avc != sub_std: all_match = False; ce_info = {"op":"sub", "a":a, "b":b, "std":sub_std, "avc":sub_avc, "cond":"a>b"}; break
            else: # a <= b
                if sub_avc != AREO_UNIO: all_match = False; ce_info = {"op":"sub", "a":a, "b":b, "std_underflow_eq":None, "avc":sub_avc, "exp_underfl_eq":AREO_UNIO}; break

            # Multiplication
            p_std = a * b
            p_avc = avc_mul(a,b)
            if p_std < Omega:
                if p_avc != p_std: all_match = False; ce_info = {"op":"mul", "a":a, "b":b, "std":p_std, "avc":p_avc, "cond":"<Omega"}; break
            else: # p_std >= Omega
                if p_avc != AREO_UNIO: all_match = False; ce_info = {"op":"mul", "a":a, "b":b, "std_overflow":p_std, "avc":p_avc, "exp_ovfl":AREO_UNIO}; break

            # Division (b is DFI, so b >= 1)
            q_avc = avc_div(a,b)
            if a % b == 0:
                q_std = a // b
                if 1 <= q_std < Omega:
                    if q_avc != q_std: all_match = False; ce_info = {"op":"div", "a":a, "b":b, "std":q_std, "avc":q_avc, "cond":"clean DFI quot"}; break
                else: # quotient out of DFI range or not positive
                    if q_avc != AREO_UNIO: all_match = False; ce_info = {"op":"div", "a":a, "b":b, "std_bad_quot":q_std, "avc":q_avc, "exp_bad_quot":AREO_UNIO}; break
            else: # not clean division
                if q_avc != AREO_UNIO: all_match = False; ce_info = {"op":"div", "a":a, "b":b, "std_non_exact":None, "avc":q_avc, "exp_non_exact":AREO_UNIO}; break
        if not all_match: break
    record_test(property_name, Omega, all_match, "" if all_match else "DFI operations deviate from standard behavior/overflow rules.", ce_info)


def test_stuck_at_areo():
    property_name = "Stuck-at-Areo (Unio - DFI_k == AREO_UNIO)"
    if Omega <= 1: # No DFI elements
        record_test(property_name, Omega, True, "Holds (vacuously, no DFI k).")
        return
    
    dfi_elements = [i for i in S_test if is_dfi(i)]
    if not dfi_elements: # Should be caught by Omega <= 1
         record_test(property_name, Omega, True, "Holds (vacuously, DFI list empty).")
         return

    all_stuck = True
    ce_info = None
    for k in dfi_elements:
        if avc_sub(ZERO_UNIO, k) != AREO_UNIO:
            all_stuck = False; ce_info = {"minuend":ZERO_UNIO, "subtrahend":k, "res":avc_sub(ZERO_UNIO,k), "exp":AREO_UNIO}; break
        if avc_sub(AREO_UNIO, k) != AREO_UNIO:
            all_stuck = False; ce_info = {"minuend":AREO_UNIO, "subtrahend":k, "res":avc_sub(AREO_UNIO,k), "exp":AREO_UNIO}; break
    record_test(property_name, Omega, all_stuck, "" if all_stuck else "Unio as minuend does not yield AREO_UNIO when subtracting DFI.", ce_info)

def test_full_circle_addition():
    property_name = "Full-Circle Addition (a + Unio = a, Unio + a = a)"
    all_identity = True
    ce_info = None
    for a in S_test:
        for unio_val in [ZERO_UNIO, AREO_UNIO]: # Test both aspects as the Unio operand
            if avc_add(a, unio_val) != a:
                all_identity = False; ce_info = {"op1":a, "op2":unio_val, "res":avc_add(a,unio_val), "exp":a}; break
            if avc_add(unio_val, a) != a:
                all_identity = False; ce_info = {"op1":unio_val, "op2":a, "res":avc_add(unio_val,a), "exp":a}; break
        if not all_identity: break
    record_test(property_name, Omega, all_identity, "" if all_identity else "Unio does not act as additive identity.", ce_info)

def test_omega_1_specifics():
    property_name = "Omega=1 Specifics (All ops on Unio yield Unio)"
    if Omega != 1:
        record_test(property_name, Omega, True, "N/A for this Omega.")
        return

    ops = {"add": avc_add, "sub": avc_sub, "mul": avc_mul, "div": avc_div}
    all_unio_result = True
    ce_info = None

    # For Omega=1, S_test contains [ZERO_UNIO, AREO_UNIO]
    # Note: ZERO_UNIO == AREO_UNIO is True due to __eq__
    # The aspects are distinct for mul/div inputs.
    
    for op_name, op_func in ops.items():
        for a_unio in [ZERO_UNIO, AREO_UNIO]:
            for b_unio in [ZERO_UNIO, AREO_UNIO]:
                res = op_func(a_unio, b_unio)
                if not isinstance(res, Unio): # Result must be some Unio aspect
                    all_unio_result = False
                    ce_info = {"op":op_name, "a":a_unio, "b":b_unio, "res":res, "exp_type":"Unio"}
                    break
            if not all_unio_result: break
        if not all_unio_result: break
    record_test(property_name, Omega, all_unio_result, "" if all_unio_result else "Operation did not yield Unio.", ce_info)


def test_omega_2_algebra():
    property_name = "Omega=2 Algebra (1+1=ZERO_UNIO, 1*1=1, Add Assoc, Mul Distrib)"
    if Omega != 2:
        record_test(property_name, Omega, True, "N/A for this Omega.")
        return

    val_1 = 1
    add_1_1_ok = (avc_add(val_1, val_1) == ZERO_UNIO)
    mul_1_1_ok = (avc_mul(val_1, val_1) == val_1)
    
    # Check Additive Associativity for Omega=2 (Expected to HOLD from Revised Core AVCA)
    add_assoc_omega2 = True
    ce_add_assoc_o2 = None
    for a in S_test:
        for b in S_test:
            for c in S_test:
                lhs = avc_add(avc_add(a,b),c)
                rhs = avc_add(a,avc_add(b,c))
                if lhs != rhs:
                    add_assoc_omega2 = False
                    ce_add_assoc_o2 = {"a":a, "b":b, "c":c, "lhs":lhs, "rhs":rhs}
                    break
            if not add_assoc_omega2: break
        if not add_assoc_omega2: break

    # Check Distributivity for Omega=2 (Expected to HOLD from Revised Core AVCA)
    distrib_omega2_ok = True
    ce_distrib_o2 = None
    for a in S_test:
        for b in S_test:
            for c in S_test:
                lhs = avc_mul(a, avc_add(b,c)) 
                rhs = avc_add(avc_mul(a,b), avc_mul(a,c)) 
                if lhs != rhs:
                    distrib_omega2_ok = False
                    ce_distrib_o2 = {"a":a, "b":b, "c":c, "lhs":lhs, "rhs":rhs}
                    break
            if not distrib_omega2_ok: break
        if not distrib_omega2_ok: break

    success = add_1_1_ok and mul_1_1_ok and add_assoc_omega2 and distrib_omega2_ok
    messages = []
    counterexamples = {}
    if not add_1_1_ok: messages.append(f"1+1 != ZERO_UNIO (got {avc_add(val_1,val_1)!r})")
    if not mul_1_1_ok: messages.append(f"1*1 != 1 (got {avc_mul(val_1,val_1)!r})")
    if not add_assoc_omega2: messages.append(f"Additive associativity FAILED for Omega=2."); counterexamples["add_assoc_o2"] = ce_add_assoc_o2
    if not distrib_omega2_ok: messages.append(f"Distributivity FAILED for Omega=2."); counterexamples["distrib_o2"] = ce_distrib_o2
    
    final_message = "; ".join(messages) if messages else "All Omega=2 specific properties verified."
    record_test(property_name, Omega, success, final_message, counterexamples if counterexamples else None)


# --- Main Test Execution ---
if __name__ == "__main__":
    # Omegas to test, covering phase transitions from Revised Core AVCA
    omegas_to_test = [1, 2, 3, 5, 7] 

    for current_omega_val in omegas_to_test:
        print(f"\n\n{'='*25} TESTING FOR OMEGA = {current_omega_val} {'='*25}")
        Omega = current_omega_val 
        generate_s_test()
        initialize_omega_results(Omega)

        s_test_repr = [repr(x) for x in S_test] # Corrected list comprehension
        print(f"Carrier set S_test for Omega={Omega}: {s_test_repr}\n")

        test_totality()
        test_commutativity(avc_add, "Addition")
        test_commutativity(avc_mul, "Multiplication")
        
        # Test associativity based on Revised Core AVCA "Phase-Transition Laws" table
        add_should_be_associative = (Omega <= 2)
        test_associativity(avc_add, "Addition", add_should_be_associative)
        test_associativity(avc_mul, "Multiplication", True) # Multiplication is always associative

        # Test distributivity based on Revised Core AVCA "Phase-Transition Laws" table
        mul_should_distribute_over_add = (Omega <= 2)
        test_distributivity_mul_over_add(mul_should_distribute_over_add)
        
        test_subtraction_asymmetry()
        test_dfi_haven()
        test_stuck_at_areo()
        test_full_circle_addition()
        
        if current_omega_val == 1:
            test_omega_1_specifics()
        if current_omega_val == 2:
            test_omega_2_algebra() 
        
        print(f"\nSummary for Omega={current_omega_val}: Passed={test_results_summary[current_omega_val]['passed']}, Failed={test_results_summary[current_omega_val]['failed']}")
        print(f"{'='*60}")

    print("\n\n{'='*30} OVERALL TEST SUITE SUMMARY {'='*30}")
    total_passed_all_omegas = 0
    total_failed_all_omegas = 0
    for omega_val_summary, results in test_results_summary.items(): # Use omega_val_summary to avoid conflict
        total_passed_all_omegas += results['passed']
        total_failed_all_omegas += results['failed']
        print(f"Omega={omega_val_summary}: Passed={results['passed']}, Failed={results['failed']}")
    
    if test_failures_details:
        print("\n--- DETAILED FAILURES ---")
        for failure in test_failures_details:
            print(f"  Omega={failure['omega']}: FAILED Property '{failure['property']}'")
            print(f"    Message: {failure['message']}")
            if failure['counterexample']:
                 # Make counterexample print nicely
                if isinstance(failure['counterexample'], dict):
                    ce_parts = []
                    for k, v_ce in failure['counterexample'].items():
                        ce_parts.append(f"{k}={v_ce!r}")
                    print(f"    Counterexample: {{{', '.join(ce_parts)}}}")
                else:
                    print(f"    Counterexample: {failure['counterexample']!r}")

    print(f"\nTotal tests passed across all Omega values: {total_passed_all_omegas}")
    print(f"Total tests failed across all Omega values: {total_failed_all_omegas}")
    print(f"{'='*70}")

    if total_failed_all_omegas == 0:
        print("\n🎉🎉🎉 ALL REVISED CORE AVCA STRESS TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    else:
        print("\nSYSTEM ALERT: ⚠️⚠️⚠️ SOME REVISED CORE AVCA STRESS TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")