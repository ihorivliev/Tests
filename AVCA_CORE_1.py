import itertools
from typing import Union, List, Any, Tuple, Callable

# --- Core AVCA Specification (from your definition) ---
# Global Omega, needs to be set by the test runner for each iteration
Omega: int = 0 # Default, will be overwritten

class Unio:
    __slots__ = ("aspect",)
    def __init__(self, aspect: str):
        # "zero" or "areo"
        assert aspect in ("zero","areo")
        self.aspect = aspect
    def __eq__(self, other):
        # All Unio objects are identified algebraically
        return isinstance(other, Unio)
    def __hash__(self):
        # Make Unio objects hashable for use in sets/dictionary keys if needed,
        # but remember they are all algebraically equivalent.
        # For distinctness based on aspect, check self.aspect.
        return hash(Unio) # All Unio hash to the same value
    def __repr__(self):
        return f"Unio({self.aspect!r})"

ZERO_UNIO = Unio("zero")  # additive-identity aspect
AREO_UNIO = Unio("areo")  # overflow / underflow aspect

AVCVal = Union[int, Unio]

def _check_val(x: AVCVal):
    """Allow only Unio or ints 1…Omega-1."""
    global Omega
    if Omega == 0:
        raise ValueError("Omega must be set before _check_val can be used.")
    if isinstance(x, Unio):
        return
    if not isinstance(x, int):
        raise TypeError(f"Bad AVCVal: {x!r} (type: {type(x)})")
    if Omega == 1 and isinstance(x, int): # No DFI if Omega is 1
         raise ValueError(f"DFI ints not allowed when Omega=1, got {x}")
    if Omega > 1 and not (1 <= x < Omega):
        raise ValueError(f"DFI ints must satisfy 1<=x<Omega (Omega={Omega}), got {x}")

# --- Four total operations (from your Core AVCA spec) ---

def avc_add(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega
    _check_val(a); _check_val(b)
    if isinstance(a, Unio): return b
    if isinstance(b, Unio): return a
    # Both a, b are DFI ints
    s = a + b
    return s if s < Omega else ZERO_UNIO

def avc_sub(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega
    _check_val(a); _check_val(b)
    if isinstance(b, Unio): return a
    if isinstance(a, Unio): return AREO_UNIO # If b is DFI
    # Both a, b are DFI ints
    return (a - b) if a > b else AREO_UNIO

def avc_mul(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega
    _check_val(a); _check_val(b)
    if isinstance(a, Unio):
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    if isinstance(b, Unio): # a must be DFI here
        return ZERO_UNIO if b.aspect=="zero" else AREO_UNIO
    # Both a, b are DFI ints
    p = a * b
    return p if p < Omega else AREO_UNIO

def avc_div(a: AVCVal, b: AVCVal) -> AVCVal:
    global Omega
    _check_val(a); _check_val(b)
    if isinstance(a, Unio):
        return ZERO_UNIO if a.aspect=="zero" else AREO_UNIO
    if isinstance(b, Unio): # a must be DFI here
        return AREO_UNIO
    # Both a, b are DFI ints
    if b == 0: # Should be caught by _check_val for DFI as DFI is >=1
        # This case handles if _check_val was bypassed or Omega allows DFI b=0
        # However, DFI is {1,...,Omega-1}, so b cannot be 0 if it's a DFI int.
        # This explicit check is for robustness against misuse if _check_val changes.
        return AREO_UNIO # Division by DFI zero, per spec "otherwise"
        
    q, r = divmod(a, b)
    return q if (r==0 and 1<=q<Omega) else AREO_UNIO

# --- Testing Harness ---
S_test: List[AVCVal] = []

def generate_s_test():
    global S_test, Omega
    if Omega == 0:
        raise ValueError("Omega must be set before S_test can be generated.")
    S_test = [ZERO_UNIO, AREO_UNIO]
    if Omega > 1:
        S_test.extend(list(range(1, Omega)))
    # If Omega is 1, S_test will be [ZERO_UNIO, AREO_UNIO].
    # Note: Per Unio.__eq__, ZERO_UNIO == AREO_UNIO.
    # For exhaustive tests, it's good to have both distinct aspect objects.

test_results = {
    "passed": 0,
    "failed": 0,
    "details": []
}

def reset_test_results():
    global test_results
    test_results = {"passed": 0, "failed": 0, "details": []}

def record_test_result(property_name: str, omega_val: int, success: bool, message: str = "", counterexample: Any = None):
    global test_results
    status_emoji = "✅" if success else "❌"
    test_results["details"].append({
        "property": property_name,
        "omega": omega_val,
        "status": "PASSED" if success else "FAILED",
        "message": message,
        "counterexample": counterexample
    })
    if success:
        test_results["passed"] += 1
        print(f"{status_emoji} Omega={omega_val}: Property '{property_name}' PASSED. {message}")
    else:
        test_results["failed"] += 1
        print(f"{status_emoji} Omega={omega_val}: Property '{property_name}' FAILED. {message}")
        if counterexample:
            print(f"    Counterexample: {counterexample}")

def is_dfi(val: AVCVal) -> bool:
    global Omega
    return isinstance(val, int) and 1 <= val < Omega

# --- Test Functions for Core AVCA Properties ---

def test_totality():
    global S_test, Omega
    property_name = "Operation Totality"
    ops = {
        "add": avc_add,
        "sub": avc_sub,
        "mul": avc_mul,
        "div": avc_div
    }
    all_total = True
    counterexample_info = None

    for op_name, op_func in ops.items():
        for a in S_test:
            for b in S_test:
                try:
                    res = op_func(a, b)
                    # Check if result is in the extended carrier set (includes both Unio aspects)
                    # or is a valid DFI int if Omega > 1
                    if not (isinstance(res, Unio) or (Omega > 1 and isinstance(res, int) and 1 <= res < Omega) or (Omega == 1 and isinstance(res, Unio))):
                        all_total = False
                        counterexample_info = f"Op: {op_name}, Inputs: ({a!r}, {b!r}), Result: {res!r} (Not in S_test for Omega={Omega})"
                        break
                except Exception as e:
                    all_total = False
                    counterexample_info = f"Op: {op_name}, Inputs: ({a!r}, {b!r}), Exception: {e}"
                    break
            if not all_total: break
        if not all_total: break
    
    record_test_result(property_name, Omega, all_total, "" if all_total else "Operation resulted in value outside S_test or raised unexpected error.", counterexample_info)

def test_commutativity_add():
    global S_test, Omega
    property_name = "Commutativity of Addition (a+b == b+a)"
    all_commutative = True
    counterexample_info = None
    for a in S_test:
        for b in S_test:
            res1 = avc_add(a,b)
            res2 = avc_add(b,a)
            if res1 != res2: # Uses Unio.__eq__
                all_commutative = False
                counterexample_info = f"a={a!r}, b={b!r}, a+b={res1!r}, b+a={res2!r}"
                break
        if not all_commutative: break
    record_test_result(property_name, Omega, all_commutative, "" if all_commutative else "Addition not commutative.", counterexample_info)

def test_commutativity_mul():
    global S_test, Omega
    property_name = "Commutativity of Multiplication (a*b == b*a)"
    all_commutative = True
    counterexample_info = None
    for a in S_test:
        for b in S_test:
            res1 = avc_mul(a,b)
            res2 = avc_mul(b,a)
            if res1 != res2:
                all_commutative = False
                counterexample_info = f"a={a!r}, b={b!r}, a*b={res1!r}, b*a={res2!r}"
                break
        if not all_commutative: break
    record_test_result(property_name, Omega, all_commutative, "" if all_commutative else "Multiplication not commutative.", counterexample_info)

def test_associativity_mul():
    global S_test, Omega
    property_name = "Associativity of Multiplication ((a*b)*c == a*(b*c))"
    all_associative = True
    counterexample_info = None
    for a in S_test:
        for b in S_test:
            for c in S_test:
                res1 = avc_mul(avc_mul(a,b),c)
                res2 = avc_mul(a,avc_mul(b,c))
                if res1 != res2:
                    all_associative = False
                    counterexample_info = f"a={a!r}, b={b!r}, c={c!r}, (a*b)*c={res1!r}, a*(b*c)={res2!r}"
                    break
            if not all_associative: break
        if not all_associative: break
    record_test_result(property_name, Omega, all_associative, "" if all_associative else "Multiplication not associative.", counterexample_info)

def test_non_associativity_add():
    global S_test, Omega
    property_name = "Non-associativity of Addition ((a+b)+c != a+(b+c))"
    found_non_associative_case = False
    counterexample_info = None
    
    if Omega < 2: # Associativity holds trivially or by definition for Omega=1
        record_test_result(property_name, Omega, True, "Holds (vacuously or by structure for Omega < 2). Expect non-associativity for Omega >= 2.", None)
        return

    for a in S_test:
        for b in S_test:
            for c in S_test:
                res1 = avc_add(avc_add(a,b),c)
                res2 = avc_add(a,avc_add(b,c))
                if res1 != res2:
                    found_non_associative_case = True
                    counterexample_info = f"a={a!r}, b={b!r}, c={c!r}, (a+b)+c={res1!r}, a+(b+c)={res2!r}"
                    break
            if found_non_associative_case: break
        if found_non_associative_case: break
    
    # For Omega >= 2, we EXPECT non-associativity. So, success is finding a counterexample.
    record_test_result(property_name, Omega, found_non_associative_case, 
                       "Non-associativity confirmed as expected for Omega >= 2." if found_non_associative_case else "Failed to find non-associative case (unexpected for Omega >=2).", 
                       counterexample_info if found_non_associative_case else "No counterexample found.")

def test_distributivity_mul_over_add():
    global S_test, Omega
    property_name = "Distributivity of Mul over Add (a*(b+c) == (a*b)+(a*c))"
    is_distributive_universally = True
    counterexample_info = None

    for a in S_test:
        for b in S_test:
            for c in S_test:
                lhs = avc_mul(a, avc_add(b,c))
                rhs = avc_add(avc_mul(a,b), avc_mul(a,c))
                if lhs != rhs:
                    is_distributive_universally = False
                    counterexample_info = f"a={a!r}, b={b!r}, c={c!r}, a*(b+c)={lhs!r}, (a*b)+(a*c)={rhs!r}"
                    break
            if not is_distributive_universally: break
        if not is_distributive_universally: break

    if Omega == 2:
        record_test_result(property_name, Omega, is_distributive_universally, 
                           "Distributivity holds as expected for Omega=2." if is_distributive_universally else "Distributivity FAILED (unexpected for Omega=2).",
                           counterexample_info)
    elif Omega >= 3:
        # We expect it to FAIL for Omega >= 3. Success is if is_distributive_universally is FALSE.
        record_test_result(property_name, Omega, not is_distributive_universally,
                           "Non-distributivity confirmed as expected for Omega>=3." if not is_distributive_universally else "Distributivity HELD (unexpected for Omega>=3).",
                           counterexample_info if not is_distributive_universally else "No counterexample found.")
    else: # Omega == 1
         record_test_result(property_name, Omega, is_distributive_universally, "Holds (trivially for Omega=1)." , counterexample_info)


def test_subtraction_asymmetry():
    global S_test, Omega
    property_name = "Subtraction Asymmetry (Unio-x == AREO_UNIO, x-Unio == x)"
    holds_unio_minus_x = True
    holds_x_minus_unio = True
    counterexample_info_umx = None
    counterexample_info_xmu = None

    for x in S_test:
        # Test Unio - x (any aspect of Unio minuend gives AREO_UNIO if x is DFI, or aspect-dependent if x is Unio)
        # Core AVCA: if isinstance(a,Unio): return AREO_UNIO (when b is DFI)
        res_zero_unio_minus_x = avc_sub(ZERO_UNIO, x)
        res_areo_unio_minus_x = avc_sub(AREO_UNIO, x)
        
        expected_unio_minus_x = AREO_UNIO # If x is DFI
        if isinstance(x, Unio): # Unio - Unio == Unio(a) (if b is Unio, returns a, which is Unio)
            expected_unio_minus_x = ZERO_UNIO # Subtraction rule: if isinstance(b, Unio): return a
                                              # So ZERO_UNIO - Unio() -> ZERO_UNIO
                                              # AREO_UNIO - Unio() -> AREO_UNIO

        if isinstance(x, Unio) and res_zero_unio_minus_x != ZERO_UNIO:
             holds_unio_minus_x = False
             counterexample_info_umx = f"ZERO_UNIO - {x!r} = {res_zero_unio_minus_x!r}, expected {ZERO_UNIO!r}"
        elif isinstance(x, Unio) and res_areo_unio_minus_x != AREO_UNIO:
             holds_unio_minus_x = False
             counterexample_info_umx = f"AREO_UNIO - {x!r} = {res_areo_unio_minus_x!r}, expected {AREO_UNIO!r}"
        elif is_dfi(x) and (res_zero_unio_minus_x != AREO_UNIO or res_areo_unio_minus_x != AREO_UNIO):
            holds_unio_minus_x = False
            counterexample_info_umx = f"ZERO_UNIO-{x!r}={res_zero_unio_minus_x!r} (exp {AREO_UNIO!r}), AREO_UNIO-{x!r}={res_areo_unio_minus_x!r} (exp {AREO_UNIO!r})"
        
        if not holds_unio_minus_x: break

        # Test x - Unio
        # Core AVCA: if isinstance(b,Unio): return a
        res_x_minus_zero_unio = avc_sub(x, ZERO_UNIO)
        res_x_minus_areo_unio = avc_sub(x, AREO_UNIO)
        if res_x_minus_zero_unio != x or res_x_minus_areo_unio != x: # x - Unio == x
            holds_x_minus_unio = False
            counterexample_info_xmu = f"{x!r}-ZERO_UNIO={res_x_minus_zero_unio!r}, {x!r}-AREO_UNIO={res_x_minus_areo_unio!r}, expected {x!r} for both"
            break
        if not holds_x_minus_unio: break
            
    success = holds_unio_minus_x and holds_x_minus_unio
    final_counterexample = counterexample_info_umx or counterexample_info_xmu
    record_test_result(property_name, Omega, success, "" if success else "Asymmetry rules not universally met.", final_counterexample)

def test_dfi_haven():
    global S_test, Omega
    property_name = "DFI-Haven (Ops behave like standard +,* if no wrap/overflow)"
    if Omega <= 1: # No DFI or DFI is empty
        record_test_result(property_name, Omega, True, "Holds (vacuously, no DFI).", None)
        return

    dfi_set = [val for val in S_test if is_dfi(val)]
    if not dfi_set: # Should not happen if Omega > 1
        record_test_result(property_name, Omega, True, "Holds (vacuously, DFI set empty despite Omega > 1 - check S_test generation).", None)
        return

    holds_haven = True
    counterexample_info = None

    # Test Addition
    for a in dfi_set:
        for b in dfi_set:
            std_sum = a + b
            avc_res_add = avc_add(a,b)
            if std_sum < Omega:
                if avc_res_add != std_sum:
                    holds_haven = False
                    counterexample_info = f"ADD: a={a}, b={b}. Expected DFI {std_sum}, got {avc_res_add!r}"
                    break
            else: # std_sum >= Omega (overflow)
                if avc_res_add != ZERO_UNIO:
                    holds_haven = False
                    counterexample_info = f"ADD OVFL: a={a}, b={b}. Expected {ZERO_UNIO!r}, got {avc_res_add!r}"
                    break
        if not holds_haven: break
    
    if holds_haven:
        # Test Multiplication
        for a in dfi_set:
            for b in dfi_set:
                std_prod = a * b
                avc_res_mul = avc_mul(a,b)
                if std_prod < Omega:
                    if avc_res_mul != std_prod:
                        holds_haven = False
                        counterexample_info = f"MUL: a={a}, b={b}. Expected DFI {std_prod}, got {avc_res_mul!r}"
                        break
                else: # std_prod >= Omega (overflow)
                    if avc_res_mul != AREO_UNIO: # Core AVCA mul overflows to AREO_UNIO
                        holds_haven = False
                        counterexample_info = f"MUL OVFL: a={a}, b={b}. Expected {AREO_UNIO!r}, got {avc_res_mul!r}"
                        break
            if not holds_haven: break

    record_test_result(property_name, Omega, holds_haven, "" if holds_haven else "DFI ops do not match standard ops or overflow rules.", counterexample_info)


def test_stuck_at_areo():
    global S_test, Omega
    property_name = "Stuck-at-Areo (AREO_UNIO - k == AREO_UNIO for DFI k)"
    # Per Core AVCA: if isinstance(a,Unio): return AREO_UNIO (when b is DFI)
    # So, ZERO_UNIO - DFI_k -> AREO_UNIO
    # And AREO_UNIO - DFI_k -> AREO_UNIO
    
    is_stuck = True
    counterexample_info = None

    dfi_k_values = [val for val in S_test if is_dfi(val)]

    if not dfi_k_values and Omega > 1: # If Omega=1, DFI is empty, test is vacuous for DFI k
        record_test_result(property_name, Omega, True, "Holds (vacuously, no DFI k to test).", None)
        return
    if Omega == 1:
        record_test_result(property_name, Omega, True, "Holds (vacuously, no DFI k for Omega=1).", None)
        return

    for k in dfi_k_values:
        res_zu = avc_sub(ZERO_UNIO, k)
        res_au = avc_sub(AREO_UNIO, k)
        if res_zu != AREO_UNIO or res_au != AREO_UNIO :
            is_stuck = False
            counterexample_info = f"k={k!r}. ZERO_UNIO-k = {res_zu!r} (exp {AREO_UNIO!r}), AREO_UNIO-k = {res_au!r} (exp {AREO_UNIO!r})"
            break
            
    record_test_result(property_name, Omega, is_stuck, "" if is_stuck else "Unio (Areo aspect) does not absorb DFI subtraction.", counterexample_info)


def test_full_circle_addition():
    global S_test, Omega
    property_name = "Full-Circle Addition (a+Unio == a, Unio+a == a)"
    # Core AVCA: if isinstance(a,Unio): return b; if isinstance(b,Unio): return a
    holds_full_circle = True
    counterexample_info = None

    for a in S_test:
        # Test a + ZERO_UNIO
        res_a_plus_zu = avc_add(a, ZERO_UNIO)
        if res_a_plus_zu != a:
            holds_full_circle = False
            counterexample_info = f"a={a!r}, a + ZERO_UNIO = {res_a_plus_zu!r}, expected {a!r}"
            break
        # Test a + AREO_UNIO
        res_a_plus_au = avc_add(a, AREO_UNIO)
        if res_a_plus_au != a:
            holds_full_circle = False
            counterexample_info = f"a={a!r}, a + AREO_UNIO = {res_a_plus_au!r}, expected {a!r}"
            break
        
        # Test ZERO_UNIO + a
        res_zu_plus_a = avc_add(ZERO_UNIO, a)
        if res_zu_plus_a != a:
            holds_full_circle = False
            counterexample_info = f"a={a!r}, ZERO_UNIO + a = {res_zu_plus_a!r}, expected {a!r}"
            break
        # Test AREO_UNIO + a
        res_au_plus_a = avc_add(AREO_UNIO, a)
        if res_au_plus_a != a:
            holds_full_circle = False
            counterexample_info = f"a={a!r}, AREO_UNIO + a = {res_au_plus_a!r}, expected {a!r}"
            break
    if not holds_full_circle: pass # already broken

    record_test_result(property_name, Omega, holds_full_circle, "" if holds_full_circle else "Unio does not act as additive identity.", counterexample_info)

def test_omega_2_special_case():
    global Omega
    property_name = "Omega=2 Special Case (1+1=ZERO_UNIO, 1*1=1)"
    if Omega != 2:
        record_test_result(property_name, Omega, True, "N/A for this Omega.", None)
        return

    val_1 = 1
    expected_add_res = ZERO_UNIO
    expected_mul_res = 1
    
    actual_add_res = avc_add(val_1, val_1)
    actual_mul_res = avc_mul(val_1, val_1)

    add_correct = (actual_add_res == expected_add_res)
    mul_correct = (actual_mul_res == expected_mul_res)
    success = add_correct and mul_correct
    
    msg = []
    if not add_correct: msg.append(f"1+1={actual_add_res!r} (exp {expected_add_res!r})")
    if not mul_correct: msg.append(f"1*1={actual_mul_res!r} (exp {expected_mul_res!r})")

    record_test_result(property_name, Omega, success, "" if success else "; ".join(msg), None if success else msg)

# --- Main Test Execution ---
if __name__ == "__main__":
    omegas_to_test = [1, 2, 3, 4, 5] # Test key phase transition points and a bit beyond

    overall_summary = {}

    for current_omega_val in omegas_to_test:
        print(f"\n\n{'='*20} TESTING FOR OMEGA = {current_omega_val} {'='*20}")
        Omega = current_omega_val # Set global Omega for this run
        generate_s_test()
        reset_test_results()

        s_test_repr = [repr(x) for x in S_test]
        print(f"Carrier set S_test for Omega={Omega}: {s_test_repr}\n")

        test_totality()
        test_commutativity_add()
        test_commutativity_mul()
        test_associativity_mul()
        test_non_associativity_add() # Expected to find non-assoc for Omega >= 2
        test_distributivity_mul_over_add() # Expected to hold for Omega=2, fail for Omega >= 3
        test_subtraction_asymmetry()
        test_dfi_haven()
        test_stuck_at_areo()
        test_full_circle_addition()
        
        if current_omega_val == 2:
            test_omega_2_special_case()
        
        overall_summary[current_omega_val] = test_results.copy()
        print(f"\nSummary for Omega={current_omega_val}: Passed={test_results['passed']}, Failed={test_results['failed']}")
        print(f"{'='*50}")

    print("\n\n{'='*25} OVERALL TEST SUITE SUMMARY {'='*25}")
    total_passed_all_omegas = 0
    total_failed_all_omegas = 0
    for omega_val, results in overall_summary.items():
        total_passed_all_omegas += results['passed']
        total_failed_all_omegas += results['failed']
        print(f"Omega={omega_val}: Passed={results['passed']}, Failed={results['failed']}")
        if results['failed'] > 0:
            for detail in results['details']:
                if detail['status'] == 'FAILED':
                    print(f"  - FAILED: {detail['property']} - {detail['message']}")
                    if detail['counterexample']:
                         print(f"    Counterexample: {detail['counterexample']}")
    print(f"\nTotal tests passed across all Omega values: {total_passed_all_omegas}")
    print(f"Total tests failed across all Omega values: {total_failed_all_omegas}")
    print(f"{'='*70}")

    if total_failed_all_omegas == 0:
        print("\n🎉🎉🎉 ALL CORE AVCA STRESS TESTS PASSED SUCCESSFULLY! 🎉🎉🎉")
    else:
        print("\n⚠️⚠️⚠️ SOME CORE AVCA STRESS TESTS FAILED. PLEASE REVIEW OUTPUT. ⚠️⚠️⚠️")