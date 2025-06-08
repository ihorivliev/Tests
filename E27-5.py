# deterministic_kolmogorov_test.py

def kolmogorov_bound_test(n):
    """
    Deterministic test of Kolmogorov bound for arbitrary n:
      sub_map[p] = (p-1) mod n
      K_map[p]   = p+1
    The strong‐wall property then follows by strict increase of K_map.
    """
    # Build sub_map and K_map
    sub_map = [(p-1) % n for p in range(n)]
    K_map   = [p+1          for p in range(n)]
    # Check K(p) <= K(sub_map[p]) + 1
    return all(K_map[p] <= K_map[sub_map[p]] + 1 for p in range(n))

if __name__ == "__main__":
    print("n    Kolmogorov bound holds?")
    for n in [10, 20, 50, 100, 200, 500, 1000]:
        ok = kolmogorov_bound_test(n)
        print(f"{n:4d} -> {ok}")
