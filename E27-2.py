# E27_fixed_monte_carlo.py

import random

def random_continuum_strong_test(n, trials=10000, bijection_samples=1000):
    """
    Monte Carlo test:
    - Random subpattern mapping: for each pattern p, choose sub != p.
    - Random K: a random permutation of 1..n ensures full continuum.
    - Check Kolmogorov bound: K[p] <= K[sub[p]] + 1 for all p.
    - For strong wall: sample random bijections (permutations of indices) 
      and ensure no non-identity bijection satisfies K[f(p)] <= K[p] ∀p.
    """
    patterns = list(range(n))
    # Pre-generate identity for comparison
    identity = list(range(n))

    for t in range(trials):
        # 1) Subpattern map: each p -> sub_map[p] != p
        sub_map = [random.choice([q for q in patterns if q != p]) for p in patterns]
        # 2) Random K: true continuum spanning 1..n
        K = list(range(1, n+1))
        random.shuffle(K)
        # Kolmogorov bound
        if any(K[p] > K[sub_map[p]] + 1 for p in patterns):
            continue
        # 3) Strong wall test: no non-identity bijection preserves/increases complexity
        violated = False
        for _ in range(bijection_samples):
            f = patterns[:]
            random.shuffle(f)
            if f == identity:
                continue
            # Test if K[f[p]] <= K[p] for all p
            if all(K[f[p]] <= K[p] for p in patterns):
                violated = True
                break
        if not violated:
            # Found a strong-wall candidate
            return True, sub_map, K
    return False, None, None

if __name__ == '__main__':
    for n in [10, 20, 50]:
        ok, sub_map, K = random_continuum_strong_test(n, trials=5000, bijection_samples=500)
        print(f"n={n:2d} => Strong-wall passed:", ok)
        if ok:
            print(" Example subpattern map:", sub_map)
            print(" Example complexity  K():", K)
        print()
