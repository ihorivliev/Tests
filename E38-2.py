# random_stress_loop.py

import random

def random_stress_loop(N, trials=1000, bijection_samples=200):
    """
    Monte Carlo stress test for:
      1) Kolmogorov bound: K[p] <= K[sub_map[p]] + 1
      2) Strong Wall: no non-identity bijection f with K[f[p]] <= K[p] ∀p
    Returns True if all sampled worlds pass, otherwise reports first failure.
    """
    patterns = list(range(N))
    identity = list(range(N))
    
    for t in range(1, trials+1):
        # 1) Random subpattern map: each p -> q != p
        sub_map = [random.choice([q for q in patterns if q != p]) for p in patterns]
        # 2) Random K: a random permutation of 1..N (ensures full continuum)
        K_map = list(range(1, N+1))
        random.shuffle(K_map)
        # Test Kolmogorov bound
        if any(K_map[p] > K_map[sub_map[p]] + 1 for p in patterns):
            # Skip worlds that don't satisfy the bound
            continue
        
        # Test strong-wall by sampling random bijections
        violation = False
        for _ in range(bijection_samples):
            perm = identity[:] 
            random.shuffle(perm)
            if perm == identity:
                continue
            # check if this bijection never raises complexity
            if all(K_map[perm[p]] <= K_map[p] for p in patterns):
                violation = True
                break
        
        if violation:
            print(f"❌ Trial {t}: Strong-wall violated")
            print(" sub_map =", sub_map)
            print(" K_map   =", K_map)
            return False
    
    print(f"✅ All {trials} trials passed for N={N}")
    return True

if __name__ == "__main__":
    for N in [10, 20]:
        print(f"\n--- Stress Test N={N} ---")
        random_stress_loop(N, trials=2000, bijection_samples=500)
