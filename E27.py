import random

def random_continuum_strong_test(n, trials=10000):
    patterns = list(range(n))
    for t in range(trials):
        # 1) Random SubPattern: pick for each p a sub ≠ p
        sub_map = [random.choice([q for q in patterns if q!=p]) for p in patterns]
        # 2) Random K: a random permutation of 1..n to ensure a full continuum
        K = list(range(1, n+1))
        random.shuffle(K)
        # Check Kolmogorov bound: K[p] <= K[sub_map[p]]+1
        if any(K[p] > K[sub_map[p]] + 1 for p in patterns):
            continue
        # 3) Strong Wall: ensure no non-identity perm lowers complexity everywhere
        for _ in range(100):  # sample 100 random bijections
            perm = K[:]       # start with identity mapping of complexity
            random.shuffle(perm)
            if all(perm[p] <= K[p] for p in patterns) and perm != K:
                break
        else:
            # Found a strong-wall candidate
            return True, sub_map, K
    return False, None, None

ok, sub_map, K = random_continuum_strong_test(10)
print("Stress Sampling (n=10) passed:", ok)
if ok:
    print("Example sub:", sub_map)
    print("Example K  :", K)
