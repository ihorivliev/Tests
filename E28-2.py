# cost_enumeration_n4.py

import itertools

n = 4
patterns = list(range(n))
# Complexity K(p)=p+1
K = {p:p+1 for p in patterns}

valid = 0
for C_tuple in itertools.product(range(1,n+1), repeat=n):
    # Check C(p) >= K(p)
    if all(C_tuple[p] >= K[p] for p in patterns):
        valid += 1

print(f"✅ Cost assignments satisfying C(p) ≥ K(p): {valid} / {n**n}")
