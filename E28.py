# non_deterministic_self_similarity.py

import itertools

# Universe of 3 patterns
patterns = [0,1,2]
pairs = [(p,q) for p in patterns for q in patterns if p!=q]

# Fixed complexity assignment K(p)=p+1
K = {p:p+1 for p in patterns}

valid = 0
for mask in range(1<<len(pairs)):
    # Build relation R from mask
    R = [pairs[i] for i in range(len(pairs)) if (mask>>i)&1]
    # 1) Existence: every p has at least one (p,q)
    if not all(any(src==p for src,_ in R) for p in patterns):
        continue
    # 2) Kolmogorov proxy: for each p there is (p,q) with K[p] <= K[q]+1
    ok = True
    for p in patterns:
        if not any(src==p and K[p] <= K[q]+1 for src,q in R):
            ok = False; break
    if not ok:
        continue
    valid += 1

print(f"✅ Relations satisfying non-deterministic self-similarity: {valid} / {1<<len(pairs)}")
