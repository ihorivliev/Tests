import itertools

# Finite domain {0,1} for Structure and Feeling values
domain = [0, 1]

# Check all possible assignments for s1, s2, f1, f2
solutions = []
for s1, s2, f1, f2 in itertools.product(domain, repeat=4):
    # Universal Principle: if s1 == s2 then f1 == f2
    if s1 == s2 and f1 != f2:
        continue
    # Assumption: s1 == s2
    if s1 != s2:
        continue
    # Claim: f1 != f2
    if f1 == f2:
        continue
    # If we reach here, all conditions are met
    solutions.append((s1, s2, f1, f2))

# Report results
if solutions:
    print("❌ Found satisfying assignments (unexpected):", solutions)
else:
    print("✅ No satisfying assignment found: the formulas are unsatisfiable, demonstrating the contradiction.")
