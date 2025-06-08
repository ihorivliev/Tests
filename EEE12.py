# Stage 6: Unified No‑Mercy Audit for N=4 Semilattices with Proper Filter & Join‑Homomorphism
# ------------------------------------------------------------------------------------------
# Domain: {0,1,2,3}
# Signature:
#   • meet(x,y) : commutative, idempotent, associative, unique neutral e_meet
#   • join(x,y) : commutative, idempotent, associative, unique neutral e_join
#   • P(x)      : unary predicate
#
# Axioms:
#   1. meet/join form a distributive semilattice pair:
#      meet(x, join(y,z)) = join(meet(x,y), meet(x,z))
#      join(x, meet(y,z)) = meet(join(x,y), join(x,z))
#   2. Proper filter at e_meet: P(e_meet)=True, P(x)=False for x≠e_meet
#   3. Prime-filter: P(x)&P(y) ↔ P(meet(x,y))
#   4. Homomorphism: P(x)&P(y) → P(join(x,y))
#
# Zero-dependency brute-force enumeration. Feasible in a few minutes.

from itertools import product

# 1. Domain setup
nodes = [0, 1, 2, 3]
keys = [(i, j) for i in nodes for j in nodes if i < j]
all_triples = list(product(nodes, repeat=3))

# 2. Enumerate meet candidates
meet_models = []
for vals in product(nodes, repeat=len(keys)):
    meet = {}
    # idempotence on diagonal
    for i in nodes:
        meet[(i, i)] = i
    # fill symmetric off-diagonal
    for (k, (i, j)) in enumerate(keys):
        v = vals[k]
        meet[(i, j)] = v
        meet[(j, i)] = v
    # associativity
    if not all(meet[(a, meet[(b, c)])] == meet[(meet[(a, b)], c)] for a, b, c in all_triples):
        continue
    # unique neutral
    neutrals = [e for e in nodes if all(meet[(e, x)] == x and meet[(x, e)] == x for x in nodes)]
    if len(neutrals) != 1:
        continue
    meet_models.append((meet, neutrals[0]))

# 3. Enumerate join candidates
join_models = []
for vals in product(nodes, repeat=len(keys)):
    join = {}
    for i in nodes:
        join[(i, i)] = i
    for (k, (i, j)) in enumerate(keys):
        v = vals[k]
        join[(i, j)] = v
        join[(j, i)] = v
    if not all(join[(a, join[(b, c)])] == join[(join[(a, b)], c)] for a, b, c in all_triples):
        continue
    neutrals = [e for e in nodes if all(join[(e, x)] == x and join[(x, e)] == x for x in nodes)]
    if len(neutrals) != 1:
        continue
    join_models.append((join, neutrals[0]))

# 4. Filter semilattice pairs by distributivity
semilattices = []
for meet, e_meet in meet_models:
    for join, e_join in join_models:
        # meet distributes over join
        if not all(meet[(x, join[(y, z)])] == join[(meet[(x, y)], meet[(x, z)])] for x, y, z in all_triples):
            continue
        # join distributes over meet
        if not all(join[(x, meet[(y, z)])] == meet[(join[(x, y)], join[(x, z)])] for x, y, z in all_triples):
            continue
        semilattices.append((meet, e_meet, join, e_join))

# 5. Enforce proper filter and homomorphism
final_models = []
for meet, e_meet, join, e_join in semilattices:
    for bits in product([False, True], repeat=len(nodes)):
        P = dict(zip(nodes, bits))
        # proper filter: only e_meet in P
        if not P[e_meet]: 
            continue
        if any(P[x] for x in nodes if x != e_meet):
            continue
        # prime-filter
        if not all((P[x] and P[y]) == P[meet[(x, y)]] for x, y in product(nodes, repeat=2)):
            continue
        # homomorphism
        if not all(not (P[x] and P[y]) or P[join[(x, y)]] for x, y in product(nodes, repeat=2)):
            continue
        final_models.append((meet, e_meet, join, e_join, P))

# 6. Report results
print("Total semilattice models passing distributivity:", len(semilattices))
print("Total models after proper filter & homomorphism:", len(final_models))
if final_models:
    meet, e_meet, join, e_join, P = final_models[0]
    print("\nExample Model:")
    print(" meet-neutral =", e_meet, " join-neutral =", e_join)
    print(" P =", P)
    print(" meet table:")
    for i in nodes:
        print("  ", [meet[(i, j)] for j in nodes])
    print(" join table:")
    for i in nodes:
        print("  ", [join[(i, j)] for j in nodes])
