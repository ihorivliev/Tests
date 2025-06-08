# Stage 6: Unified No‑Mercy Audit for Domain {0,1,2}
# A) Enforce Proper Filter
# B) Explore Homomorphic Extension with Join
# C) Scale Up to 3‑Element Semilattice
#
# We enumerate all "meet" and "join" operations
# that satisfy semilattice axioms (commutative, idempotent, associative,
# unique neutral). For each, we enforce distributivity both ways.
# Then we enumerate all P assignments that satisfy:
#   - Proper filter: only meet-neutral e_meet is in P
#   - Prime-filter: P(x)&P(y) ↔ P(meet(x,y))
#   - Homomorphism: P(x)&P(y) → P(join(x,y))
#
# Finally, we report the models found.

from itertools import product

# Domain and pair list
nodes = [0, 1, 2]
pairs = [(i, j) for i in nodes for j in nodes]

# Generate semilattice "meet" candidates
meet_cands = []
# Unordered pairs for assignment
keys = [(0,1), (0,2), (1,2)]
for vals in product(nodes, repeat=3):
    meet = {}
    # idempotence
    for i in nodes:
        meet[(i,i)] = i
    # commutativity
    for (k,(i,j)) in enumerate(keys):
        v = vals[k]
        meet[(i,j)] = v
        meet[(j,i)] = v
    # associativity check
    if not all(meet[(a, meet[(b,c)])] == meet[(meet[(a,b)], c)]
               for a,b,c in product(nodes, repeat=3)):
        continue
    # unique neutral
    neutrals = [e for e in nodes if all(meet[(e,x)]==x and meet[(x,e)]==x for x in nodes)]
    if len(neutrals) != 1:
        continue
    meet_cands.append((meet, neutrals[0]))

# Generate semilattice "join" candidates
join_cands = []
for vals in product(nodes, repeat=3):
    join = {}
    for i in nodes:
        join[(i,i)] = i
    for (k,(i,j)) in enumerate(keys):
        v = vals[k]
        join[(i,j)] = v
        join[(j,i)] = v
    if not all(join[(a, join[(b,c)])] == join[(join[(a,b)], c)]
               for a,b,c in product(nodes, repeat=3)):
        continue
    neutrals = [e for e in nodes if all(join[(e,x)]==x and join[(x,e)]==x for x in nodes)]
    if len(neutrals) != 1:
        continue
    join_cands.append((join, neutrals[0]))

# Combine meet/join and enforce distributivity both ways
models = []
for meet, e_meet in meet_cands:
    for join, e_join in join_cands:
        # distributivity checks
        if not all(meet[(x, join[(y,z)])] == join[(meet[(x,y)], meet[(x,z)])]
                   for x,y,z in product(nodes,repeat=3)):
            continue
        if not all(join[(x, meet[(y,z)])] == meet[(join[(x,y)], join[(x,z)])]
                   for x,y,z in product(nodes,repeat=3)):
            continue
        models.append((meet, e_meet, join, e_join))

# Enforce proper filter and homomorphic extension
final_models = []
for meet, e_meet, join, e_join in models:
    for bits in product([False, True], repeat=len(nodes)):
        P = dict(zip(nodes, bits))
        # A) Proper filter: P(e_meet)=True, others False
        if not P[e_meet]: continue
        if any(P[x] for x in nodes if x != e_meet): continue
        # Prime-filter: ∀x,y. P(x)&P(y) ↔ P(meet(x,y))
        if not all((P[x] and P[y]) == P[meet[(x,y)]] for x,y in product(nodes,repeat=2)):
            continue
        # B) Homomorphism: ∀x,y. P(x)&P(y) → P(join(x,y))
        if not all(not (P[x] and P[y]) or P[join[(x,y)]] for x,y in product(nodes,repeat=2)):
            continue
        final_models.append((meet, e_meet, join, e_join, P))

# Report
print(f"Total semilattice models passing distributivity: {len(models)}")
print(f"Total models after proper filter & homomorphism: {len(final_models)}\n")
for idx,(meet,e_meet,join,e_join,P) in enumerate(final_models):
    print(f"Model #{idx+1}:")
    print(f"  meet-neutral = {e_meet}, join-neutral = {e_join}")
    print(f"  P = {P}")
    print("  meet table:")
    for i in nodes:
        print("   ", [meet[(i,j)] for j in nodes])
    print("  join table:")
    for i in nodes:
        print("   ", [join[(i,j)] for j in nodes])
    break
