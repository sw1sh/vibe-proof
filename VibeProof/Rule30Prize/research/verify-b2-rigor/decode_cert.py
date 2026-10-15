rankP = 1636695304138607345681430566450342879541164928147624093384226552632404513874232764790848370478092089357155105678346690372348660919069330654870135373832
perP = 79538861190790864407636279553
b, P = 3, 4
w = [0, 0, 1, 1]
def enc(s):
    return sum(x << i for i, x in enumerate(s))
def rk(ph, s):
    return (rankP >> (16 * (ph * 2**b + enc(s)))) % 65536
import itertools, collections
ranks = collections.Counter()
badnodes = []
for ph in range(P):
    for s in itertools.product([0, 1], repeat=b):
        r = rk(ph, list(s))
        ranks[r] += 1
        if r == 0:
            badnodes.append((ph, s))
print("rank histogram:", sorted(ranks.items()))
print("distinct ranks:", len(ranks), "max rank", max(ranks))
print("bad class (rank 0) size:", len(badnodes))
for n in badnodes: print("  ", n)
print("periods m(r):", [(perP >> (8 * r)) % 256 for r in range(13)])
# Check skeleton predicate on bad class directly
ok = all((s[0] == 1) if ph in (1, 2) else ((s[0] == 0) if ph == 3 else True) for ph, s in badnodes)
print("skeleton predicate holds on all bad nodes:", ok)
# Recompute edge relation and check monotonicity + nonbad edges
def lin3(l):
    return [l[i] ^ (l[i+1] | l[i+2]) for i in range(len(l) - 2)]
viol = 0
for ph in range(P):
    for s in itertools.product([0, 1], repeat=b):
        for x in (0, 1):
            s2 = lin3([w[ph]] + list(s) + [x])
            r, r2 = rk(ph, list(s)), rk((ph + 1) % P, s2)
            if r2 > r: viol += 1
            # non-bad rank preserving edges: since posP=wordP=0, positions all 0 and u = 0; m(r) must be such that ...
print("rank-increasing edges:", viol)
