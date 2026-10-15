import itertools
rankP = 1636695304138607345681430566450342879541164928147624093384226552632404513874232764790848370478092089357155105678346690372348660919069330654870135373832
b, P, w = 3, 4, [0, 0, 1, 1]
enc = lambda s: sum(x << i for i, x in enumerate(s))
rk = lambda ph, s: (rankP >> (16 * (ph * 2**b + enc(s)))) % 65536
lin3 = lambda l: tuple(l[i] ^ (l[i+1] | l[i+2]) for i in range(len(l) - 2))
nodes = [(ph, s) for ph in range(P) for s in itertools.product([0, 1], repeat=b)]
succ = {n: set() for n in nodes}
for ph, s in nodes:
    for x in (0, 1):
        succ[(ph, s)].add(((ph + 1) % P, lin3([w[ph]] + list(s) + [x])))
def reach(src):
    seen, st = {src}, [src]
    while st:
        u = st.pop()
        for v in succ[u]:
            if v not in seen: seen.add(v); st.append(v)
    return seen
R = {n: reach(n) for n in nodes}
sccs = []
done = set()
for n in nodes:
    if n in done: continue
    comp = {m for m in R[n] if n in R[m]}
    done |= comp
    sccs.append(comp)
for comp in sccs:
    rks = {rk(*m) for m in comp}
    cyc = any(v in comp for u in comp for v in succ[u])
    print(len(comp), "nodes, ranks", rks, "cyclic" if cyc else "trivial", sorted(comp) if len(comp) <= 4 else "")
bad = {n for n in nodes if rk(*n) == 0}
print("rank-0 class is one SCC:", any(c == bad for c in sccs))
