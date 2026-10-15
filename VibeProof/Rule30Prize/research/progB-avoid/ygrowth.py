import sys
w = sys.argv[1]; b = int(sys.argv[2]); fph = int(sys.argv[3]); Lmax = int(sys.argv[4])
P = len(w)
B = set()
for line in open(f'bad_{w}_{b}.txt'):
    ph, s, c = map(int, line.split()); B.add((ph, s))
def succ2(ph, s):
    c = int(w[ph]); bit = lambda p: c if p == 0 else (s >> (p - 1)) & 1
    base = 0
    for p in range(1, b): base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
    nph = (ph + 1) % P
    if bit(b): return [(nph, base | ((1 ^ bit(b - 1)) << (b - 1)))]
    return [(nph, base | (bit(b - 1) << (b - 1))), (nph, base | ((1 ^ bit(b - 1)) << (b - 1)))]
S = {v: [u for u in succ2(*v) if u in B] for v in B}
# P-step successor map from free-phase nodes to free-phase nodes
fp = [v for v in B if v[0] == fph]
idx = {v: i for i, v in enumerate(fp)}
nxt = {}
for v in fp:
    cur = {v}
    for _ in range(P):
        cur = set(u for x in cur for u in S[x])
    nxt[idx[v]] = frozenset(idx[u] for u in cur)
lab = [fp[i][1] & 1 for i in range(len(fp))]
words = {}
for y in (0, 1):
    sel = frozenset(i for i in range(len(fp)) if lab[i] == y)
    if sel: words[(y,)] = sel
counts = [len(words)]
for L in range(2, Lmax + 1):
    nw = {}
    for wd, nodes in words.items():
        succ = set()
        for i in nodes: succ |= nxt[i]
        for y in (0, 1):
            sel = frozenset(i for i in succ if lab[i] == y)
            if sel: nw[wd + (y,)] = sel
    words = nw
    counts.append(len(words))
rat = [counts[i] / counts[i - 1] for i in range(len(counts) - 4, len(counts))]
print(f"w={w} b={b}: counts up to L={Lmax}: {counts[-6:]}; last ratios {[round(r,3) for r in rat]}")
