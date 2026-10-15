import sys
from collections import defaultdict
w = sys.argv[1]; b = int(sys.argv[2]); fph = int(sys.argv[3]); L = int(sys.argv[4]); K = int(sys.argv[5])
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
fp = [v for v in B if v[0] == fph]; idx = {v: i for i, v in enumerate(fp)}
nxt = {}
for v in fp:
    cur = {v}
    for _ in range(P): cur = set(u for x in cur for u in S[x])
    nxt[idx[v]] = frozenset(idx[u] for u in cur)
lab = [fp[i][1] & 1 for i in range(len(fp))]
words = {}
for y in (0, 1):
    sel = frozenset(i for i in range(len(fp)) if lab[i] == y)
    if sel: words[str(y)] = sel
for _ in range(L - 1):
    nw = {}
    for wd, nodes in words.items():
        succ = set()
        for i in nodes: succ |= nxt[i]
        for y in (0, 1):
            sel = frozenset(i for i in succ if lab[i] == y)
            if sel: nw[wd + str(y)] = sel
    words = nw
# gap words: sequences of complete gaps (between consecutive 1s) occurring inside allowed words
allowed = defaultdict(set)
for x in words:
    ones = [i for i, ch in enumerate(x) if ch == '1']
    gaps = [c - a - 1 for a, c in zip(ones, ones[1:])]
    for k in range(1, K + 1):
        for i in range(len(gaps) - k + 1):
            allowed[k].add(tuple(gaps[i:i + k]))
alph = sorted(set(g for (g,) in allowed[1]))
print(f"w={w} b={b}: gap alphabet {alph}")
for k in range(1, K + 1):
    import itertools
    mf = []
    for t in itertools.product(alph, repeat=k):
        if t in allowed[k]: continue
        if k == 1 or (t[1:] in allowed[k - 1] and t[:-1] in allowed[k - 1]): mf.append(''.join(map(str, t)))
    print(f"  k={k}: allowed {len(allowed[k])} of {len(alph)**k}; minimal forbidden gap-words: {mf[:40]}")
