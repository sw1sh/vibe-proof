# y-language of the bad SCC: the free output bit (column 1 at the free phase) along paths in B_b
import sys
from collections import defaultdict
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
def adv(nodes):
    cur = set(nodes)
    for _ in range(P):
        nxt = set()
        for v in cur: nxt.update(S[v])
        cur = nxt
    return frozenset(cur)
start = [v for v in B if v[0] == fph]
words = {(): frozenset(start)}
forb = []
for L in range(1, Lmax + 1):
    nw = {}
    for wd, nodes in words.items():
        base = adv(nodes) if wd else nodes
        for y in (0, 1):
            sel = frozenset(v for v in base if (v[1] & 1) == y)
            if sel: nw[wd + (y,)] = sel
            else:
                # minimal forbidden if all proper factors allowed (check suffix)
                forb.append(''.join(map(str, wd + (y,))))
    words = nw
    print(f"L={L}: {len(words)} realizable y-words (of {2**L})")
# minimal forbidden words: those whose proper factors are all realizable
allw = set(''.join(map(str, k)) for k in words)
print("forbidden (prefix-minimal) words, first few:", forb[:30])
