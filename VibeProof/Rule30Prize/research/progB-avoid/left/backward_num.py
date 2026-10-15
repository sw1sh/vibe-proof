# numeric backward reconstruction for many random y; look for depth relations holding for all samples
import sys, random
pat = sys.argv[1]; Q = int(sys.argv[2]); NS = int(sys.argv[3]); start_phase = int(sys.argv[4]) if len(sys.argv) > 4 else 0
cpat = sys.argv[5] if len(sys.argv) > 5 else '0' * len(pat)
P = len(pat)
random.seed(5)
H = Q + 2
# bit-parallel over samples: each value is an int with NS bits (one per sample)
nblocks = (H + start_phase) // P + 2
ys = [random.getrandbits(NS) for _ in range(nblocks)]
FULL = (1 << NS) - 1
def col1(t):
    ph = (start_phase + t) % P; blk = (start_phase + t) // P
    ch = pat[ph]
    return {'0': 0, '1': FULL, 'y': ys[blk], 'n': FULL ^ ys[blk]}[ch]
prev = [FULL if cpat[(start_phase + t) % len(cpat)] == '1' else 0 for t in range(H)]
cur = [col1(t) for t in range(H)]
rows = [cur[0]]
for q in range(1, Q):
    nxt = [cur[t + 1] ^ (cur[t] | prev[t]) for t in range(H - q)]
    prev, cur = cur[:H - q], nxt
    rows.append(cur[0])
consts = [(q + 1, 'one' if r == FULL else 'zero') for q, r in enumerate(rows) if r == 0 or r == FULL]
print("constant depths:", consts[:60], '... total', len(consts), 'max depth', max([c[0] for c in consts]) if consts else None)
pairs = []
for a in range(Q):
    for b in range(a + 1, min(Q, a + 12)):
        x = rows[a] ^ rows[b]
        if x == 0 or x == FULL:
            pairs.append((a + 1, b + 1, 'eq' if x == 0 else 'neq'))
print("pair relations (depth a, depth b):", pairs[:80], '... total', len(pairs), 'max depth', max([p[1] for p in pairs]) if pairs else None)
# can rows be all-zero on [q1, q2] ? count samples with zeros on windows of length L at various positions
for L in (4, 8, 12, 16):
    best = 0
    for q1 in range(Q - L):
        z = FULL
        for q in range(q1, q1 + L): z &= FULL ^ rows[q]
        if z: best = max(best, q1 + 1)
    print("zero window of length %d occurs (some sample) up to start depth %d" % (L, best))
