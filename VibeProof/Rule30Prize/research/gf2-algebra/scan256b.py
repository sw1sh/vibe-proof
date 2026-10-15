# For each ECA rule: ANF degree of the t-step center map Phi_t (t = 6, 7) via big-int truth tables,
# and eventual periodicity of the single-seed center column (2000 steps, zero background).
import sys
def anf_degree(rule, t):
    n = 2 * t + 1; M = 1 << n; FULL = (1 << M) - 1
    # projection truth tables
    proj = []
    for v in range(n):
        # bit x set iff (x >> v) & 1 ; pattern: blocks of 2^v zeros then 2^v ones
        block = ((1 << (1 << v)) - 1) << (1 << v)
        period = 1 << (v + 1)
        pat = 0; reps = M // period
        # build by doubling
        pat = block; length = period
        while length < M: pat |= pat << length; length *= 2
        proj.append(pat & FULL)
    cur = proj
    for s in range(t):
        nxt = []
        for i in range(1, len(cur) - 1):
            l, c, r = cur[i - 1], cur[i], cur[i + 1]
            out = 0
            for k in range(8):
                if (rule >> k) & 1:
                    a = l if (k >> 2) & 1 else FULL ^ l
                    b = c if (k >> 1) & 1 else FULL ^ c
                    d = r if k & 1 else FULL ^ r
                    out |= a & b & d
            nxt.append(out)
        cur = nxt
    f = cur[0]
    # Moebius transform on bits of f
    for v in range(n):
        sh = 1 << v
        # mask of positions x with bit v = 0
        block = (1 << sh) - 1; period = 2 * sh; pat = block; length = period
        while length < M: pat |= pat << length; length *= 2
        low = pat & FULL
        f ^= (f & low) << sh
    deg = 0
    x = f
    while x:
        lsb = x & -x; idx = lsb.bit_length() - 1
        deg = max(deg, bin(idx).count('1')); x ^= lsb
    return deg
def center(rule, N):
    W = 2 * N + 5; off = N + 2
    row = 1 << off; bg = 0; cen = []
    mask = (1 << W) - 1
    for t in range(N):
        cen.append((row >> off) & 1)
        l = (row << 1) & mask; r = row >> 1
        # boundary: background bit bg extends both sides
        if bg: l |= 1; r |= 1 << (W - 1)
        out = 0
        for k in range(8):
            if (rule >> k) & 1:
                a = l if (k >> 2) & 1 else mask ^ l
                b = row if (k >> 1) & 1 else mask ^ row
                d = r if k & 1 else mask ^ r
                out |= a & b & d
        bg = (rule >> (7 * bg)) & 1
        row = out
    return cen
def eventual(seq):
    n = len(seq)
    for P in range(1, n // 4):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
res = []
for rule in range(256):
    d6 = anf_degree(rule, 6); d7 = anf_degree(rule, 7)
    ev = eventual(center(rule, 2000))
    res.append((rule, d6, d7, ev))
hi = [r for r in res if r[2] >= 12]
print("count deg7>=12:", len(hi), " of which eventually periodic center:", sum(1 for r in hi if r[3] is not None), " deg7==15 (max):", sum(1 for r in res if r[2] == 15), " of which periodic:", sum(1 for r in res if r[2] == 15 and r[3] is not None))
import sys; sys.exit(0)
print("rules with deg Phi_7 >= 12 (2t-2):")
for r in hi: print("  rule %3d deg6=%2d deg7=%2d center eventual (T,P)=%s" % r)
