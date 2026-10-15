# Python model of the bit-sliced (lane) checker; compare with node-DFS deepest values.
import sys
def scanN(acc, As, Bs):
    out = []
    for i, a in enumerate(As):
        b = Bs[i] if i < len(Bs) else 0
        acc = acc ^ (a | b)
        out.append(acc)
    return out, acc
def pat(n, s):
    B = ((1 << (1 << s)) - 1) << (1 << s); ln = 1 << (s + 1)
    for _ in range(n - (s + 1)):
        B = B | (B << ln); ln *= 2
    return B
def run(W, n, c, K):
    N = 1 << n; ALL = (1 << N) - 1
    pats = [pat(n, s) for s in range(n)]
    R, Rm, alive = [], [], ALL
    for k in range(K):
        if k % 2 == 0:
            out, last = scanN(ALL, R, [0] + Rm); Rn = [ALL] + out
            if W < k + 1: alive &= ALL ^ last
        elif k + 1 <= W:
            s = k // 2
            y = pats[s] if s < n else (ALL if (c >> (s - n)) & 1 else 0)
            out, last = scanN(y, R, [0] + Rm); Rn = [y] + out
        else:
            out, T = scanN(0, R, [0] + Rm); Rn = [T] + [T ^ v for v in out]
        R, Rm = Rn, R
    return alive == 0
W = int(sys.argv[1]); K = int(sys.argv[2]); n = int(sys.argv[3])
nfree = W // 2
ok = all(run(W, n, c, K) for c in range(1 << (nfree - n)))
print("W", W, "K", K, "n", n, "chunks", 1 << (nfree - n), "ok", ok)
