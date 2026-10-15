# Theta(f)(k) as Boolean functions of f_0..f_{n-1}; truth tables as python ints over 2^n assignments.
import sys
n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
N = 1 << n
ALL = (1 << N) - 1
def var(i):
    # bit a of result = bit i of a
    x = 0
    blk = 1 << i
    pat = ((1 << blk) - 1) << blk
    per = 2 * blk
    x = 0
    for start in range(0, N, per):
        x |= pat << start
    return x & ALL
V = [var(i) for i in range(n)]
T = 2 * n
X1 = [ALL if t % 2 == 0 else V[t // 2] for t in range(T)]
X0 = [0] * (T + 1)
cols = [X0, X1]
L = [None, X1[0]]
for k in range(1, T - 1):
    a, b = cols[-2], cols[-1]
    nxt = [b[t + 1] ^ (b[t] | a[t]) for t in range(len(b) - 1)]
    cols.append(nxt)
    L.append(nxt[0])
# ANF via Moebius transform
def anf(tt):
    a = [(tt >> i) & 1 for i in range(N)]
    h = 1
    while h < N:
        for i in range(N):
            if i & h: a[i] ^= a[i ^ h]
        h <<= 1
    return [i for i in range(N) if a[i]]
def mono(m):
    if m == 0: return '1'
    return ''.join('f%d' % i for i in range(n) if m >> i & 1)
for k in range(1, min(len(L), 2 * n)):
    if (k - 1) // 2 >= n + 1: break
    ms = anf(L[k])
    deg = max((bin(m).count('1') for m in ms), default=0)
    s = ' + '.join(mono(m) for m in sorted(ms, key=lambda m: (bin(m).count('1'), m)))
    if len(s) > 300: s = s[:300] + ' ...'
    print(f"L({k}) deg={deg} nterms={len(ms)}: {s}")
