# Symbolic structure of Psi: f -> x_0, where column -1 is y = (1, f0, 1, f1, 1, f2, ...).
# Truth tables over n free bits (bitmask functions over 2^n assignments, as python ints).
import sys
n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
N = 1 << n
FULL = (1 << N) - 1
def var(i):
    # truth table of f_i over all assignments a in [0, 2^n): bit a set iff (a >> i) & 1
    tt = 0
    for a in range(N):
        if (a >> i) & 1: tt |= 1 << a
    return tt
F = [var(i) for i in range(n)]
T = 2 * n            # times available for column -1
y = []
for t in range(T):
    y.append(FULL if t % 2 == 0 else F[t // 2])
cols = [[0] * T, y]   # column 0 (wall) and column -1
for k in range(2, T + 1):
    cur, prev = cols[-1], cols[-2]
    nxt = [cur[t + 1] ^ (cur[t] | prev[t]) for t in range(len(cur) - 1)]
    cols.append(nxt)
# x_0(-k) = cols[k][0]
def anf(tt):
    # Moebius transform: coefficients of monomials
    c = [(tt >> a) & 1 for a in range(N)]
    for i in range(n):
        for a in range(N):
            if (a >> i) & 1: c[a] ^= c[a ^ (1 << i)]
    return [a for a in range(N) if c[a]]
def mono(a):
    if a == 0: return '1'
    return '*'.join(f'f{i}' for i in range(n) if (a >> i) & 1)
for k in range(1, min(2 * n, 2 * n) + 1):
    if len(cols[k]) == 0: break
    tt = cols[k][0]
    ms = anf(tt)
    deg = max((bin(a).count('1') for a in ms), default=0)
    s = ' + '.join(mono(a) for a in ms[:12]) + (' + ...' if len(ms) > 12 else '')
    print(f'x0(-{k}) : deg {deg}, #monomials {len(ms)} : {s}')
