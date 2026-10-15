# Period-2 hypothesis, left half, symbolic dependence analysis.
# Hypothesis: c(t) = t mod 2 (zeros at even t = 2k, ones at odd t), t >= 0 (relative time).
# Rule at column 0 when c(t)=1 forces col_{-1}(t) = not c(t+1) = 1 at odd t.
# col_{-1}(2k) = u_k free.  Rule at column 1 forces u to avoid "00" (golden mean shift).
# Spatial (leftward) reconstruction: x_{n+1}(t) = x_n(t+1) xor (x_n(t) or x_{n-1}(t)), x_0 = c, x_1 = col_{-1}.
# Bit-sliced over all 2^W assignments of u_0..u_{W-1}.
import sys
W = int(sys.argv[1]) if len(sys.argv) > 1 else 16
NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 2 * W - 2
N = 1 << W
ALL = (1 << N) - 1
def var(k):
    # bit i of result = bit k of i
    blk = 1 << k
    pat = ((1 << blk) - 1) << blk          # within a 2*blk period, upper half ones
    reps = N // (2 * blk)
    # build by doubling
    x = pat
    period = 2 * blk
    cur = 1
    while cur < reps:
        x = x | (x << (period * cur))
        cur *= 2
    return x & ALL
U = [var(k) for k in range(W)]
# golden mean indicator: no two consecutive zeros among u_0..u_{W-1}
X = ALL
for k in range(W - 1):
    X &= (U[k] | U[k + 1])
L = 2 * W  # times 0..2W-1 have col_{-1} defined from u_0..u_{W-1}
x0 = [ALL if (t % 2 == 1) else 0 for t in range(L + 1)]
x1 = [(U[t // 2] if t % 2 == 0 else ALL) for t in range(L)]
cols = [x0, x1]
def flip(f, k):
    blk = 1 << k
    M = ALL ^ U[k]                 # indices with bit k = 0
    return ((f >> blk) & M) | ((f & M) << blk)
Xf = [X & flip(X, k) for k in range(W)]  # both word and its k-flip in X
def deps(f):
    return [k for k in range(W) if ((f ^ flip(f, k)) & Xf[k]) != 0]
def const_on_X(f):
    if f & X == 0: return 0
    if (f & X) == X: return 1
    return None
for n in range(1, NMAX):
    a, b = cols[-2], cols[-1]
    m = min(len(b) - 1, len(a))
    nxt = [b[t + 1] ^ (b[t] | a[t]) for t in range(m)]
    cols.append(nxt)
for n in range(0, min(NMAX, len(cols))):
    col = cols[n]
    out = []
    for t in range(min(4, len(col))):
        # only meaningful if all deps lie within the window: x_n(t) uses x_1 on [t, t+n-1] -> u up to (t+n-1)//2 < W
        if (t + n - 1) // 2 >= W: out.append('--'); continue
        c = const_on_X(col[t])
        out.append(str(c) if c is not None else 'u' + ','.join(map(str, deps(col[t]))))
    print(n, ' | '.join(out))
