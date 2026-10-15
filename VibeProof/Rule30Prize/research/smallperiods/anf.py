# ANF of the time-0 row cells x_{-n}(0) as polynomials in alpha (period-2 left constraint), via Moebius transform.
import sys, itertools
K = int(sys.argv[1]); ph = int(sys.argv[2]); nmax = int(sys.argv[3])
def row_for(alpha):
    n = 2 * K + 2
    c = [(t + ph) % 2 for t in range(n + 2)]
    a = []; it = iter(alpha)
    for t in range(n + 1):
        if c[t] == 1: a.append(1 - c[t + 1])
        else:
            try: a.append(next(it))
            except StopIteration: a.append(None)
    cols = [c[:n+1], a]
    while len(cols[-1]) > 1:
        xp, xq = cols[-1], cols[-2]
        cols.append([None if (xp[t] is None or xp[t+1] is None or xq[t] is None) else xp[t+1] ^ (xp[t] | xq[t]) for t in range(len(xp)-1)])
    return [cols[k][0] for k in range(1, len(cols))]
N = 1 << K
rows = [row_for(tuple((m >> i) & 1 for i in range(K))) for m in range(N)]
for n in range(1, nmax + 1):
    f = [rows[m][n-1] for m in range(N)]
    if any(v is None for v in f): print('pos', -n, 'undetermined'); continue
    # Moebius
    g = f[:]
    for i in range(K):
        for m in range(N):
            if (m >> i) & 1: g[m] ^= g[m ^ (1 << i)]
    terms = [m for m in range(N) if g[m]]
    def tstr(m):
        if m == 0: return '1'
        return '*'.join('a%d' % i for i in range(K) if (m >> i) & 1)
    deg = max((bin(m).count('1') for m in terms), default=0)
    print('x_{-%d}(0): deg %d, %d terms: %s' % (n, deg, len(terms), ' + '.join(tstr(m) for m in terms) if len(terms) <= 12 else '...'))
