# For each ECA rule, simulate single seed and report whether the center column looks eventually periodic.
import sys
def step(rule, row, off):
    # row: dict-free list representation with offset; use python int bits: bit k <-> position k-off
    pass

def simulate(rule, T):
    # positions -T-2..T+2 ; bit index = pos + T + 2
    W = 2*T + 5
    off = T + 2
    x = 1 << off
    mask = (1 << W) - 1
    col = []
    for t in range(T):
        col.append((x >> off) & 1)
        l = (x << 1) & mask   # bit i gets x_{i-1}
        c = x
        r = x >> 1            # bit i gets x_{i+1}
        new = 0
        for k in range(8):
            if (rule >> k) & 1:
                p = (k >> 2) & 1; q = (k >> 1) & 1; s = k & 1
                term = (l if p else ~l) & (c if q else ~c) & (r if s else ~r) & mask
                new |= term
        x = new & mask
    return col

def eventual_period(col, maxp=256, tail_from=None):
    n = len(col)
    start = tail_from if tail_from is not None else n // 2
    for p in range(1, maxp + 1):
        if all(col[t] == col[t + p] for t in range(start, n - p)):
            # find minimal preperiod
            T0 = start
            while T0 > 0 and col[T0 - 1] == col[T0 - 1 + p]:
                T0 -= 1
            return p, T0
    return None

def lp(rule):
    # left permutive: f(p,q,r) != f(1-p,q,r) for all q,r
    return all(((rule >> (4 | (q << 1) | r)) & 1) != ((rule >> ((q << 1) | r)) & 1) for q in (0, 1) for r in (0, 1))

T = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
print('Left-permutive ECAs, quiescent (f(000)=0), with f(001) value, single-seed center column eventual period (period, preperiod) or None:')
for rule in range(256):
    if not lp(rule):
        continue
    quiescent = (rule & 1) == 0
    f001 = (rule >> 1) & 1
    col = simulate(rule, T)
    ep = eventual_period(col)
    print(rule, 'quiescent' if quiescent else 'nonquiescent', 'f001=%d' % f001, 'center:', ''.join(map(str, col[:40])), '... ->', ep)
