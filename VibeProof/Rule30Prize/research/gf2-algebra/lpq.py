# All ECA of the form new = l xor g(c, r) with g(0,0) = 0: center column from a single seed.
import itertools
def rule_number(f):
    return sum(f(l, c, r) << (4 * l + 2 * c + r) for l in (0, 1) for c in (0, 1) for r in (0, 1))
def run(f, N):
    W = 2 * N + 3; off = N + 1
    row = [0] * W; row[off] = 1; center = []; colm = {}
    for t in range(N):
        center.append(row[off])
        new = [0] * W
        for p in range(1, W - 1): new[p] = f(row[p - 1], row[p], row[p + 1])
        row = new
    return center
def eventual(seq):
    n = len(seq)
    for P in range(1, n // 4):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
gs = {'0': lambda c, r: 0, 'c': lambda c, r: c, 'r': lambda c, r: r, 'c^r': lambda c, r: c ^ r,
      'c&r': lambda c, r: c & r, 'c|r': lambda c, r: c | r, 'c&~r': lambda c, r: c & (1 - r), '~c&r': lambda c, r: (1 - c) & r}
N = 1200
for name, g in gs.items():
    f = lambda l, c, r, g=g: l ^ g(c, r)
    cen = run(f, N)
    leftgrow = g(0, 1)
    print(f"g={name:5s} rule {rule_number(f):3d}  left edge moves: {bool(leftgrow)}  center[0:40]={''.join(map(str, cen[:40]))}  eventual (T,P) on {N}: {eventual(cen)}")
