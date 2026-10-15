# Symbolic forced-cell analysis: driver word w, effective left boundary c' = w & rot(w),
# column -1 pattern pat over {0,1,*} (forced phases), free bits enumerated over K periods.
# Computes the left-permutive extension (with true c for the cell_left relation at column 0? No: we use
# the effective boundary c' consistently -- the extension x_{-2}(t) = a(t+1) xor (a(t) | c(t)) equals
# a(t+1) xor (a(t) | c'(t)) whenever the consistency relation holds) and reports, per column and phase,
# whether the cell value is forced (same for all free-bit assignments).
import sys, itertools
w = sys.argv[1]; pat = sys.argv[2]; K = int(sys.argv[3]); ncols = int(sys.argv[4])
p = len(w)
c = [int(w[t % p]) for t in range(p * K + 2)]
free = [ph for ph in range(p) if pat[ph] == '*']
n_free = len(free) * K
L = p * K
results = None
for bits in itertools.product((0, 1), repeat=n_free):
    it = iter(bits)
    a = []
    for t in range(L):
        ch = pat[t % p]
        a.append(next(it) if ch == '*' else int(ch))
    cols = {0: c[:L], -1: a}
    for n in range(1, ncols):
        xp, xq = cols[-n], cols[-n + 1]
        cols[-n - 1] = [xp[t + 1] ^ (xp[t] | xq[t]) for t in range(len(xp) - 1)]
    if results is None:
        results = {n: [set() for _ in range(len(cols[-n]))] for n in range(1, ncols + 1)}
    for n in range(1, ncols + 1):
        for t, v in enumerate(cols[-n]):
            results[n][t].add(v)
for n in range(1, ncols + 1):
    row = results[n]
    # only look at times where the dependency window is fully inside [0, L): t <= L - n
    s = ''.join(str(next(iter(v))) if len(v) == 1 else '*' for v in row[:max(0, L - n - 1)])
    # per phase summary over 'interior' times
    print('col -%2d: %s' % (n, s))
