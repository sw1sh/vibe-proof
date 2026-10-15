# z3: can the right half driven by periodic w (phase 0 at t=0) show column-1 pattern pat at times [t0, t0+len)?
import sys, z3
w = sys.argv[1]; pat = sys.argv[2]; t0s = [int(x) for x in sys.argv[3].split(',')]
p = len(w)
for t0 in t0s:
    L = t0 + len(pat)
    N = L + 2
    s = z3.Solver()
    X = [z3.Bool('x_%d' % i) for i in range(N + 1)]  # positions 1..N at time 0 (index 0 unused)
    row = {i: X[i] for i in range(1, N + 1)}
    cols1 = []
    for t in range(L):
        cols1.append(row[1])
        c = z3.BoolVal(w[t % p] == '1')
        new = {}
        for i in range(1, N + 1 - (t + 1)):
            left = c if i == 1 else row[i - 1]
            new[i] = z3.Xor(left, z3.Or(row[i], row[i + 1]))
        row = new
    for k, ch in enumerate(pat):
        s.add(cols1[t0 + k] == (ch == '1'))
    r = s.check()
    print(w, pat, 't0=%d' % t0, r)
