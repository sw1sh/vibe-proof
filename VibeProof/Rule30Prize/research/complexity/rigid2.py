# Period-2 hypothesis: c(T+2k)=1, c(T+2k+1)=0. Constraint A forces col_{-1}(T+2k)=1; s_k = col_{-1}(T+2k+1).
# Constraint B (column 1 rule) forces s to avoid "00" (golden mean).
# Compute columns -m (via left-permutivity) as functions of s; report columns/phases that are constant.
import itertools, sys
def golden(n):
    out = []
    for bits in itertools.product((0,1), repeat=n):
        if all(not (bits[i]==0 and bits[i+1]==0) for i in range(n-1)): out.append(bits)
    return out
N = int(sys.argv[1]) if len(sys.argv)>1 else 12
M = int(sys.argv[2]) if len(sys.argv)>2 else 16
words = golden(N)
vals = {}  # (m, j) -> set of values
for s in words:
    J = 2*N
    c = [1 if j%2==0 else 0 for j in range(J+1)]
    cols = {0: c, 1: [1 if j%2==0 else s[j//2] for j in range(J)]}
    for m in range(1, M):
        a, b = cols[m], cols[m-1]
        cols[m+1] = [a[j+1] ^ (a[j] | b[j]) for j in range(len(a)-1)]
    for m in range(1, M+1):
        for j in range(min(len(cols[m]), 2*N - m - 1)):
            vals.setdefault((m, j), set()).add(cols[m][j])
for m in range(1, M+1):
    row = []
    for j in range(0, 12):
        v = vals.get((m, j))
        if v is None: row.append('?')
        elif len(v) == 1: row.append(str(next(iter(v))))
        else: row.append('*')
    print(f"col -{m:2d}: " + ''.join(row))
