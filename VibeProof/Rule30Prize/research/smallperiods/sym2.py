# Symbolic left-permutive extension for period-2 center column with constraint (*):
# c(t) = (t+phase) % 2 ; when c(t)=1, a(t) = not c(t+1); a(t) free (alpha var) when c(t)=0.
# Cells are Boolean functions of alpha_0..alpha_{K-1}, stored as truth tables (int bitmask over 2^K assignments).
import sys
K = int(sys.argv[1]) if len(sys.argv)>1 else 10
phase = int(sys.argv[2]) if len(sys.argv)>2 else 0
NN = 1 << K
FULL = (1 << NN) - 1
def var(i):
    m = 0
    for x in range(NN):
        if (x >> i) & 1: m |= 1 << x
    return m
V = [var(i) for i in range(K)]
Tmax = 2*K  # times 0..Tmax-1
c = [FULL if (t+phase)%2==1 else 0 for t in range(Tmax+1)]
a = []
vi = 0
for t in range(Tmax):
    if (t+phase)%2==1:
        a.append(FULL ^ c[t+1])
    else:
        a.append(V[vi] if vi < K else None); vi += 1
cols = {0: c, -1: a}
def describe(m):
    if m == 0: return '0'
    if m == FULL: return '1'
    for i in range(K):
        if m == V[i]: return 'a%d'%i
        if m == FULL ^ V[i]: return '~a%d'%i
    # support
    sup = [i for i in range(K) if any(((m >> x) & 1) != ((m >> (x ^ (1<<i))) & 1) for x in range(NN))]
    return '{' + ','.join(map(str,sup)) + '}'
p = -1
while True:
    xp, xq = cols[p], cols[p+1]
    new = []
    for t in range(len(xp)-1):
        if xp[t] is None or xp[t+1] is None or xq[t] is None: new.append(None); continue
        new.append(xp[t+1] ^ (xp[t] | xq[t]))
    if not new or all(v is None for v in new): break
    cols[p-1] = new
    p -= 1
    if p < -14: break
for q in sorted(cols, reverse=True):
    print(q, ' '.join(describe(v) if v is not None else '?' for v in cols[q][:16]))
