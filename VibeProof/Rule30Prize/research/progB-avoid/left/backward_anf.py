# Backward (left-permutive) reconstruction of the zero-boundary left half (ZBL) from column -1.
# Column -1 pattern per block k (phases 0..3): pat = (0, y_k, 0, 1) for w=0001 skeleton.
# u_q(t): cell(t,-q). u_0 = 0 (effective boundary). u_{q+1}(t) = u_q(t+1) ^ (u_q(t) | u_{q-1}(t)).
# ANF over GF(2): a polynomial = frozenset of monomials; monomial = frozenset of variable indices.
import sys
def X(a, b): return a ^ b
def A(a, b):
    r = set()
    for m1 in a:
        for m2 in b:
            m = m1 | m2
            if m in r: r.remove(m)
            else: r.add(m)
    return frozenset(r)
def O(a, b): return X(X(a, b), A(a, b))
ONE = frozenset([frozenset()]); ZERO = frozenset()
def var(i): return frozenset([frozenset([i])])
def show(p):
    if not p: return '0'
    terms = []
    for m in sorted(p, key=lambda m: (len(m), sorted(m))):
        terms.append('1' if not m else '*'.join('y%d' % i for i in sorted(m)))
    return ' + '.join(terms)
pat = sys.argv[1] if len(sys.argv) > 1 else '0y01'   # per phase: '0','1','y' (free), 'n' (not y)
Q = int(sys.argv[2]) if len(sys.argv) > 2 else 24
start_phase = int(sys.argv[3]) if len(sys.argv) > 3 else 0
cpat = sys.argv[4] if len(sys.argv) > 4 else '0' * len(pat)
P = len(pat)
H = Q + 2
def col1(t):
    ph = (start_phase + t) % P; blk = (start_phase + t) // P
    ch = pat[ph]
    if ch == '0': return ZERO
    if ch == '1': return ONE
    if ch == 'y': return var(blk)
    if ch == 'n': return X(ONE, var(blk))
prev = [ONE if cpat[(start_phase + t) % len(cpat)] == '1' else ZERO for t in range(H)]   # u_0 = effective column 0
cur = [col1(t) for t in range(H)]   # u_1
rows = [cur[0]]
for q in range(1, Q):
    nxt = [X(cur[t + 1], O(cur[t], prev[t])) for t in range(H - q)]
    prev, cur = cur[:H - q], nxt
    rows.append(cur[0])
for q, p in enumerate(rows, 1):
    print('u_%d = %s' % (q, show(p) if len(p) < 40 else '(%d terms) %s ...' % (len(p), show(frozenset(sorted(p, key=len)[:6])))))
