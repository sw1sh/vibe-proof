# Algebraic (ANF) degree over GF(2) of f_n(x_{-n..n}) = (F^n x)_0 for ECA rules,
# and the single-seed center column, to test "degree growth => aperiodic center" claims.
import sys
def rule_fn(rule):
    return lambda a,b,c: (rule >> (a*4+b*2+c)) & 1
def center_after(rule, bits, n):
    f = rule_fn(rule)
    row = list(bits)
    for _ in range(n):
        row = [f(row[i-1], row[i], row[i+1]) for i in range(1, len(row)-1)]
    assert len(row) == 1
    return row[0]
def anf_degree(rule, n):
    m = 2*n+1
    N = 1 << m
    tt = bytearray(N)
    for x in range(N):
        bits = [(x >> i) & 1 for i in range(m)]
        tt[x] = center_after(rule, bits, n)
    # Moebius transform
    a = tt
    h = 1
    while h < N:
        for i in range(0, N, 2*h):
            for j in range(i, i+h):
                a[j+h] ^= a[j]
        h *= 2
    deg = max((bin(x).count('1') for x in range(N) if a[x]), default=-1)
    return deg
def single_seed_center(rule, T):
    f = rule_fn(rule)
    W = T + 2
    row = [0]*(2*W+1); row[W] = 1
    out = [1]
    for t in range(T):
        row = [0] + [f(row[i-1], row[i], row[i+1]) for i in range(1, len(row)-1)] + [0]
        out.append(row[W])
    return out
rules = [int(r) for r in sys.argv[1:]] or [30, 22]
for r in rules:
    degs = [anf_degree(r, n) for n in range(1, 7)]
    c = single_seed_center(r, 60)
    print(f"rule {r}: ANF degree of center-after-n, n=1..6: {degs}")
    print(f"   single-seed center column t=0..60: {''.join(map(str,c))}")
