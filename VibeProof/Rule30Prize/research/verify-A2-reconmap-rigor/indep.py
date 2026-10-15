# Independent brute-force check of the ZBL reconstruction claims (a)-(f).
# Written from the rule-30 definition directly, sharing no code with A-reconmap/core.py.
# Position k >= 1 stands for cell -k; position 0 is held white.
import itertools, random

def step(row, n):
    """One ZBL step on positions 1..n of a row given as dict-free list r[0..n+1] (r[0]=0).
    Positions beyond the list are taken as white; returns list of length n+1 (index 0 = 0)."""
    get = lambda k: row[k] if 0 <= k < len(row) else 0
    out = [0] * (n + 1)
    for k in range(1, n + 1):
        out[k] = get(k + 1) ^ (get(k) | get(k - 1))
    return out

def evolve(L, T):
    """L: list with L[0]=0, L[1..n] the row. Returns rows[t] for t=0..T, each valid on 1..n-t
    (cells beyond n are unknown; we only use positions inside the dependence cone)."""
    rows = [list(L)]
    cur = list(L)
    n = len(L) - 1
    for _ in range(T):
        cur = step(cur, n)
        rows.append(cur)
    return rows

def trace(L, T):
    # boundary column y_t = position 1 at time t; valid while 1 + t <= n
    rows = evolve(L, T)
    return [rows[t][1] for t in range(T + 1)]

ok = True
# (a)+(c) at finite level: the map L(1..n) -> y_0..y_{n-1} is a bijection, and
# L(k) is determined by y_0..y_{k-1} (lower triangular), with pivot: y_{k-1} flips L(k).
for n in range(1, 15):
    seen = {}
    for bits in itertools.product((0, 1), repeat=n):
        L = [0] + list(bits)
        y = tuple(trace(L, n - 1))
        if y in seen:
            ok = False; print('not injective', n, bits, seen[y]); break
        seen[y] = bits
    if len(seen) != 2 ** n:
        ok = False; print('not onto', n)
    # triangularity / pivot: for each k, L(k) as a function of y_0..y_{k-1}
    for k in range(1, n + 1):
        fn = {}
        for y, bits in seen.items():
            key = y[:k]
            if key in fn and fn[key] != bits[k - 1]:
                ok = False; print('L(k) not a function of y_<k', n, k); break
            fn[key] = bits[k - 1]
        # pivot: flipping y_{k-1} flips L(k)
        for key, v in fn.items():
            key2 = key[:-1] + (1 - key[-1],)
            if fn[key2] == v:
                ok = False; print('pivot fails', n, k); break
print('(a),(b),(c) finite-level bijection/triangular/pivot for n<=14:', ok)

# (a) at general t: zrow L t k depends only on y_t..y_{t+k-1}
random.seed(7)
ok2 = True
for trial in range(3000):
    n = random.randint(4, 14)
    L1 = [0] + [random.getrandbits(1) for _ in range(n)]
    L2 = [0] + [random.getrandbits(1) for _ in range(n)]
    R1, R2 = evolve(L1, n), evolve(L2, n)
    for t in range(n):
        for k in range(1, n - t + 1):
            # need y_{t..t+k-1} defined: position 1 at time t+k-1 valid iff 1 + t + k - 1 <= n
            if t + k > n: continue
            if all(R1[t + i][1] == R2[t + i][1] for i in range(k)):
                if R1[t][k] != R2[t][k]:
                    ok2 = False
                # (b) pivot: k+1 <= n - t needed for position k+1 at time t to be valid
                if t + k + 1 <= n and (R1[t][k + 1] ^ R2[t][k + 1]) != (R1[t + k][1] ^ R2[t + k][1]):
                    ok2 = False
print('(a),(b) at general t (random pairs):', ok2)

# Phi via brute force inverse table, (d), (e)-style sanity, (f)
def Phi_prefix(f, n):
    """Rows positions 1..n of Phi f, via the finite bijection: y_{2s}=1, y_{2s+1}=f_s."""
    y = [1 if t % 2 == 0 else f[t // 2] for t in range(n)]
    # solve L(k) from y using the inverse recursion (independent derivation):
    # column k as a time series: c1 = y; c_{k+2}(t) = c_{k+1}(t+1) ^ (c_{k+1}(t) | c_k(t))
    cols = [[0] * (n + 1), list(y) + [0]]
    for k in range(0, n - 1):
        prev, cur = cols[k], cols[k + 1]
        cols.append([cur[t + 1] ^ (cur[t] | prev[t]) for t in range(len(cur) - 1)])
    return [0] + [cols[k][0] for k in range(1, n + 1)]

ok3 = True
for trial in range(500):
    m = random.randint(2, 12)
    f = [random.getrandbits(1) for _ in range(m + 2)]
    n = 2 * m + 1
    L = Phi_prefix(f, n)
    y = trace(L, n - 1)
    if y != [1 if t % 2 == 0 else f[t // 2] for t in range(n)]:
        ok3 = False; print('Phi trace mismatch')
    # (f): two steps of Phi f equal Phi(shift f) on the valid range 1..n-2
    R = evolve(L, 2)[2]
    L2 = Phi_prefix(f[1:], n - 2)
    if R[1:n - 1] != L2[1:n - 1]:
        ok3 = False; print('F^2 Phi != Phi shift', f)
print('Phi trace and (f) F^2 o Phi = Phi o shift (prefixes):', ok3)

# (d): L(2s+2) xor f_s depends only on f_<s; L(2s+3) depends only on f_<=s
ok4 = True
for m in range(1, 10):
    n = 2 * m + 1
    tab = {}
    for f in itertools.product((0, 1), repeat=m):
        tab[f] = Phi_prefix(list(f), n)
    for s in range(m):
        g, h = {}, {}
        for f, L in tab.items():
            key = f[:s]
            v = L[2 * s + 2] ^ f[s]
            if key in g and g[key] != v: ok4 = False
            g[key] = v
            if 2 * s + 3 <= n:
                key2 = f[:s + 1]
                if key2 in h and h[key2] != L[2 * s + 3]: ok4 = False
                h[key2] = L[2 * s + 3]
print('(d) triangular form for m<=9:', ok4)
