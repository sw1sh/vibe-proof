"""Independent numerical check of claim C_mahler_linear_complexity_of_diagonals.

R_j(t) = cell(t, t-j) for rule 30 from a single black cell.
- Part A: direct CA simulation vs diagonal recurrence (small range).
- Part B: diagonal recurrence on N = 2^LOGN values, least period by direct shift test,
          Mahler coefficients by subset-sum (zeta) transform, linear complexity by
          Games-Chan (independent of Mahler), and checks of (a)-(d), (b) bounds.
"""
import sys
import math
import numpy as np

LOGN = int(sys.argv[1]) if len(sys.argv) > 1 else 22
N = 1 << LOGN

# ---------------- Part A: direct CA ----------------
T = 1024
W = 2 * T + 8
off = T + 4
row = np.zeros(W, dtype=np.uint8)
row[off] = 1
JA = 24
direct = np.zeros((JA + 1, T), dtype=np.uint8)
for t in range(T):
    for j in range(JA + 1):
        p = t - j
        direct[j, t] = row[off + p]
    left = np.roll(row, 1)    # left[i] = row[i-1]
    right = np.roll(row, -1)  # right[i] = row[i+1]
    row = left ^ (row | right)
    row[0] = 0
    row[-1] = 0


def excl_prefix_xor(v):
    c = np.bitwise_xor.accumulate(v)
    out = np.empty_like(v)
    out[0] = 0
    out[1:] = c[:-1]
    return out


# ---------------- Part B: diagonal recurrence ----------------
R = {}
R[-2] = np.zeros(N, dtype=np.uint8)
R[-1] = np.zeros(N, dtype=np.uint8)
R[0] = np.ones(N, dtype=np.uint8)

for j in range(0, JA + 1):
    if j >= 1:
        R[j] = excl_prefix_xor(R[j - 1] | R[j - 2])
    assert np.array_equal(R[j][:T], direct[j]), f"recurrence mismatch at j={j}"
print(f"Part A: diagonal recurrence matches direct CA for j<= {JA}, t < {T}")


def least_period_exp(u, bound_exp):
    """least f <= bound_exp with u(t+2^f)=u(t) on [0, 2^bound_exp); requires u 2^bound_exp-periodic"""
    P = 1 << bound_exp
    assert 2 * P <= len(u)
    # sanity: verify the 2^bound_exp-periodicity on available range
    assert np.array_equal(u[P:2 * P], u[:P])
    for f in range(0, bound_exp + 1):
        q = 1 << f
        if np.array_equal(u[q:q + P], u[:P]):
            return f
    raise AssertionError


def mahler(u_period):
    a = u_period.copy()
    n = len(a)
    h = 1
    while h < n:
        b = a.reshape(-1, 2, h)
        b[:, 1, :] ^= b[:, 0, :]
        h *= 2
    return a


def top_plus_one(mu):
    nz = np.nonzero(mu)[0]
    return 0 if len(nz) == 0 else int(nz[-1]) + 1


def games_chan(s):
    s = s.copy()
    n = len(s)
    L = 0
    while n > 1:
        h = n // 2
        a, b = s[:h], s[h:n]
        d = a ^ b
        if d.any():
            L += h
            s = d
        else:
            s = a
        n = h
    if s[0] == 1:
        L += 1
    return L


brief_e = [int(x) for x in "0 1 1 2 3 3 4 5 5 6 6 6 6 6 6 7 8 8 8 8 8 8 8 8 9 10 10 11 11 12 12 12 12 12 13 13 14 15 15 16 16 17 17 18 18 18 18 18 19 20 20 21 21 21 22 23 23 23 24 24 25 25 25 26 27 27 28 28 28 29 30 30 31 31 32".split()]

e = {-2: 0, -1: 0}
Lc = {-2: 0, -1: 0}
E = {}
j = 0
fails = []
while True:
    if j >= 1:
        if j not in R:
            R[j] = excl_prefix_xor(R[j - 1] | R[j - 2])
    # guaranteed period exponent from structure (summation of a 2^a periodic seq is 2^(a+1) periodic)
    bound = 0 if j == 0 else max(e[j - 1], e[j - 2]) + 1
    if 2 * (1 << bound) > N:
        break
    f = least_period_exp(R[j], bound)
    e[j] = f
    P = 1 << f
    mu = mahler(R[j][:P])
    Lj = top_plus_one(mu)
    gc = games_chan(R[j][:P])
    Lc[j] = Lj
    if gc != Lj:
        fails.append(("games-chan vs mahler", j, gc, Lj))
    # reconstruct from mahler on [0, 2P) to check expansion via Lucas
    if f <= 16:
        t = np.arange(2 * P)
        recon = np.zeros(2 * P, dtype=np.uint8)
        for m in np.nonzero(mu)[0]:
            recon ^= ((t & m) == m).astype(np.uint8)
        if not np.array_equal(recon, R[j][:2 * P]):
            fails.append(("mahler reconstruct", j))
    # e_j = ceil(log2 L_j)
    if f != (0 if Lj <= 1 else math.ceil(math.log2(Lj))):
        fails.append(("e=ceil log2 L", j, f, Lj))
    if j < len(brief_e) and brief_e[j] != f:
        fails.append(("brief e", j, brief_e[j], f))
    if j >= 1:
        # (a): L_j = L(input)+1 ; input has period 2^max(e_{j-1}, e_{j-2})
        a_exp = max(e[j - 1], e[j - 2])
        v = (R[j - 1] | R[j - 2])[: 1 << a_exp]
        Lv = top_plus_one(mahler(v))
        if Lj != Lv + 1:
            fails.append(("(a)", j, Lj, Lv))
    if j >= 2:
        # (b)
        lo = math.log2(math.ceil(j / 2) + 1)
        if not (lo <= f <= max(e[j - 1], e[j - 2]) + 1):
            fails.append(("(b)", j))
        if Lj <= math.ceil(j / 2):
            fails.append(("L_j > ceil(j/2)", j, Lj))
        # (c)
        if f > max(e[j - 1], e[j - 2]):
            if Lj != (1 << (f - 1)) + 1:
                fails.append(("(c)", j, Lj))
    j += 1

J = j - 1
# (d) check needs L_{j+1}
nd = 0
for j in range(2, J):
    if e[j] > max(e[j - 1], e[j - 2]) and Lc[j - 1] >= 2:
        nd += 1
        pred = (1 << (e[j] - 1)) + Lc[j - 1] + 1
        if Lc[j + 1] != pred:
            fails.append(("(d)", j, Lc[j + 1], pred))
print(f"Part B: computed j = 0..{J} (N = 2^{LOGN})")
print("e_j:", [e[i] for i in range(J + 1)])
print("L_j:", [Lc[i] for i in range(J + 1)])
print("number of (d) instances checked:", nd)
for jj, val in [(16, 129), (17, 194), (25, 513), (26, 770), (38, 24578), (49, 524289), (50, 786434)]:
    if jj <= J:
        print(f"L_{jj} = {Lc[jj]} (claimed {val})", "OK" if Lc[jj] == val else "MISMATCH")
print("FAILS:", fails if fails else "none")
