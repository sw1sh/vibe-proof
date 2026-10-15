"""Independent checks for claim B_right_edge_odometer.

Rule  l xor g(c, r)  from a single black cell, right diagonals R_j(t) = cell(t, t - j).
Checks:
  1. direct CA simulation == diagonal recurrence R_j(t+1) = R_j(t) xor g(R_{j-1}(t), R_{j-2}(t)),
     R_{-1} = R_{-2} = 0, R(0) = e_0   (i.e. G^t(e_0) = R(t)).
  2. rule 30: least periods 2^{e_j} vs the brief's list; least period > ceil(j/2).
  3. truncated orbit (R_0..R_J)(t): least period 2^{E_J}, points in one period pairwise distinct.
  4. conjugacy psi(alpha+1) = G(psi(alpha)) at "negative" 2-adic points alpha = -1, -2, ..., and
     at random residues.
  5. all 8 rules l xor g(c,r) with g(0,0)=0: diagonal periods are powers of 2; growth of E_J.
  6. centers of rules 90, 150, 210 (claim F) and rule 60 diagonal period formula.
"""
import math
import random
import sys

import numpy as np


def g_of(rule):
    """Return g as a dict {(c,r): bit} if rule == l xor g(c,r), else None."""
    bit = lambda l, c, r: (rule >> (4 * l + 2 * c + r)) & 1
    g = {}
    for c in (0, 1):
        for r in (0, 1):
            g0 = bit(0, c, r)
            g1 = bit(1, c, r)
            if g1 != 1 ^ g0:
                return None
            g[(c, r)] = g0
    return g


def simulate(rule, T):
    """rows[t] as numpy array over positions -T..T (index p + T)."""
    W = 2 * T + 3
    off = T + 1
    row = np.zeros(W, dtype=np.uint8)
    row[off] = 1
    rows = [row.copy()]
    tbl = np.array([(rule >> k) & 1 for k in range(8)], dtype=np.uint8)
    for t in range(T):
        l = np.roll(row, 1)
        r = np.roll(row, -1)
        idx = 4 * l + 2 * row + r
        new = tbl[idx]
        new[0] = 0
        new[-1] = 0
        row = new
        rows.append(row.copy())
    return rows, off


def diag_recurrence(g, J, N):
    """R[j] for j = 0..J on t in [0, N) via the recurrence (vectorized as prefix xor)."""
    R = {-2: np.zeros(N, dtype=np.uint8), -1: np.zeros(N, dtype=np.uint8)}
    gt = np.array([[g[(0, 0)], g[(0, 1)]], [g[(1, 0)], g[(1, 1)]]], dtype=np.uint8)
    # R_0: R_0(0) = 1, R_0(t+1) = R_0(t) xor g(0,0) = R_0(t)
    for j in range(0, J + 1):
        inp = gt[R[j - 1], R[j - 2]]
        x0 = 1 if j == 0 else 0
        acc = np.bitwise_xor.accumulate(inp)
        out = np.empty(N, dtype=np.uint8)
        out[0] = x0
        out[1:] = acc[:-1] ^ x0
        R[j] = out
    return R


def least_period(u):
    """least P (any integer) with u[t+P] = u[t] on the available range, P <= len(u)//2."""
    n = len(u)
    for P in range(1, n // 2 + 1):
        if np.array_equal(u[P:], u[:n - P]):
            return P
    return None


def least_period_pow2(u):
    n = len(u)
    P = 1
    while 2 * P <= n:
        if np.array_equal(u[P:], u[:n - P]):
            return P
        P *= 2
    return None


def main():
    out = []
    ok = True
    # ---------------- 1. direct simulation vs recurrence, all 8 rules ----------------
    rules = [r for r in range(256) if g_of(r) is not None and g_of(r)[(0, 0)] == 0]
    out.append(f"rules of form l xor g(c,r), g(0,0)=0: {rules}")
    T = 300
    for rule in rules:
        g = g_of(rule)
        rows, off = simulate(rule, T)
        R = diag_recurrence(g, 2 * T, T + 1)
        for j in range(0, 2 * T + 1):
            direct = np.array([rows[t][off + t - j] if t - j >= -T else 0 for t in range(T + 1)], dtype=np.uint8)
            if not np.array_equal(direct, R[j][:T + 1]):
                out.append(f"MISMATCH rule {rule} j={j}")
                ok = False
                break
        # right of right edge is zero
        for t in range(T + 1):
            if rows[t][off + t + 1:].any():
                out.append(f"rule {rule}: nonzero right of right edge at t={t}")
                ok = False
                break
    out.append(f"1. direct CA == diagonal recurrence for t <= {T}, all j: {'OK' if ok else 'FAIL'}")

    # ---------------- 2. rule 30 periods ----------------
    brief_e = [int(x) for x in "0 1 1 2 3 3 4 5 5 6 6 6 6 6 6 7 8 8 8 8 8 8 8 8 9 10 10 11 11 12 12 12 12 12 13 13 14 15 15 16 16 17 17 18 18 18 18 18 19 20 20 21 21 21 22 23 23 23 24 24 25 25 25 26 27 27 28 28 28 29 30 30 31 31 32".split()]
    LOGN = 22
    N = 1 << LOGN
    g30 = g_of(30)
    J30 = 52
    R30 = diag_recurrence(g30, J30, N)
    e30 = []
    fails2 = []
    for j in range(J30 + 1):
        P = least_period_pow2(R30[j])
        if P is None or 2 * P > N:
            break
        # also any-integer least period (sanity: should be the same power of 2) for small P
        if P <= 4096:
            Pany = least_period(R30[j][: 4 * P])
            if Pany != P:
                fails2.append(("least period not pow2", j, P, Pany))
        e = P.bit_length() - 1
        e30.append(e)
        if e != brief_e[j]:
            fails2.append(("brief e", j, e, brief_e[j]))
        if not P > math.ceil(j / 2):
            fails2.append(("P > ceil(j/2)", j, P))
        # zero run: R_j(t) = 0 for t < ceil(j/2), R_j(ceil(j/2)) = 1
        m = (j + 1) // 2
        if R30[j][:m].any() or R30[j][m] != 1:
            fails2.append(("zero-run", j))
    out.append(f"2. rule 30 e_j (j<={len(e30)-1}): {e30}")
    out.append(f"   checks vs brief, P_j > ceil(j/2), zero-run then 1: {fails2 if fails2 else 'OK'}")

    # ---------------- 3. truncated orbit ----------------
    fails3 = []
    Jmax3 = 0
    for J in range(0, len(e30)):
        EJ = max(e30[: J + 1])
        if EJ > 18:
            break
        L = 1 << EJ
        # pack (R_0..R_J)(t) into python ints via numpy object accumulation (J <= 60 fits in uint64)
        packed = np.zeros(2 * L, dtype=np.uint64)
        for j in range(J + 1):
            packed |= (R30[j][: 2 * L].astype(np.uint64) << np.uint64(j))
        if not np.array_equal(packed[L:2 * L], packed[:L]):
            fails3.append(("not periodic 2^EJ", J))
        if len(np.unique(packed[:L])) != L:
            fails3.append(("not distinct", J))
        if EJ >= 1:
            h = L // 2
            if np.array_equal(packed[h:h + L], packed[:L]):
                fails3.append(("period smaller", J))
        Jmax3 = J
    out.append(f"3. truncated orbit least period 2^E_J and distinct points, J <= {Jmax3}: {fails3 if fails3 else 'OK'}")

    # ---------------- 4. conjugacy at 2-adic points ----------------
    J4 = Jmax3
    EJ = max(e30[: J4 + 1])
    M = 1 << EJ

    def psi(alpha):  # alpha: python int (any sign), truncated to j <= J4
        return [int(R30[j][alpha % (1 << e30[j])]) for j in range(J4 + 1)]

    def G(y):
        z = []
        for j in range(len(y)):
            a = y[j - 1] if j >= 1 else 0
            b = y[j - 2] if j >= 2 else 0
            z.append(y[j] ^ (a | b))
        return z

    fails4 = []
    rng = random.Random(7)
    pts = list(range(-50, 50)) + [rng.randrange(-10 ** 30, 10 ** 30) for _ in range(300)]
    for a in pts:
        if G(psi(a)) != psi(a + 1):
            fails4.append(a)
    out.append(f"4. psi(a+1) == G(psi(a)) on j <= {J4} for {len(pts)} points incl. negatives: {fails4[:5] if fails4 else 'OK'}")
    # psi(-1) is the G-preimage of e_0
    out.append(f"   psi(-1)[:24] = {''.join(map(str, psi(-1)[:24]))}")

    # ---------------- 5. general rules: periods are powers of 2; growth ----------------
    LOG5 = 18
    N5 = 1 << LOG5
    for rule in rules:
        g = g_of(rule)
        J5 = 40
        R = diag_recurrence(g, J5, N5)
        es = []
        bad = []
        for j in range(J5 + 1):
            P = least_period_pow2(R[j])
            if P is None or 2 * P > N5:
                es.append(None)
                continue
            if P <= 2048:
                Pany = least_period(R[j][: 4 * P])
                if Pany != P:
                    bad.append((j, P, Pany))
            if P > (1 << j):
                bad.append(("P > 2^j", j))
            es.append(P.bit_length() - 1)
        zero_diags = [j for j in range(J5 + 1) if not R[j].any()]
        gs = ''.join(str(g[k]) for k in [(0, 1), (1, 0), (1, 1)])
        out.append(f"5. rule {rule:3d} (g(0,1)g(1,0)g(1,1)={gs}): e_j j<= {J5}: {es}; identically-zero diags: {zero_diags[:12]}{'...' if len(zero_diags) > 12 else ''}; non-pow2: {bad if bad else 'none'}")

    # ---------------- 6. centers, rule 60 formula ----------------
    T6 = 3000
    for rule in (90, 150, 210, 60, 30):
        rows, off = simulate(rule, T6)
        c = np.array([rows[t][off] for t in range(T6 + 1)], dtype=np.uint8)
        P = None
        Tr = None
        # eventual period search: smallest P <= 64 with c[t+P]=c[t] for t >= 1000
        for q in range(1, 65):
            if np.array_equal(c[1000 + q:], c[1000:len(c) - q]):
                P = q
                break
        if P is not None:
            Tr = 0
            while not np.array_equal(c[Tr + P:], c[Tr:len(c) - P]):
                Tr += 1
        out.append(f"6. rule {rule}: center[:20]={''.join(map(str, c[:20]))}  eventual period (<=64, checked to t={T6}): {P}, transient {Tr}")
    g60 = g_of(60)
    R60 = diag_recurrence(g60, 300, 1 << 12)
    bad60 = []
    for j in range(301):
        P = least_period_pow2(R60[j])
        if P != (1 << math.ceil(math.log2(j + 1))):
            bad60.append((j, P))
        # binomial check
        tt = np.arange(1 << 12)
        if not np.array_equal(R60[j], ((tt & j) == j).astype(np.uint8)):
            bad60.append(("binom", j))
    out.append(f"6. rule 60: R_j(t) = binom(t,j) mod 2 and least period 2^ceil(log2(j+1)) for j<=300: {bad60 if bad60 else 'OK'}")
    # rule 210 == rule 90 single-seed pattern
    rows90, off = simulate(90, 1000)
    rows210, _ = simulate(210, 1000)
    same = all(np.array_equal(a, b) for a, b in zip(rows90, rows210))
    out.append(f"6. rule 210 single-seed pattern identical to rule 90 for t <= 1000: {same}")
    print("\n".join(out))


if __name__ == "__main__":
    main()
