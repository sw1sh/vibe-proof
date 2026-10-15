# Independent numeric sanity check: direct rule-30 simulation (bitset rows), right diagonals
# R_j(t) = cell(t, t-j), least periods within a window, and the claimed rules.
import sys
LOG = int(sys.argv[1]) if len(sys.argv) > 1 else 14
T = 1 << LOG
J = int(sys.argv[2]) if len(sys.argv) > 2 else 34
N = T + 2               # bit b <-> position p = b - N
W = 2 * N + 4
mask = (1 << W) - 1
row = 1 << N            # cell(0, 0) = 1
Rbits = [0] * (J + 1)   # Rbits[j] bit t = R_j(t)
for t in range(T):
    for j in range(J + 1):
        b = t - j + N
        if (row >> b) & 1:
            Rbits[j] |= 1 << t
    # new(p) = cell(p-1) xor (cell(p) or cell(p+1)); bit b gets left from b-1, right from b+1
    row = ((row << 1) ^ (row | (row >> 1))) & mask

def bit(x, t): return (x >> t) & 1

def least_period(x, L):
    # least p <= L/2 with x(t+p) = x(t) for all t < L - p (window check)
    for p in range(1, L // 2 + 1):
        m = (1 << (L - p)) - 1
        if ((x >> p) ^ x) & m == 0:
            return p
    return None

brief = [int(v) for v in "0 1 1 2 3 3 4 5 5 6 6 6 6 6 6 7 8 8 8 8 8 8 8 8 9 10 10 11 11 12 12 12 12 12 13 13 14 15 15 16 16 17 17 18 18 18 18 18 19 20 20 21 21 21 22 23 23 23 24 24 25 25 25 26 27 27 28 28 28 29 30 30 31 31 32".split()]
e = []
ok = True
for j in range(J + 1):
    p = least_period(Rbits[j], T)
    if p is None or p & (p - 1):
        print("j", j, "least window period", p, "not a power of 2 or too large"); ok = False; break
    e.append(p.bit_length() - 1)
print("e_j (window):", " ".join(map(str, e)))
print("matches brief:", e == brief[:len(e)])
for j in range(len(e) - 1):
    # (c) e_{j+1} = e_j + R_{j+1}(2^{e_j})
    if e[j + 1] != e[j] + bit(Rbits[j + 1], 1 << e[j]):
        print("e_step FAILS at j", j); ok = False
    # (a) monotone
    if e[j + 1] < e[j]:
        print("mono FAILS at j", j); ok = False
for j in range(2, len(e)):
    g = Rbits[j - 1] | Rbits[j - 2]
    pg = least_period(g, T)
    par = bin(g & ((1 << pg) - 1)).count("1") % 2
    if j >= 3 and pg != (1 << e[j - 1]):
        print("least period of g_j wrong at j", j, pg, 1 << e[j - 1]); ok = False
    if j >= 3 and e[j] - e[j - 1] != par:
        print("S rule fails at j", j); ok = False
    if j == 2:
        print("j=2: least period of g_2 =", pg, " 2^{e_1} =", 1 << e[1], " S_2 =", e[2] - e[1], " parity over least period =", par)
# shift formula / half-black in doubling case, on the window
for j in range(len(e) - 1):
    P = 1 << e[j]
    c = bit(Rbits[j + 1], P)
    for t in range(T - P):
        if bit(Rbits[j + 1], t + P) != bit(Rbits[j + 1], t) ^ c:
            print("shift formula fails j", j, "t", t); ok = False; break
print("ALL OK" if ok else "SOME CHECK FAILED")
