# For n >= 0: count x in GF(2)^{2n+1} (positions -n..n) such that, evolving rule 30 inside the
# triangle with apex (n, 0):  A: cell(s, n-s) = 0 for s = 0..n  and  B: sum_{s=0..n} cell(s, s-n) = n (mod 2).
# Also count A alone, and the full-monomial coefficient of Phi_{n+2} directly.
import sys, itertools
def rows(x, n):
    # x: list of 2n+1 bits for positions -n..n ; returns dict (s,p) -> bit within triangle
    cur = {p: x[p + n] for p in range(-n, n + 1)}
    out = {(0, p): cur[p] for p in cur}
    for s in range(1, n + 1):
        nxt = {}
        for p in range(-n + s, n - s + 1):
            nxt[p] = cur[p - 1] ^ (cur[p] | cur[p + 1])
            out[(s, p)] = nxt[p]
        cur = nxt
    return out
def phi(x, t):  # x positions -t..t, returns cell(t, 0)
    cur = list(x)
    for s in range(t):
        cur = [cur[i - 1] ^ (cur[i] | cur[i + 1]) for i in range(1, len(cur) - 1)]
    return cur[0]
for n in range(0, 8):
    cA = cAB = 0
    for bits in itertools.product((0, 1), repeat=2 * n + 1):
        r = rows(bits, n)
        if all(r[(s, n - s)] == 0 for s in range(n + 1)):
            cA += 1
            if sum(r[(s, s - n)] for s in range(n + 1)) % 2 == n % 2: cAB += 1
    t = n + 2
    # full monomial coefficient of Phi_t on x_{-t+2..t}: sum over y with x_{-t}=x_{-t+1}=0
    top = 0
    if 2 * t - 1 <= 15:
        for y in itertools.product((0, 1), repeat=2 * t - 1):
            top ^= phi((0, 0) + y, t)
    print(f"n={n} t={t}: #A={cA} #(A and B)={cAB} parity={cAB % 2} topcoef={top if 2*t-1<=15 else '-'}")
