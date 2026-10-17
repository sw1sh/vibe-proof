"""Bounded search for eventually periodic readouts in the frozen-boundary core.

For a step g, an offset d >= 2, a right part rho < 2^d and a word w, the seed whose readout d is
w^infinity from time 0 is unique as a 2-adic integer (exact death). It is forced bit by bit: the
right part evolves on its own, R_{t+1} = g(R_t + w(t) 2^{t+d}) mod 2^{t+d+1}, and the columns
above d follow sideways from readout_left. A counterexample is a forced seed that is a natural
number, i.e. whose forced row is eventually white. Every eventually periodic readout becomes such
a readout after a restart (offset d + T, right part = low bits of g^T(x)).
Usage: python3 -I core_scan.py PMAX DMAX N
"""
import sys

def step(x, a, b, c):
    y = x ^ ((x << 1) | (x << 2))
    return y ^ ((1 if a else 0) + 2 * ((1 if b else 0) if y % 2 == 0 else (1 if c else 0)))

def forced_row_word(abc, d, rho, w, N):
    P = len(w)
    col0 = sum(1 << t for t in range(N) if w[t % P])
    R, u = rho, 0
    for t in range(N):
        u |= ((R >> (t + d - 1)) & 1) << t
        R = step(R + (w[t % P] << (t + d)), *abc) & ((1 << (t + d + 1)) - 1)
    prev, cur, row = u, col0, []
    for k in range(1, N):
        nxt = ((cur >> 1) ^ (cur | prev)) & ((1 << (N - k)) - 1)
        row.append(nxt & 1)
        prev, cur = cur, nxt
    return row

if __name__ == "__main__":
    PMAX, DMAX, N = map(int, sys.argv[1:4])
    words = [tuple((n >> i) & 1 for i in range(P)) for P in range(2, PMAX + 1) for n in range(1, (1 << P) - 1)]
    for name, abc, keep in [("Phi (control)", (0, 0, 0), lambda r: True),
                            ("white-blinking (1,0,1)", (1, 0, 1), lambda r: not (r >> 1) & 1),
                            ("(1,1,1)", (1, 1, 1), lambda r: True)]:
        runs = worst = 0; hits = []
        for d in range(2, DMAX + 1):
            for rho in range(1 << d):
                if not keep(rho): continue
                for w in words:
                    row = forced_row_word(abc, d, rho, w, N)
                    runs += 1
                    tail = 0
                    for v in reversed(row):
                        if v: break
                        tail += 1
                    worst = max(worst, tail)
                    if tail > N // 4: hits.append((d, rho, w, tail))
        print(f"{name}: {runs} (d, rho, word) runs, longest white tail of a forced row {worst} of {N - 1}; suspicious: {hits[:5]}")
