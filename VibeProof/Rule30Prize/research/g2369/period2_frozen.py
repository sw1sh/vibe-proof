"""Period 2 for the frozen-boundary steps: the sideways row.

Fix a step g = step(a, b, c), an offset d >= 1 and a right part rho < 2^d (bits 0..d-1 of the seed).
If readout d alternates 1, 0, 1, 0, ... from time 0, then:
  * the right part evolves on its own: R_{t+1} = g(R_t + alt(t) 2^{t+d}) mod 2^{t+d+1};
  * readout d-1 is u(t) = bit t+d-1 of R_t;
  * the left columns follow sideways (readout_left):
        col_{k+1}(t) = col_k(t+1) xor (col_k(t) or col_{k-1}(t)),  col_0 = alt, col_{-1} = u.
The seed's bits above d are then forced: bit d+k = col_k(0). So for each (g, d, rho) there is exactly
one 2-adic seed with that right part whose readout d alternates, and a finite counterexample exists
iff this forced row has finitely many black cells. Columns are Python ints, bit t = time t.
Usage: python3 -I period2_frozen.py N DMAX
"""
import sys

def step(x, a, b, c):
    y = x ^ ((x << 1) | (x << 2))
    return y ^ ((1 if a else 0) + 2 * ((1 if b else 0) if y % 2 == 0 else (1 if c else 0)))

def forced_row(abc, d, rho, N):
    alt = sum(1 << t for t in range(0, N, 2))
    R, u = rho, 0
    for t in range(N):
        u |= ((R >> (t + d - 1)) & 1) << t
        R = step(R + (((t + 1) % 2) << (t + d)), *abc) & ((1 << (t + d + 1)) - 1)
    prev, cur, row = u, alt, []
    for k in range(1, N):
        n = N - k
        nxt = ((cur >> 1) ^ (cur | prev)) & ((1 << n) - 1)
        row.append(nxt & 1)
        prev, cur = cur, nxt
    return u, row

if __name__ == "__main__":
    N, DMAX = int(sys.argv[1]), int(sys.argv[2])
    for abc in [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]:
        worst = None
        for d in range(1, DMAX + 1):
            for rho in range(1 << d):
                u, row = forced_row(abc, d, rho, N)
                last = max((k for k, v in enumerate(row) if v), default=-1)
                ones = sum(row)
                gap = 0; best = 0
                for v in row:
                    gap = 0 if v else gap + 1; best = max(best, gap)
                if worst is None or best > worst[0]:
                    worst = (best, d, rho, last, ones)
        print(abc, "longest white run in forced row (depth<%d):" % N, worst[0],
              "at d=%d rho=%d; last black depth %d, black count %d" % worst[1:])
