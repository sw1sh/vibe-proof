"""
End-to-end test of steps 1-5 of Theorem B in the driven right-half model.

Model: columns 1..W (bit p-1 of an int), driven by column 0 = d(t).
  new(p) = old(p-1) xor (old(p) or old(p+1)),  old(0) = d(t).
Column 1 at time t <= W-2 equals that of a genuine infinite evolution from any extension
of the initial row (light cone), so W >= H + 2 makes all recorded values exact.

Driver: random prefix of length T, then w^infinity with w a rotation of 1^r u, |w| = P.
Claim tested (what the proof establishes, independent of the left half):
  for t1 the start of a black window of length r at or after T, with
  9*ceil((P-r+9)/2) <= r, column 1 satisfies col1(t+P) = col1(t) for all t >= e = t1 + r.
We test the exact start e (not 'eventually'), over random u, random rotations, random
prefixes and random initial right-half states.
Negative controls: (a) same check starting at e-1 or earlier (expected to fail sometimes),
(b) r one or more below the threshold (expected to fail sometimes), to show the test is sensitive.
"""
import random, sys

def ceil_half(n):
    return (n + 1) // 2

def simulate_col1(init_row, W, drivers):
    mask = (1 << W) - 1
    row = init_row
    col1 = [row & 1]
    for d in drivers:
        left = ((row << 1) | d) & mask
        right = row >> 1
        row = (left ^ (row | right)) & mask
        col1.append(row & 1)
    return col1  # col1[t] for t = 0..len(drivers)

def periodic_from(col, start, P):
    for t in range(start, len(col) - P):
        if col[t + P] != col[t]:
            return False
    return True

rng = random.Random(20261015)

def one_test(u, r, extra_periods=6, check_shift=0):
    P = r + len(u)
    w = [1] * r + u
    rho = rng.randrange(P)
    wrot = w[rho:] + w[:rho]
    T = rng.randrange(0, 60)
    t1 = T + ((P - rho) % P)
    e = t1 + r
    H = e + extra_periods * P + 50
    prefix = [rng.randrange(2) for _ in range(T)]
    drivers = prefix + [wrot[i % P] for i in range(H - T)]
    # sanity: window [t1, t1+r) black
    assert all(drivers[t1 + s] == 1 for s in range(r))
    W = H + 3
    init_row = rng.getrandbits(W)
    col1 = simulate_col1(init_row, W, drivers)
    return periodic_from(col1, e - check_shift, P)

