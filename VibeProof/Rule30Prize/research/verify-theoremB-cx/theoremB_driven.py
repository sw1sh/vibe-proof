"""Adversarial simulation of Theorem B in the driven right half.

Right half = columns p >= 1, bit (p-1) of a Python int. Column 0 is the driver d(t).
  cell(t+1,p) = cell(t,p-1) xor (cell(t,p) or cell(t,p+1)),  cell(t,0) = d(t).
The int is never masked: the initial state is arbitrary on columns 1..W and white beyond, and the
simulation is exact for that (legitimate) initial state.

Scenario: driver arbitrary (random, or the REAL center column) for t < T, then periodic with
period P and repeating word a rotation of 1^r u. Checks, for the first window [t1,t1+r) >= T that
is all black (and also for every later window start in the first period):
  (i)   row at e_k = t1 + r + kP reads (0,1)^j on columns 1..2j        (step 1)
  (ii)  cell(e+s,1) = cell(e_k+s,1) for 0 <= s <= 2j-1                  (step 3)
  (iii) cell(e+s,1) = cell(e_k+s,1) = 0 for P-r+9 <= s <= P-1          (step 4)
  (iv)  column 1 is P-periodic from e on the whole horizon              (step 5)
  (v)   the column-1 trace over [e, e+P) depends only on (u, r) and the rotation offset of the
        window inside the black run (prediction of the proof) -- checked across random states.
"""
import random
import sys
import math

REAL = None


def real_center(n):
    global REAL
    if REAL is None or len(REAL) < n:
        data = open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin', 'rb').read((n + 7) // 8 + 1)
        bits = []
        for byte in data:
            for k in range(7, -1, -1):
                bits.append((byte >> k) & 1)
        REAL = bits
    return REAL[:n]


def simulate(row0, driver, steps):
    """Return list of rows (ints) at times 0..steps."""
    rows = [row0]
    x = row0
    for t in range(steps):
        x = (((x << 1) | driver[t]) ^ (x | (x >> 1)))
        rows.append(x)
    return rows


def bit(x, p):  # column p >= 1
    return (x >> (p - 1)) & 1


def threshold_j(P, r):
    return (P - r + 10) // 2  # = ceil((P-r+9)/2)


def run_case(u, r, rng, mode, extra_periods=6, pre_mode='random', tag=''):
    P = r + len(u)
    j = threshold_j(P, r)
    w = [1] * r + list(u)
    T = rng.randrange(0, 60)
    phase = rng.randrange(P)
    horizon = T + 2 * P + extra_periods * P + 5
    # driver
    if pre_mode == 'random':
        pre = [rng.randrange(2) for _ in range(T)]
    elif pre_mode == 'real':
        pre = real_center(T)
    else:
        pre = [0] * T
    drv = pre + [w[(t - T + phase) % P] for t in range(T, horizon + 1)]
    # initial right half
    W = rng.choice([1, 5, 50, horizon + 5])
    if mode == 'zero':
        row0 = 0
    elif mode == 'ones':
        row0 = (1 << W) - 1
    elif mode == 'alt':
        row0 = int('01' * (W // 2 + 1), 2) & ((1 << W) - 1)
    elif mode == 'alt2':
        row0 = int('10' * (W // 2 + 1), 2) & ((1 << W) - 1)
    else:
        dens = rng.choice([0.5, 0.1, 0.9, 0.3, 0.7])
        row0 = 0
        for p in range(W):
            if rng.random() < dens:
                row0 |= 1 << p
    rows = simulate(row0, drv, horizon)
    col1 = [bit(rows[t], 1) for t in range(horizon + 1)]
    # window starts t1 >= T with drv[t1..t1+r-1] all black, within the first period after T
    starts = [t1 for t1 in range(T, T + P) if all(drv[t1 + s] == 1 for s in range(r))]
    assert starts, (u, r, phase)
    fails = []
    traces = []
    for t1 in starts:
        e = t1 + r
        kmax = (horizon - e) // P - 1
        # (i)
        for k in range(0, kmax + 1):
            ek = e + k * P
            for i in range(1, j + 1):
                if bit(rows[ek], 2 * i - 1) != 0 or bit(rows[ek], 2 * i) != 1:
                    fails.append(('i', t1, k, i))
        # (ii), (iii)
        for k in range(0, kmax):
            ek = e + k * P
            for s in range(0, 2 * j):
                if s < P and col1[e + s] != col1[ek + s]:
                    fails.append(('ii', t1, k, s))
            for s in range(P - r + 9, P):
                if col1[e + s] != 0 or col1[ek + s] != 0:
                    fails.append(('iii', t1, k, s))
        # (iv)
        for t in range(e, horizon + 1 - P):
            if col1[t + P] != col1[t]:
                fails.append(('iv', t1, t))
                break
        traces.append((tuple(drv[e:e + P]), tuple(col1[e:e + P])))
    return fails, traces, P, j


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    total = 0
    nfail = 0
    trace_db = {}
    modes = ['random', 'random', 'random', 'zero', 'ones', 'alt', 'alt2']
    pres = ['random', 'real', 'none']
    # fixed words from the evidence plus random words
    fixed = ['0', '00', '010', '0110', '0000000', '01010101', '', '1', '11', '0' * 20, '1' * 7 + '0', '01' * 9]
    words = [tuple(int(ch) for ch in s) for s in fixed]
    for _ in range(150):
        L = rng.randrange(0, 22)
        words.append(tuple(rng.randrange(2) for _ in range(L)))
    for u in words:
        jth = math.ceil((len(u) + 9) / 2)
        rth = 9 * jth
        for r in sorted(set([rth, rth + 1, rth + 2, rth + rng.randrange(3, 30)])):
            P = r + len(u)
            assert 9 * threshold_j(P, r) <= r
            for rep in range(4):
                mode = rng.choice(modes)
                pre = rng.choice(pres)
                fails, traces, P, j = run_case(u, r, rng, mode, pre_mode=pre)
                total += 1
                if fails:
                    nfail += 1
                    print('FAIL', u, r, P, j, mode, pre, fails[:5])
                for dkey, tr in traces:
                    key = (r, P, dkey)
                    trace_db.setdefault(key, set()).add(tr)
    multi = {k: len(v) for k, v in trace_db.items() if len(v) > 1}
    print(f'cases: {total}, failing cases: {nfail}')
    print(f'(r,P,driver-after-window) keys: {len(trace_db)}, keys with >1 distinct column-1 period trace: {len(multi)}')
    if multi:
        print(list(multi.items())[:10])


if __name__ == '__main__':
    main()
