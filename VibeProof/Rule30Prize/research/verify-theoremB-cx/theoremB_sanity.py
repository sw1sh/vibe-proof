"""(a) Detector sanity: below the threshold r < 9*ceil((P-r+9)/2) the periodicity-from-e check
should sometimes fail (the theorem says nothing there; failures show the checker is live).
(b) Realistic scenario: driver = REAL center column for t < T (T up to 6000), periodic after;
right half starts all white at time 0 (exactly the real right half). Check (i)-(iv).
(c) Prediction (v) with many samples per key: column-1 trace over one period from e is the same
for all initial states, for fixed u, r and window alignment.
"""
import random
import sys
import math
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-theoremB-cx')
import theoremB_driven as M


def periodic_from_e(u, r, rng, mode='random'):
    P = r + len(u)
    w = [1] * r + list(u)
    T = 0
    phase = 0  # window starts at t1 = 0
    horizon = 12 * P
    drv = [w[t % P] for t in range(horizon + 1)]
    W = horizon + 5
    row0 = 0
    for p in range(W):
        if rng.random() < 0.5:
            row0 |= 1 << p
    rows = M.simulate(row0, drv, horizon)
    col1 = [M.bit(rows[t], 1) for t in range(horizon + 1)]
    e = r
    ok_from_e = all(col1[t + P] == col1[t] for t in range(e, horizon + 1 - P))
    # eventual periodicity on the last half (weak check)
    ok_late = all(col1[t + P] == col1[t] for t in range(horizon // 2, horizon + 1 - P))
    return ok_from_e, ok_late


def main():
    rng = random.Random(7)
    print('(a) below-threshold detector sanity')
    for u in [(0,), (0, 0), (0, 1, 0), (0, 1, 1, 0), (0,) * 7, (0, 1) * 4, (0, 0, 0, 1)]:
        jth = math.ceil((len(u) + 9) / 2)
        rth = 9 * jth
        line = []
        for r in [rth - 1, rth - 5, rth - 9, rth - 18, 20, 12, 9]:
            if r < 1:
                continue
            res = [periodic_from_e(u, r, rng) for _ in range(30)]
            nf = sum(1 for a, b in res if not a)
            nl = sum(1 for a, b in res if not b)
            line.append(f'r={r}: notPerFromE {nf}/30, notPerLate {nl}/30')
        print('  u=', ''.join(map(str, u)), 'thr', rth, '|', '; '.join(line))
        sys.stdout.flush()

    print('(b) realistic: real center column as pre-driver, right half white at time 0')
    total = 0
    bad = 0
    words = [(0,), (0, 0), (0, 1, 0), (0, 1, 1, 0), (0,) * 7, (0, 1) * 4]
    for _ in range(30):
        L = rng.randrange(0, 16)
        words.append(tuple(rng.randrange(2) for _ in range(L)))
    for u in words:
        jth = math.ceil((len(u) + 9) / 2)
        rth = 9 * jth
        for T in [rng.randrange(0, 6000) for _ in range(3)]:
            r = rth + rng.choice([0, 0, 1, 3, 10])
            P = r + len(u)
            j = M.threshold_j(P, r)
            w = [1] * r + list(u)
            phase = rng.randrange(P)
            horizon = T + 8 * P
            drv = M.real_center(T) + [w[(t - T + phase) % P] for t in range(T, horizon + 1)]
            rows = M.simulate(0, drv, horizon)
            col1 = [M.bit(rows[t], 1) for t in range(horizon + 1)]
            starts = [t1 for t1 in range(T, T + P) if all(drv[t1 + s] == 1 for s in range(r))]
            for t1 in starts:
                e = t1 + r
                total += 1
                okv = True
                for k in range(0, (horizon - e) // P):
                    ek = e + k * P
                    for i in range(1, j + 1):
                        if M.bit(rows[ek], 2 * i - 1) != 0 or M.bit(rows[ek], 2 * i) != 1:
                            okv = False
                if not all(col1[t + P] == col1[t] for t in range(e, horizon + 1 - P)):
                    okv = False
                if not okv:
                    bad += 1
                    print('  FAIL', u, r, T, t1)
    print(f'  windows checked: {total}, failures: {bad}')

    print('(c) trace uniqueness with many samples per key')
    worst = 0
    nkeys = 0
    for u in [(0,), (0, 1, 1, 0), (0, 1) * 4, (0,) * 7, (0, 0, 1, 0, 1, 1, 0, 1, 0)]:
        jth = math.ceil((len(u) + 9) / 2)
        r = 9 * jth
        P = r + len(u)
        traces = set()
        for _ in range(60):
            horizon = 4 * P
            w = [1] * r + list(u)
            drv = [w[t % P] for t in range(horizon + 1)]
            W = rng.choice([1, 10, horizon + 5])
            row0 = 0
            for p in range(W):
                if rng.random() < rng.choice([0.5, 0.2, 0.8]):
                    row0 |= 1 << p
            rows = M.simulate(row0, drv, horizon)
            col1 = [M.bit(rows[t], 1) for t in range(horizon + 1)]
            traces.add(tuple(col1[r:r + P]))
        nkeys += 1
        worst = max(worst, len(traces))
        print('  u=', ''.join(map(str, u)), 'r', r, 'distinct traces over 60 random states:', len(traces))
    print('  max distinct:', worst)


if __name__ == '__main__':
    main()
