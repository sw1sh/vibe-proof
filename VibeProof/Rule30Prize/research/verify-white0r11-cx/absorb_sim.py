# Drive the right half (columns >= 1) with column 0 = (0^r 1 1)^inf (any phase) from many initial
# configurations, and test the claimed dynamics: for r >= 10, a non-Z2 period (ell != r+2) is followed
# two periods later by the lock, the lock persists, and column 1 then reads 1^(r+1) 0; Z2 periods read
# 0^(r+1) 1.  For r in 6..9, test empirical eventual periodicity of column 1.
import numpy as np, random, sys, time

def true_row(T):
    # row T of rule 30 from a single cell, columns -T-1..T+1
    W = 2 * T + 3
    row = np.zeros(W, dtype=np.uint8); row[T + 1] = 1
    for t in range(T):
        l = np.concatenate(([0], row[:-1])); rr = np.concatenate((row[1:], [0]))
        row = l ^ (row | rr)
    return row  # index T+1 is column 0

def simulate(init, drv, steps):
    """init: numpy row for columns 1..W (index i = column i+1). drv(t) = column 0 at time t.
    Returns array col[t][p] for p = 1..4 (first few columns) and the full first-black positions."""
    W = len(init) + steps + 4
    row = np.zeros(W, dtype=np.uint8); row[:len(init)] = init
    cols = np.zeros((steps + 1, 6), dtype=np.uint8)
    fb = []
    for t in range(steps + 1):
        cols[t] = row[:6]
        nz = np.flatnonzero(row)
        fb.append(int(nz[0]) if len(nz) else None)
        if t == steps: break
        l = np.concatenate(([drv(t)], row[:-1])); rr = np.concatenate((row[1:], [0]))
        row = l ^ (row | rr)
    return cols, fb

def check_r(r, ninit, K, rng, kinds):
    Q = r + 2
    w = [0] * r + [1, 1]
    bad = []
    stats = {"z2_periods": 0, "lock_by_k": {}}
    for it in range(ninit):
        kind = kinds[it % len(kinds)]
        if kind == "true":
            T = rng.randint(1, 300)
            row = true_row(T)
            init = row[T + 2:]  # columns 1..T+1
        elif kind == "finite":
            n = rng.randint(1, 200)
            init = np.array([rng.randint(0, 1) for _ in range(n)], dtype=np.uint8)
        elif kind == "infinite":
            n = K * Q + Q + 10  # wide enough that column 1 is exact through all steps
            init = np.array([rng.randint(0, 1) for _ in range(n)], dtype=np.uint8)
        elif kind == "sparse":
            n = rng.randint(1, 400)
            init = np.zeros(n, dtype=np.uint8)
            for _ in range(rng.randint(1, 4)): init[rng.randint(0, n - 1)] = 1
        elif kind == "z2bait":
            # first black exactly at column r+3 (ell = r+2), rest random
            n = rng.randint(r + 3, r + 200)
            init = np.array([0] * (r + 2) + [1] + [rng.randint(0, 1) for _ in range(n - r - 3)], dtype=np.uint8)
        phase = rng.randint(0, Q - 1)
        drv = lambda t, phase=phase: w[(t + phase) % Q]
        steps = K * Q + Q
        cols, fb = simulate(init, drv, steps)
        # phase-0 times: t with (t + phase) % Q == 0
        a0 = (Q - phase) % Q
        starts = [a0 + k * Q for k in range(K) if a0 + k * Q + Q <= steps]
        ells = [fb[a] for a in starts]
        if r >= 10:
            locked_from = None
            for k, a in enumerate(starts):
                # column 1 pattern in this period
                pat = tuple(int(cols[a + i][0]) for i in range(Q))
                is_lock = cols[a][0] == 1
                if is_lock:
                    if pat != tuple([1] * (r + 1) + [0]): bad.append(("lockpattern", r, it, kind, k, pat)); break
                    if k + 1 < len(starts) and cols[starts[k + 1]][0] != 1: bad.append(("lockbreak", r, it, kind, k)); break
                if ells[k] == r + 2:
                    stats["z2_periods"] += 1
                    if pat != tuple([0] * (r + 1) + [1]): bad.append(("z2pattern", r, it, kind, k, pat)); break
                elif ells[k] is not None or True:
                    if k + 2 < len(starts) and cols[starts[k + 2]][0] != 1:
                        bad.append(("nolock2", r, it, kind, k, ells[k])); break
                if is_lock and locked_from is None: locked_from = k
            stats["lock_by_k"][locked_from] = stats["lock_by_k"].get(locked_from, 0) + 1
        else:
            # empirical: column 1 Q-periodic over the last 5 periods?
            last = [tuple(int(cols[a + i][0]) for i in range(Q)) for a in starts[-6:]]
            if len(set(last)) != 1:
                bad.append(("notperiodic_tail", r, it, kind, ells[-6:]))
    return bad, stats

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
t0 = time.time()
kinds = ["true", "finite", "infinite", "sparse", "z2bait"]
for r in list(range(6, 10)) + list(range(10, 41)):
    K = 25 if r < 10 else 12
    bad, stats = check_r(r, 60 if r >= 10 else 120, K, rng, kinds)
    if r >= 10:
        print(f"r={r}: bad={len(bad)} {bad[:3]} z2_periods={stats['z2_periods']} lock_from={sorted(stats['lock_by_k'].items(), key=lambda x: (x[0] is None, x[0]))}", flush=True)
    else:
        print(f"r={r}: tail-nonperiodic={len(bad)} {bad[:2]}", flush=True)
    if time.time() - t0 > 50: print("time budget hit at r", r); break
