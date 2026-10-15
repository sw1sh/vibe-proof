"""Earliest onset tau of P-periodicity of column 1 (driven right half, random state at time 0 = T,
random phase), compared with e = end of first full black window >= T (proof guarantees tau <= e)."""
import random, math, sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-theoremB-cx')
import theoremB_driven as M
rng = random.Random(11)
for s in ['0', '00', '010', '0110', '0000000', '01010101']:
    u = tuple(int(ch) for ch in s)
    r = 9 * math.ceil((len(u) + 9) / 2)
    P = r + len(u)
    w = [1] * r + list(u)
    taus = []; slack = []
    for trial in range(200):
        phase = rng.randrange(P)
        horizon = 10 * P
        drv = [w[(t + phase) % P] for t in range(horizon + 1)]
        W = horizon + 5
        x0 = sum((rng.randrange(2)) << p for p in range(W))
        rows = M.simulate(x0, drv, horizon)
        col1 = [M.bit(rows[t], 1) for t in range(horizon + 1)]
        # earliest tau with col1 P-periodic on [tau, horizon]
        tau = horizon - P
        while tau > 0 and col1[tau - 1 + P] == col1[tau - 1]:
            tau -= 1
        t1 = next(t for t in range(P) if all(drv[t + i] for i in range(r)))
        e = t1 + r
        taus.append(tau); slack.append(e - tau)
    print(f'u={s:9s} r={r} P={P}: onset tau (from T): max {max(taus)}, mean {sum(taus)/len(taus):.1f}; min(e - tau) = {min(slack)} (>=0 required)')
