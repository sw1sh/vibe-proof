"""Stress: long u (up to 40), long horizons (20 periods), all window starts, random/real pre-drivers."""
import random, math, sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-theoremB-cx')
import theoremB_driven as M
rng = random.Random(int(sys.argv[1]))
tot = bad = 0
maxj = 0
for _ in range(120):
    L = rng.randrange(0, 41)
    # adversarial-ish u: random, all-zero, all-one, alternating, or with a long interior black run
    kind = rng.randrange(5)
    if kind == 0: u = tuple(rng.randrange(2) for _ in range(L))
    elif kind == 1: u = (0,) * L
    elif kind == 2: u = (1,) * L
    elif kind == 3: u = tuple(i % 2 for i in range(L))
    else:
        k = rng.randrange(0, L + 1); u = (0,) * (L - k) + (1,) * k
        u = u[::-1] if rng.random() < 0.5 else u
    r = 9 * math.ceil((len(u) + 9) / 2) + rng.choice([0, 0, 1, 2, 7])
    fails, traces, P, j = M.run_case(u, r, rng, rng.choice(['random', 'zero', 'ones', 'alt']), extra_periods=20,
                                     pre_mode=rng.choice(['random', 'real', 'none']))
    tot += 1; maxj = max(maxj, j)
    if fails:
        bad += 1; print('FAIL', u, r, fails[:3])
print(f'stress seed {sys.argv[1]}: cases {tot}, failures {bad}, max j {maxj}')
