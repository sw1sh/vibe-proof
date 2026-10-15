# Theorem B' in full generality (any block u, length 0..9): min j0 by brute force, then driven test.
import itertools, random, sys, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-bprime-cx')
from det_check import min_j0
from driven_check import col1_trace, periodic_from
random.seed(3)
t0 = time.time(); runs = 0; fails = 0; maxj = 0; hist = {}
for n in range(0, 10):
    for u in itertools.product((0, 1), repeat=n):
        if n >= 8 and random.random() > 0.15:   # subsample long blocks for time
            continue
        j0 = min_j0(u)
        hist[j0] = hist.get(j0, 0) + 1
        maxj = max(maxj, j0)
        for dr in (0, 3):
            r = max(9, 9 * j0) + dr
            word = [1] * r + list(u); P = len(word); N = 5 * P + 100
            for _ in range(4):
                tr = col1_trace(word, random.getrandbits(N + 1), N)
                ok, _ = periodic_from(tr, P, r)
                runs += 1; fails += (not ok)
print('min j0 histogram (all u, len<=9, len 8-9 subsampled):', dict(sorted(hist.items())))
print('runs', runs, 'fails', fails, 'time %.1fs' % (time.time() - t0))
