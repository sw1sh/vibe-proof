"""Index arithmetic of the proof (exhaustive over P <= 3000) and random tests of the cone lemma.

Arithmetic, for all 1 <= P <= 6000 (A3/A4 by direct loop for P <= 400), 0 <= r <= P with 9*ceil((P-r+9)/2) <= r:
  A1 Lean's (P - r + 10) // 2 equals ceil((P - r + 9)/2)
  A2 2j >= P-r+9 and 9j <= r (j = ceil((P-r+9)/2))
  A3 every s in [0, P-1] satisfies s <= 2j-1 (cone) or P-r+9 <= s <= P-1 (next run)
  A4 for s in [P-r+9, P-1]: [s-9, s) is inside [P-r, P)  (the next black run, offsets from e)
  A5 black stretch [e-9j, e) is inside [e-r, e)
  A6 r >= 0.82P + 8.2 (and r <= P) implies the condition; report the exact minimal r per P vs 0.82P+8.2
  A7 minimal admissible r is 45 (so the theorem is non-vacuous only for P >= 45)
Cone lemma: two right halves with equal columns 1..n at times t0, t1 and equal drivers from then on
agree at (t0+s, p) for 1 <= p, p+s <= n.  Also show the cone is the sharp region (disagreement
can occur at p+s = n+1), so the test is not trivially passing.
"""
import math
import random
import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-theoremB-cx')
import theoremB_driven as M


def arith():
    cnt = 0
    minr = None
    worst_gap = -1e9
    for P in range(1, 6001):
        rmin_P = None
        for r in range(0, P + 1):
            cond = 9 * math.ceil((P - r + 9) / 2) <= r
            assert ((P - r + 10) // 2) == math.ceil((P - r + 9) / 2)  # A1
            if not cond:
                if r >= 0.82 * P + 8.2:
                    print('A6 FAIL', P, r)
                continue
            cnt += 1
            if rmin_P is None:
                rmin_P = r
            j = math.ceil((P - r + 9) / 2)
            assert 2 * j >= P - r + 9 and 9 * j <= r  # A2
            for s in (range(P) if P <= 400 else []):
                assert s <= 2 * j - 1 or (P - r + 9 <= s <= P - 1)  # A3
                if P - r + 9 <= s <= P - 1:
                    assert P - r <= s - 9 and s - 1 < P  # A4
            assert r - 9 * j >= 0  # A5: e-9j >= e-r
            minr = r if minr is None else min(minr, r)
        if rmin_P is not None:
            worst_gap = max(worst_gap, rmin_P - (0.82 * P + 8.2))
    print(f'arith: {cnt} admissible (P,r) pairs checked; min admissible r = {minr}; '
          f'max over P of (min admissible r - (0.82P+8.2)) = {worst_gap:.3f} (<= 0 means 0.82P+8.2 suffices)')


def cone_tests():
    rng = random.Random(3)
    viol = 0
    edge_diff = 0
    for trial in range(3000):
        n = rng.randrange(1, 40)
        W = n + rng.randrange(0, 60)
        a = [rng.randrange(2) for _ in range(W)]
        b = a[:n] + [rng.randrange(2) for _ in range(W - n)]
        steps = rng.randrange(1, 50)
        drv = [rng.randrange(2) for _ in range(steps + 1)]
        xa = sum(v << i for i, v in enumerate(a))
        xb = sum(v << i for i, v in enumerate(b))
        ra = M.simulate(xa, drv, steps)
        rb = M.simulate(xb, drv, steps)
        for s in range(steps + 1):
            for p in range(1, n + 2):
                same = M.bit(ra[s], p) == M.bit(rb[s], p)
                if p + s <= n and not same:
                    viol += 1
                if p + s == n + 1 and not same:
                    edge_diff += 1
    print(f'cone lemma: violations {viol}; disagreements just outside the cone (p+s=n+1): {edge_diff}')


if __name__ == '__main__':
    arith()
    cone_tests()
