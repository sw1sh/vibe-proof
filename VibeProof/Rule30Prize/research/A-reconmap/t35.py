import sys, itertools, time
sys.path.insert(0, '.')
from t34 import tail_profile
t0 = time.time()
alive = []; cnt = 0; worst = 0
for p in (5, 6):
    for P in itertools.product((0, 1), repeat=p):
        if any(p % d == 0 and P == P[:d] * (p // d) for d in range(1, p)): continue
        cnt += 1
        for a in (12, 20):
            b, nst = tail_profile(a, P, 4 * a + 40)
            if b is None: alive.append((''.join(map(str, P)), a, nst))
            else: worst = max(worst, b / a)
print('periods 5,6: %d primitive tails tested at a in {12,20}; alive: %s; worst death depth / a = %.2f (%.1fs)' % (cnt, alive, worst, time.time() - t0))
