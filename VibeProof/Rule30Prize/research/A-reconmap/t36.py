import sys, itertools, time
sys.path.insert(0, '.')
from t8 import step
def tail_profile(a, P, bmax, cap=3_000_000):
    p = len(P)
    states = {(0, 0)}
    for k in range(0, bmax):
        new = set()
        ys = (1,) if k % 2 == 0 else (0, 1)
        target = P[(k + 1) % p]
        for (Dkm1, Dk) in states:
            for yk in ys:
                Dn = step(Dkm1, Dk, k, yk)
                if k + 1 >= a and (Dn & 1) != target: continue
                new.add((Dk, Dn))
        states = new
        if not states: return k + 1, 0
        if len(states) > cap: return None, len(states)
    return None, len(states)
a = int(sys.argv[1]); pmax = int(sys.argv[2])
t0 = time.time(); alive = []; cnt = 0; worst = 0
for p in range(1, pmax + 1):
    for P in itertools.product((0, 1), repeat=p):
        if any(p % d == 0 and P == P[:d] * (p // d) for d in range(1, p)): continue
        cnt += 1
        b, nst = tail_profile(a, P, 4 * a + 40)
        if b is None: alive.append((''.join(map(str, P)), nst))
        else: worst = max(worst, b / a)
        if time.time() - t0 > 55: break
print('a=%d periods<=%d: %d primitive tails; compatible (alive): %s; worst death depth/a = %.2f (%.1fs)' % (a, pmax, cnt, alive, worst, time.time() - t0))
