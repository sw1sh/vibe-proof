# GC check: for every primitive tail P of period <= pmax compatible at window start a, the surviving
# free-bit sequences are eventually periodic.
import sys, itertools, time
sys.path.insert(0, '.')
from t8 import step
def surv(a, P, depth, cap=200000):
    p = len(P)
    states = {(0, 0): ()}
    for k in range(depth):
        new = {}
        ys = (1,) if k % 2 == 0 else (0, 1)
        target = P[(k + 1) % p]
        for (Dkm1, Dk), h in states.items():
            for yk in ys:
                Dn = step(Dkm1, Dk, k, yk)
                if k + 1 >= a and (Dn & 1) != target: continue
                new.setdefault((Dk, Dn), h + (yk,))
        states = new
        if not states or len(states) > cap: break
    return list(states.values())
a = int(sys.argv[1]); pmax = int(sys.argv[2]); depth = int(sys.argv[3])
t0 = time.time(); ncompat = 0; nonper = []; tested = 0; periods = {}
for p in range(1, pmax + 1):
    for P in itertools.product((0, 1), repeat=p):
        if any(p % d == 0 and P == P[:d] * (p // d) for d in range(1, p)): continue
        tested += 1
        hs = surv(a, P, depth)
        if not hs: continue
        ncompat += 1
        periods[p] = periods.get(p, 0) + 1
        for h in hs:
            f = [h[2 * s + 1] for s in range(len(h) // 2)]
            tail = f[len(f) // 2:]
            per = next((q for q in range(1, 40) if all(tail[i] == tail[i + q] for i in range(len(tail) - q))), None)
            if per is None: nonper.append(''.join(map(str, P)))
    if time.time() - t0 > 50: print('time limit at period', p); break
print('a=%d, periods<=%d, depth %d: tested %d primitive tails; compatible: %d (by period: %s); compatible tails with non-eventually-periodic f: %s (%.1fs)' % (a, pmax, depth, tested, ncompat, periods, nonper[:10], time.time() - t0))
