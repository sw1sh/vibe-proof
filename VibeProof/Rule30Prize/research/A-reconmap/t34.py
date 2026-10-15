# For spatially periodic tails P (L(k) = P[k mod p] for k >= a), is there any f with that tail?
# BFS over anti-diagonal states (dedup); at even depths the pivot forces f; at odd depths it's a check.
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
seen = set()
rows = []
t0 = time.time()
for p in range(1, 5):
    for P in itertools.product((0, 1), repeat=p):
        # primitive words only, all phases (P indexed by k mod p)
        if any(p % d == 0 and P == P[:d] * (p // d) for d in range(1, p)): continue
        res = []
        for a in (10, 16, 22, 28):
            b, nst = tail_profile(a, P, 4 * a + 40)
            res.append((a, b if b else 'ALIVE(%d)' % nst))
        print('P=%s (P[k mod %d], k>=a):' % (''.join(map(str, P)), p), res, flush=True)
        if time.time() - t0 > 50: break
