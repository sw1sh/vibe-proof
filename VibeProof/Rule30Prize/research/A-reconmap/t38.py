# For the compatible period-7 tails, extract the surviving free-bit sequences and test eventual periodicity.
import sys
sys.path.insert(0, '.')
from t8 import step
def survivors(a, P, depth):
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
    return list(states.values())
for Ps in ['0010000', '0100010', '0111000', '1001100', '1100111', '1101111', '1110000', '1110111', '01', '10']:
    P = [int(c) for c in Ps]
    for h in survivors(20, P, 240):
        f = [h[2 * s + 1] for s in range(len(h) // 2)]
        tail = f[40:]
        per = next((q for q in range(1, 20) if all(tail[i] == tail[i + q] for i in range(len(tail) - q))), None)
        print('P=%s: f[:24]=%s  tail period of f (from s=40): %s  f[40:52]=%s' % (Ps, ''.join(map(str, f[:24])), per, ''.join(map(str, tail[:12]))))
