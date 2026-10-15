# Elements of X that are eventually the stripe S: e finite (n), G(n) eventually all ones.
# For each, report the f sequence and whether f is eventually 1 (perturbation absorbed).
import sys
sys.path.insert(0, '.')
from t8 import step
def L_from_even(e, depth):
    Dkm1, Dk = 0, 0
    L = []; f = []
    for k in range(depth):
        if k % 2 == 0:
            Dn = step(Dkm1, Dk, k, 1)
        else:
            s = k // 2
            want = e[s] if s < len(e) else 0
            Dn = step(Dkm1, Dk, k, 0); yk = 0
            if (Dn & 1) != want:
                Dn = step(Dkm1, Dk, k, 1); yk = 1
            f.append(yk)
        L.append(Dn & 1)
        Dkm1, Dk = Dk, Dn
    return L, f
m = int(sys.argv[1]); D = int(sys.argv[2])
cnt = 0; notabs = 0
for n in range(1 << m):
    e = [(n >> i) & 1 for i in range(m)]
    L, f = L_from_even(e, D)
    odd = L[2::2]
    # eventually all ones in the odd positions over the second half?
    if all(odd[len(odd) // 2:]):
        cnt += 1
        # last zero in f
        lastz = max([i for i, b in enumerate(f) if b == 0], default=-1)
        lastodd0 = max([i for i, b in enumerate(odd) if b == 0], default=-1)
        if lastz > len(f) // 2: notabs += 1
        if cnt <= 40 or lastz > len(f) // 2:
            print('n=%d e=%s  L[:30]=%s  last odd-0 at %d  f[:40]=%s last f-zero at %d' % (n, ''.join(map(str, e)), ''.join(map(str, L[:30])), 2 * lastodd0 + 3, ''.join(map(str, f[:40])), lastz))
print('m=%d: %d of %d even-patterns give eventually-stripe L; with f not eventually 1 (within horizon): %d' % (m, cnt, 1 << m, notabs))
