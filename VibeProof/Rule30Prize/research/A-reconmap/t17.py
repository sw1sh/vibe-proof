# For e (even-depth values) with finite support, compute the odd-depth values G(e) via the anti-diagonal recursion.
import sys, random
sys.path.insert(0, '.')
from t8 import step
def L_from_even(e, depth):
    """e: list of even-depth values L(2), L(4), ... (padded with 0). Returns L(1..depth) and f."""
    Dkm1, Dk = 0, 0
    L = []; f = []
    for k in range(depth):
        if k % 2 == 0:
            yk = 1
            Dn = step(Dkm1, Dk, k, yk)
        else:
            s = k // 2
            want = e[s] if s < len(e) else 0
            Dn = step(Dkm1, Dk, k, 0)
            yk = 0
            if (Dn & 1) != want:
                Dn = step(Dkm1, Dk, k, 1); yk = 1
            f.append(yk)
        L.append(Dn & 1)
        Dkm1, Dk = Dk, Dn
    return L, f
random.seed(3)
for trial in range(12):
    m = random.randint(0, 12)
    e = [random.getrandbits(1) for _ in range(m)]
    L, f = L_from_even(e, 400)
    odd = L[2::2]   # L(3), L(5), ...
    print('e=', ''.join(map(str, e)).ljust(13), 'odd depths:', ''.join(map(str, odd[:100])), ' ones in odd[100:200]:', sum(odd[100:200]))
