import sys, random
sys.path.insert(0, '.')
from core import *
# sanity 1: forward evolution of L(f) reproduces y on the determined range
random.seed(1)
ok = True
for trial in range(300):
    m = random.randint(1, 30)
    f = [random.getrandbits(1) for _ in range(m)]
    L = L_of_f(f)
    y = y_of_f(f)
    rows = forward(L, len(y))
    for t in range(len(y)):
        # u_t(1) depends on L(1..t+1); L known for k <= len(y) so u_t(1) valid for t+1 <= len(y)
        if rows[t][0] != y[t]:
            ok = False; print('mismatch', f, t); break
    if not ok: break
print('forward(recon) == y:', ok)
# sanity 2: triangularity
for m in range(1, 12):
    ALL, F, L = L_sliced(m)
    # L(2s+2) = f_s xor g(f_<s): check that flipping f_s flips L(2s+2) everywhere
    for s in range(m):
        Lk = L[2 * s + 1]
        # flipping f_s: swap halves at block 1<<s
        blk = 1 << s
        M = ALL ^ F[s]
        flipped = ((Lk >> blk) & M) | ((Lk & M) << blk)
        assert flipped ^ Lk == ALL, (m, s)
        # L(k) for k <= 2s+1 independent of f_s
        for k in range(1, 2 * s + 2):
            Lk2 = L[k - 1]
            fl = ((Lk2 >> blk) & M) | ((Lk2 & M) << blk)
            assert fl == Lk2, (m, s, k)
print('triangularity verified m <= 11')
print('L(1)=1:', L[0] == ALL, ' L(2)+L(3)=1:', L[1] ^ L[2] == ALL)
