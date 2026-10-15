# Theorem B check: for random drivers c and T, the map {edge-structured states at time T} -> x(T..2T-2)
# is a bijection onto {0,1}^(T-1); also x(T+k) depends only on cells -1..-(k+1) and is xor-linear in cell -(k+1).
import random
def xseq(state, T, c, n):
    row = state; out = []
    for t in range(T, T + n):
        out.append(row & 1)
        W = t + 1; mask = (1 << W) - 1
        right = ((row << 1) | c(t)) & mask; left = row >> 1
        row = (left ^ (row | right)) & mask
    return tuple(out)
random.seed(1)
ok = True
for trial in range(40):
    T = random.randint(2, 11)
    bits = [random.randint(0, 1) for _ in range(4 * T + 10)]
    c = lambda t, bits=bits: bits[t - T] if t >= T else 0
    imgs = set()
    for s in range(1 << (T - 1)):
        st = s | (1 << (T - 1))
        imgs.add(xseq(st, T, c, T - 1))
    if len(imgs) != (1 << (T - 1)): ok = False; print("not bijective", T)
    # permutivity: flipping cell -(k+1) flips x(T+k) and leaves x(T..T+k-1) unchanged
    for _ in range(20):
        st = random.getrandbits(T) | (1 << (T - 1)); k = random.randint(0, T - 2)
        a = xseq(st, T, c, k + 1); b = xseq(st ^ (1 << k), T, c, k + 1)
        if a[:k] != b[:k] or a[k] == b[k]: ok = False; print("permutivity fails", T, k)
print("Theorem B numerical check:", ok)
