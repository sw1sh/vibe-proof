# BFS over anti-diagonal states for the window question: can L be zero on [a, b]?
# State at depth k (after computing D_k): (D_{k-1}, D_k) as ints, bit j of D_k = u_j(k-j), j=0..k-1.
import sys, time
def suffix_xor(g, width):
    s = g; sh = 1
    while sh < width:
        s ^= s >> sh; sh <<= 1
    return s
def step(Dkm1, Dk, k, yk):
    # D_{k+1}[k] = y_k ; D_{k+1}[j] = D_{k+1}[j+1] ^ (D_k[j] | D_{k-1}[j])  for j = k-1..0
    g = (Dk | Dkm1) & ((1 << k) - 1)
    S = suffix_xor(g, k) if k > 0 else 0       # S[j] = xor_{i >= j} g[i]
    low = S ^ (((1 << k) - 1) if yk else 0)
    return (yk << k) | low
def window_profile(a, bmax, cap=4_000_000):
    states = {(0, 0)}
    prof = []
    for k in range(0, bmax):
        # compute D_{k+1}, i.e. L(k+1) = bit 0
        new = set()
        if k % 2 == 0:
            ys = (1,)
        else:
            ys = (0, 1)
        for (Dkm1, Dk) in states:
            for yk in ys:
                Dn = step(Dkm1, Dk, k, yk)
                if k + 1 >= a and (Dn & 1): continue
                new.add((Dk, Dn))
        states = new
        prof.append(len(states))
        if not states: return k + 1, prof
        if len(states) > cap: return None, prof
    return None, prof
if __name__ == '__main__':
    amax = int(sys.argv[1])
    t0 = time.time()
    for a in range(1, amax + 1):
        b, prof = window_profile(a, 4 * a + 40)
        print(a, b, (b - a + 1) if b else None, prof[a - 2:] if a >= 2 else prof, round(time.time() - t0, 1), flush=True)
        if time.time() - t0 > 50: break
