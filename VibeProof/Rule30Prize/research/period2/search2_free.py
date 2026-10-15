# Search for column-1 sequences x such that, with an alternating center trace c(t) = (a+t)%2, the
# left-permutive reconstruction gives a left half L with cell(0,-k) = 0 for all k > W.
# Anti-diagonals: D_k(j) = cell(j, -(k-j)), j = 0..k-1; bit j of an int.
# Right-half constraint on x: x(t) = 1  =>  x(t+1) = 1 - c(t).
import sys
def suffix_xor(g, width):
    s = g; sh = 1
    while sh < width:
        s ^= s >> sh; sh <<= 1
    return s
def step(Dkm1, Dk, k, xk, c):
    # returns D_{k+1}
    e1 = c(k + 1) ^ (c(k) | xk)
    if k == 0:
        return e1
    e2 = e1 ^ (((Dk >> (k - 1)) & 1) | c(k - 1))
    width = k - 1
    if width > 0:
        g = (Dk | Dkm1) & ((1 << width) - 1)
        S = suffix_xor(g, width)
        low = S ^ (((1 << width) - 1) if e2 else 0)
    else:
        low = 0
    return (e1 << k) | (e2 << (k - 1)) | low
def run(a, W, maxdepth, cap=200000):
    c = lambda t: (a + t) & 1
    # state: (Dkm1, Dk, last x) at depth k (D_k computed, depth k cells known)
    states = {(0, 0, None)}
    counts = []
    for k in range(0, maxdepth):
        new = set()
        for (Dkm1, Dk, xl) in states:
            for xk in (0, 1):
                pass
                Dn = step(Dkm1, Dk, k, xk, c)
                if k + 1 > W and (Dn & 1): continue        # cell(0, -(k+1)) must be 0
                new.add((Dk, Dn, xk))
        states = new
        counts.append(len(states))
        if not states or len(states) > cap: break
    return counts
maxd = int(sys.argv[1]) if len(sys.argv) > 1 else 60
for a in (0, 1):
    for W in range(0, 13):
        cnt = run(a, W, maxd)
        print(f"a={a} W={W:2d}: survivors by depth (last 8 of {len(cnt)}): {cnt[-8:]}")
