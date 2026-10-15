# Search for GF(2)-linear (wall-relative or edge-relative) functionals L with L(G x) = L(x) (+const)
# over all finite constrained configs x (support <= W) with x(1)=1 and G x (two steps) also constrained.
def step(x): return (x >> 1) ^ (x | (x << 1))
import sys
W = int(sys.argv[1]); N = W + 6  # positions considered
rows = []
for x in range(1, 1 << W):
    if not (x & 1): continue
    y = step(step(x))
    if not (y & 1): continue
    rows.append((x, y))
def solve(vecs, nvars):
    # find nullspace of the matrix whose rows are vecs (as ints over nvars bits)
    piv = {}
    for v in vecs:
        for p in sorted(piv, reverse=True):
            if (v >> p) & 1: v ^= piv[p]
        if v: piv[v.bit_length() - 1] = v
    return nvars - len(piv)
# wall-relative: L(x) = sum_{k<N} c_k x(k); condition L(x) ^ L(y) ^ c = 0 -> vector over N+1 vars (last = const)
vecs = []
for x, y in rows:
    d = (x ^ y) & ((1 << N) - 1)
    vecs.append(d | (1 << N))
print("pairs:", len(rows), " wall-relative affine invariants (nullity incl. trivial):", solve(vecs, N + 1))
# edge-relative: positions measured from the leftmost black cell; G moves the edge by +2
vecs = []
for x, y in rows:
    ex = x.bit_length() - 1; ey = y.bit_length() - 1
    vx = 0; vy = 0
    for j in range(N):
        if ex - j >= 0 and (x >> (ex - j)) & 1: vx |= 1 << j
        if ey - j >= 0 and (y >> (ey - j)) & 1: vy |= 1 << j
    vecs.append((vx ^ vy) | (1 << N))
print(" edge-relative affine invariants (nullity):", solve(vecs, N + 1))
