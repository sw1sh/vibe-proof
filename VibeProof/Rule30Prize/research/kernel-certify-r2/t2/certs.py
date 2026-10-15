# Class table and cycle checkpoints for the stripe-prefix family, K = 32, S = 31.
K = 32; MASK = (1 << K) - 1; SEG = 16384
def fstep(W, fp):
    s1 = 1 - fp; s2 = fp
    return (W ^ (((W << 1) | s1) | ((W << 2) | (s1 << 1) | s2))) & MASK
def stripe(k): return k % 2 == 1
def vget(b, i): return b[i] if 0 <= i < 3 else False
classes = {}
for q in range(2):
    for vb in range(8):
        b = [bool((vb >> i) & 1) for i in range(3)]
        delta = next(j for j in range(1, 6) if vget(b, j - 1) != stripe(q + j))
        W0 = sum(1 << i for i in range(K) if vget(b, delta - 1 + i))
        p0 = (q + delta) % 2
        classes[(q, vb)] = (delta, W0, p0)
cyc = {}
for (q, vb), (delta, W0, p0) in classes.items():
    if (W0, p0) in cyc: continue
    W, p = W0, p0; lam = 0; pts = [(0, W, p)]
    while True:
        W = fstep(W, p); p = 1 - p; lam += 1
        if lam % SEG == 0: pts.append((lam, W, p))
        if (W, p) == (W0, p0): break
    if pts[-1][0] != lam: pts.append((lam, W, p))
    cyc[(W0, p0)] = (lam, pts)
for k, v in sorted(classes.items()): print('class', k, v, 'lam', cyc[(v[1], v[2])][0])
for k, (lam, pts) in sorted(cyc.items()): print('cycle', k, lam, pts)
