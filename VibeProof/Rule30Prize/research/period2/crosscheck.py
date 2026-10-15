import itertools, random
exec(open('fiber2.py').read().split('random.seed(')[0])        # forced_left
exec(open('search2.py').read().split('maxd = int')[0])         # run, step
# 1) recurrence check: for random x satisfying the constraint, the anti-diagonal bit 0 equals forced-left cells
def anti_L(x, a, K):
    c = lambda t: (a + t) & 1
    Dkm1, Dk = 0, 0; out = []
    for k in range(K):
        Dn = step(Dkm1, Dk, k, x[k], c); out.append(Dn & 1); Dkm1, Dk = Dk, Dn
    return out
def col_L(x, a, K):
    c = [(a + t) % 2 for t in range(K + 2)]
    cur = [c[t + 1] ^ (c[t] | x[t]) for t in range(K)]; prev = c[:K + 1]; L = [cur[0]]
    for j in range(2, K + 1):
        nxt = [cur[t + 1] ^ (cur[t] | prev[t]) for t in range(len(cur) - 1)]
        prev, cur = cur, nxt
        if not cur: break
        L.append(cur[0])
    return L
random.seed(2); ok = True
for trial in range(200):
    a = random.getrandbits(1); K = 60
    x = []; 
    for t in range(K + 1):
        if t > 0 and x[-1] == 1: x.append(1 - ((a + t - 1) & 1))
        else: x.append(random.getrandbits(1))
    A = anti_L(x, a, K); C = col_L(x, a, K)
    if A[:len(C)] != C[:len(A)]: ok = False; print("MISMATCH", trial); break
print("anti-diagonal recurrence == column reconstruction on 200 random x:", ok)
# 2) explicit right halves: max over R of (first one of forced L beyond W) must be <= search death depth
for a in (0, 1):
    best = {}
    for n in range(1, 15):
        for bits in itertools.product((0, 1), repeat=n):
            if bits[-1] == 0: continue
            L = forced_left(list(bits), a, 70)
            for W in range(0, 25):
                k = next((i + 1 for i in range(W, len(L)) if L[i]), None)
                if k is not None: best[W] = max(best.get(W, 0), k)
    print(f"a={a}: max first-one-beyond-W over right halves of length <= 14:", [best[W] for W in range(0, 25)])
