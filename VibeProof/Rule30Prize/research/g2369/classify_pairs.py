# For each frozen-boundary step g and each cycle of g on Z/2^K, is some consecutive diagonal pair
# (bits k, k+1 along the orbit) equal, as a periodic sequence up to rotation, to a diagonal pair of
# some Phi-orbit (finite seed) at some depth j?  Then that g-orbit's readouts reduce to FinConf.
import itertools, time
t0 = time.time()
def Phi(x): return x ^ ((2 * x) | (4 * x))
def bdry(al, be, ga, y): return y ^ (al + 2 * (be if y % 2 == 0 else ga))
def canon(seq):
    n = len(seq)
    for p in range(1, n + 1):                       # minimal period
        if n % p == 0 and all(seq[i] == seq[i % p] for i in range(n)):
            w = seq[:p]; break
    return min(w[i:] + w[:i] for i in range(len(w)))
def cycles(f, M):
    seen, cyc = set(), []
    for v in range(M):
        if v in seen: continue
        c, x = [], v
        while x not in seen:
            seen.add(x); c.append(x); x = f(x)
        if x == v: cyc.append(c)
    return cyc
JPHI = 13
phi_pairs = set()
MP = 1 << (JPHI + 2)
for c in cycles(lambda x: Phi(x) % MP, MP):
    for j in range(0, JPHI + 1):
        phi_pairs.add(canon(tuple(((x >> j) & 1, (x >> (j + 1)) & 1) for x in c)))
print('Phi pairs collected:', len(phi_pairs), f'{time.time()-t0:.1f}s')
K = 10
for al, be, ga in itertools.product((0, 1), repeat=3):
    M = 1 << K
    cs = cycles(lambda x: bdry(al, be, ga, Phi(x)) % M, M)
    depth_hist, unreal = {}, 0
    for c in cs:
        hit = None
        for k in range(0, K - 1):
            if canon(tuple(((x >> k) & 1, (x >> (k + 1)) & 1) for x in c)) in phi_pairs:
                hit = k; break
        if hit is None: unreal += 1
        else: depth_hist[hit] = depth_hist.get(hit, 0) + len(c)
    print(f'step ({al},{be},{ga}): cycles mod 2^{K}: {len(cs)}, residues by first realizable depth:',
          dict(sorted(depth_hist.items())), ' cycles with no realizable pair:', unreal)
print(f'{time.time()-t0:.1f}s')
