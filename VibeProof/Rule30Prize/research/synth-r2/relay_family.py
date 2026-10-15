# Does progB-avoid's relay counterexample (0001 driver, phase 1, black at columns 4,7) enter
# B-edge-trap's ether+wall family InFamily (EtherWall.lean definitions, parsed from the Lean source)?
import re, sys
src = open(sys.argv[1]).read()
blk = src[src.index('def wallStates'):]
blk = blk[:blk.index(']\n\n')+1] if ']\n\n' in blk else blk
walls = set()
for ph, lst in re.findall(r'\((\d+),\s*\[([^\]]*)\]\)', blk):
    bits = tuple(1 if b.strip() == 'true' else 0 for b in lst.split(','))
    if len(bits) == 13: walls.add((int(ph), bits))
print("parsed wall states:", len(walls))
table = ['0011', '0110', '1101', '0101', '0011', '0001', '0001']
ether = lambda j, ph: int(table[j % 7][ph % 4])
rule = lambda l, c, r: l ^ (c | r)
def run(xblack, w, phi, T, W):
    c = lambda t: int(w[(t + phi) % 4])
    row = [c(0)] + [1 if p in xblack else 0 for p in range(1, W)]
    hist = [row]
    for t in range(T):
        r = hist[-1]
        new = [c(t + 1)] + [rule(r[p - 1], r[p], r[p + 1] if p + 1 < W else 0) for p in range(1, W)]
        hist.append(new)
    return hist
def in_family(row, j0, s, t1, kmax=80):
    for k in range(0, kmax):
        if (j0 + k) % 7 != 2: continue
        if all(row[p] == ether(j0 + p, t1 + s) for p in range(1, k + 1)):
            if ((t1 + s) % 4, tuple(row[k + 1:k + 14])) in walls: return k
    return None
w = '0001'; phi = 1; T = 1500; W = T + 40
hist = run({4, 7}, w, phi, T, W)
A = [(5, 0), (6, 0)]
first = None
for t1 in range(T - 200):
    for (j0, s) in A:
        k = in_family(hist[t1], j0, s + phi, t1)
        if k is not None:
            first = (t1, j0, k); break
    if first: break
print("relay config {4,7}, 0001, phase 1: first InFamily entry (t1, j0, k) =", first)
# sanity: a random-ish config enters with small k
hist2 = run({2, 3, 5}, w, 0, T, W)
for t1 in range(T - 200):
    hit = [(j0, in_family(hist2[t1], j0, s, t1)) for (j0, s) in A]
    hit = [h for h in hit if h[1] is not None]
    if hit: print("control config {2,3,5} phase 0 enters at t1 =", t1, "with (j0,k) =", hit[0]); break
