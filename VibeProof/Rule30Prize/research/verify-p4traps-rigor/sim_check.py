# Sanity check of the state convention: run the driven right half
# with column 0 at time t equal to w[t mod P]; record first time the strip (cols 1..b) is in S_w at
# phase t mod P, then confirm it stays there and column 1 at white times follows u.
import sys, random
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-p4traps-rigor')
fn, u, seeds, steps = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
with open(fn) as f:
    lines = [ln for ln in f.read().split('\n') if ln.strip()]
w, b, n = lines[0].split(); b = int(b); P = len(w); m = len(u)
S = {}
for ln in lines[1:]:
    ph, s, pos = map(int, ln.split()); S[(ph, s)] = pos
def r30(l, c, r): return (30 >> (4*l + 2*c + r)) & 1
entered = []
for seed in range(seeds):
    rnd = random.Random(seed)
    L = 200 + steps + 5
    row = [0] * (L + 2)       # row[p] = cell at column p, p = 0..L+1
    for p in range(1, 200): row[p] = rnd.getrandbits(1)
    first = None; viol = 0
    for t in range(steps):
        ph = t % P
        row[0] = int(w[ph])
        st = sum(row[p] << (p - 1) for p in range(1, b + 1))
        if (ph, st) in S:
            if first is None: first = t
            if w[ph] == '0' and row[1] != int(u[S[(ph, st)] % m]): viol += 1
        elif first is not None:
            viol += 1
        new = [0] * (L + 2)
        for p in range(1, L + 1):
            new[p] = r30(row[p - 1], row[p], row[p + 1])
        row = new
    entered.append((seed, first, viol))
print(fn.split('/')[-1], 'u=', u, [(s, f, v) for (s, f, v) in entered])
