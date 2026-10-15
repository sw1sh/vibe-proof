# Rigidity table: assume c(T+j) = w[j mod P] for j >= 0. Constraint A fixes col_{-1}(t) = !c(t+1) when c(t)=1;
# other col_{-1} values are free variables. Optionally constraint B (column-1 rule) prunes assignments.
# Compute columns -m by left-permutivity and print, for each column and time offset, the forced value or '*'.
import itertools, sys, random
w = sys.argv[1]; P = len(w); cw = [int(ch) for ch in w]
K = int(sys.argv[2])          # number of periods of free variables
M = int(sys.argv[3])          # columns to show
useB = int(sys.argv[4]) if len(sys.argv) > 4 else 1
samples = int(sys.argv[5]) if len(sys.argv) > 5 else 0
J = P * K
c = [cw[j % P] for j in range(J + 1)]
free = [j for j in range(J) if c[j] == 0]
def checkB(y):
    prev = None
    for t in range(J):
        if c[t] == 0:
            v = c[t+1] ^ y[t]
            if prev == 1 and v != (1 - c[t-1]): return False
        else:
            v = (1 - c[t-1]) if prev == 1 else 0
        prev = v
    return True
vals = {}
def process(y):
    cols = {0: c[:J], 1: y}
    for m in range(1, M):
        a, b = cols[m], cols[m-1]
        cols[m+1] = [a[j+1] ^ (a[j] | b[j]) for j in range(len(a)-1)]
    for m in range(1, M+1):
        for j in range(len(cols[m])):
            vals.setdefault((m, j), set()).add(cols[m][j])
count = 0
it = itertools.product((0,1), repeat=len(free)) if samples == 0 else (tuple(random.getrandbits(1) for _ in free) for _ in range(samples))
for bits in it:
    y = [0]*J
    for j in range(J):
        if c[j] == 1: y[j] = 1 - c[j+1]
    for f, b in zip(free, bits): y[f] = b
    if useB and not checkB(y): continue
    count += 1
    process(y)
print(f"w={w} assignments={count}")
show = min(J - M, 4 * P)
for m in range(1, M+1):
    row = []
    for j in range(show):
        v = vals.get((m, j))
        row.append('?' if v is None else (str(next(iter(v))) if len(v) == 1 else '*'))
        if (j+1) % P == 0: row.append(' ')
    print(f"col -{m:2d}: " + ''.join(row))
