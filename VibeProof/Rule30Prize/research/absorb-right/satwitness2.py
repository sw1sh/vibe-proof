# Get SAT witness and print spacetime diagram rows t0..t1
import sys, subprocess, os, tempfile
sys.path.insert(0, '.')
from satper import cone_cnf, CADICAL
w = sys.argv[1]; Q = int(sys.argv[2]); n = int(sys.argv[3]); t0 = int(sys.argv[4]); t1 = int(sys.argv[5]); ncols = int(sys.argv[6])
cnt, clauses, v = cone_cnf(w, n + Q, 1, 0)
a = v(n, 1); b = v(n + Q, 1)
with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
    f.write(f"p cnf {cnt[0]} {len(clauses) + 2}\n")
    for cl in clauses: f.write(' '.join(map(str, cl)) + ' 0\n')
    f.write(f"{a} {b} 0\n{-a} {-b} 0\n"); fn = f.name
r = subprocess.run([CADICAL, '-q', fn], capture_output=True, text=True); os.unlink(fn)
vals = {}
for line in r.stdout.splitlines():
    if line.startswith('v'):
        for tok in line.split()[1:]:
            k = int(tok)
            if k != 0: vals[abs(k)] = k > 0
X = 0; W = n + Q + 1
for p in range(1, W + 1):
    if vals.get(v(0, p), False): X |= 1 << (p - 1)
wb = [int(ch) for ch in w]; P = len(wb); row = X
for t in range(t1):
    if t >= t0:
        print(f"{t:5d} {t%P} {'#' if wb[t%P] else '.'}|" + ''.join('#' if (row >> i) & 1 else '.' for i in range(ncols)))
    row = ((row << 1) | wb[t % P]) ^ (row | (row >> 1))
