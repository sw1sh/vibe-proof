# Get a witness configuration X for "x(n,1) != x(n+Q,1)" and simulate it long.
import sys, subprocess, os, tempfile
sys.path.insert(0, '.')
from satper import cone_cnf, CADICAL
from sim import run
w = sys.argv[1]; Q = int(sys.argv[2]); n = int(sys.argv[3]); N = int(sys.argv[4])
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
print("witness X (cols 1..%d):" % W, ''.join('1' if (X >> i) & 1 else '0' for i in range(W)))
col, _ = run(w, 0, X, N)
# check the witness property
print("x(n,1), x(n+Q,1) =", col[n], col[n + Q])
# find last violation of period Q
last = max([t for t in range(N - Q) if col[t] != col[t + Q]] or [-1])
print("last t with col[t] != col[t+Q]:", last, " (N=%d)" % N)
s = ''.join(str(x) for x in col[:min(N, 400)])
for i in range(0, len(s), 80): print(f"{i:4d} {s[i:i+80]}")
