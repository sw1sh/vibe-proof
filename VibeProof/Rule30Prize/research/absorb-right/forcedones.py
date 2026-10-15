# After K steps of constant-1 driving (column m = 1 for K steps), which cells x(K, m+i) are forced?
import sys
sys.path.insert(0, '.')
from satper import cone_cnf, CADICAL
import subprocess, os, tempfile
def sat(nv, clauses, extra):
    with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
        f.write(f"p cnf {nv} {len(clauses)+len(extra)}\n")
        for cl in clauses + extra: f.write(' '.join(map(str, cl)) + ' 0\n')
        fn = f.name
    r = subprocess.run([CADICAL, '-q', fn], capture_output=True, text=True); os.unlink(fn)
    return r.returncode == 10
maxi = int(sys.argv[1])
for K in [int(x) for x in sys.argv[2].split(',')]:
    cnt, clauses, v = cone_cnf('1', K, maxi, 0)
    s = ''
    for i in range(1, maxi + 1):
        x = v(K, i)
        c0 = sat(cnt[0], clauses, [[-x]]); c1 = sat(cnt[0], clauses, [[x]])
        s += '*' if (c0 and c1) else ('0' if c0 else '1')
    print(f"K={K:3d}: x(K, m+1..m+{maxi}) = {s}", flush=True)
