import sys, time, os
sys.path.insert(0, '.')
from ellabs import analyze, scc_test
# usage: ellrange2.py u rmin rmax budget outfile ; resumes from outfile
u = sys.argv[1]; rmin = int(sys.argv[2]); rmax = int(sys.argv[3]); budget = float(sys.argv[4]); outf = sys.argv[5]
done = set()
if os.path.exists(outf):
    for l in open(outf):
        p = l.split()
        if len(p) >= 3 and p[0] == u: done.add(int(p[1]))
t0 = time.time()
with open(outf, 'a') as f:
    for r in range(rmin, rmax + 1):
        if r in done: continue
        if time.time() - t0 > budget: break
        w = '0' * r + u; P = len(w); L = P + 12
        nodes = analyze(w, L)
        ok, report = scc_test(nodes)
        f.write(f"{u} {r} {'PASS' if ok else 'FAIL'}\n"); f.flush()
