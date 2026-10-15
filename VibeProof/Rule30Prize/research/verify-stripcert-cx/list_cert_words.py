import sys, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-stripcert-cx')
from scc_semantic import analyze
from broad_test import necklaces
Lmin, Lmax, bmax, budget = map(int, sys.argv[1:5])
t0 = time.time(); found = []
for L in range(Lmin, Lmax + 1):
    for w in necklaces(L):
        for b in range(1, bmax + 1):
            ok, summ, nc = analyze(w, b)
            if ok: found.append((w, b)); break
        if time.time() - t0 > budget: print('budget hit', L); break
print(found)
