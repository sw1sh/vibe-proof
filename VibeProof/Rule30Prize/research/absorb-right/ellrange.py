import sys, time
sys.path.insert(0, '.')
from ellabs import analyze, scc_test
u = sys.argv[1]; r0 = int(sys.argv[2]); r1 = int(sys.argv[3]); budget = float(sys.argv[4])
t0 = time.time()
for r in range(r0, r1 + 1):
    if time.time() - t0 > budget: print("stop at r =", r); break
    w = '0' * r + u; P = len(w); L = P + 12
    nodes = analyze(w, L)
    ok, report = scc_test(nodes)
    print(f"u={u} r={r}: {'PASS' if ok else 'FAIL'}  SCCs: " + '; '.join(f"{c[:4]}:{o}" for c, o in report), flush=True)
