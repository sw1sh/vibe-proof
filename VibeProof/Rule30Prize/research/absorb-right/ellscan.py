import sys, time
sys.path.insert(0, '.')
from ellabs import analyze, scc_test
budget = float(sys.argv[1]); words = sys.argv[2:]
t0 = time.time()
for w in words:
    if time.time() - t0 > budget: print(w, "SKIPPED (budget)"); continue
    P = len(w); L = 2 * P + 6
    nodes = analyze(w, L)
    ok, report = scc_test(nodes)
    multi = [c for c in nodes if len(nodes[c][0]) > 1]
    print(f"{w}: {'PASS' if ok else 'FAIL'} L={L} multi-output classes={multi} SCCs=" +
          '; '.join(f"{comp if len(comp) < 6 else str(comp[:5])+'...'}:{outs if len(outs) < 4 else str(len(outs))+' outs'}" for comp, outs in report), flush=True)
