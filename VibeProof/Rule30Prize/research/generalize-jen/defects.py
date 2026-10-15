# Defect structure of e = c OR d (w.r.t. period P) for the right half driven by w^inf from the true state at time T.
# Report: defect density in the last half, number of defects, last defect, max gap ratio s_{k+1}/(s_k+1) over defects s_k >= 100.
import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen')
from rsim import true_rows, run
steps = int(sys.argv[1]); words = sys.argv[2].split(','); Ts = [int(x) for x in sys.argv[3].split(',')]
rows = {}
for t, rh, c in true_rows(max(Ts)):
    if t in Ts: rows[t] = rh
for w in words:
    P = len(w)
    for T in Ts:
        for ph in range(P):
            ww = w[ph:] + w[:ph]
            cc, d, _ = run(ww, rows[T], steps)
            D = [s for s in range(P, steps) if cc[s] == 0 and d[s] != d[s - P]]
            h = steps // 2
            dens = sum(1 for s in D if s >= h) / (steps - h)
            ratio = 0.0
            for a, b in zip(D, D[1:]):
                if a >= 100: ratio = max(ratio, b / (a + 1))
            last = D[-1] if D else None
            print(f"{w} T{T} ph{ph}: #def {len(D)} dens(2nd half) {dens:.3f} last {last} maxratio {ratio:.3f}", flush=True)
