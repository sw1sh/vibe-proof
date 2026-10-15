import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen')
from rsim import true_rows, run, eventual_period
steps = int(sys.argv[1]); words = sys.argv[2].split(','); Ts = [int(x) for x in sys.argv[3].split(',')]
rows = {}
for t, rh, c in true_rows(max(Ts)):
    if t in Ts: rows[t] = rh
for w in words:
    out = []
    for T in Ts:
        cc, d, _ = run(w, rows[T], steps)
        e = bytes(a | b for a, b in zip(cc, d))
        pd = eventual_period(bytes(d), maxP=steps // 4); pe = eventual_period(e, maxP=64)
        # defect density of d w.r.t. period P at ONE-phases in second half
        P = len(w); h = steps // 2
        dd = sum(1 for s in range(h, steps) if d[s] != d[s - P]) / (steps - h)
        out.append(f"T{T}: d{pd} e{pe} dDefect{dd:.3f}")
    print(w, ' | '.join(out), flush=True)
