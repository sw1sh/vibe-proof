import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen')
from rsim import true_rows, run, eventual_period
steps = int(sys.argv[1]); ks = [int(x) for x in sys.argv[2].split(',')]
Ts = [int(x) for x in sys.argv[3].split(',')]
rows = {}
for t, rh, c in true_rows(max(Ts)):
    if t in Ts: rows[t] = rh
for k in ks:
    w = '0' + '1'*k
    for T in Ts:
        out = []
        for ph in range(len(w)):
            ww = w[ph:] + w[:ph]
            cc, d, col2 = run(ww, rows[T], steps)
            e = bytes(a | b for a, b in zip(cc, d))
            pd = eventual_period(bytes(d), maxP=steps//4); pe = eventual_period(e, maxP=steps//4)
            out.append(f"{pd}/{pe}")
        print(w, T, ' '.join(out), flush=True)
