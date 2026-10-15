import sys
sys.path.insert(0, '.')
from sim import run
import closure as C
w = '0001'
for fn in sys.argv[1:]:
    ph0, cfg = open(fn).read().split()
    ph0 = int(ph0)
    x = sum(1 << i for i, ch in enumerate(cfg) if ch == '1')
    T = 2600
    hist = run(x, w, ph0, T + 300)
    # find first checkpoint where a consistent closure exists (widths 16..32)
    res = None
    for t in range(0, T, 25):
        o2 = [hist[u][1] & 1 for u in range(t, t + 300) if w[hist[u][0]] == '0']
        mm = next((d for d in range(1, len(o2) // 3) if all(o2[i] == o2[i + d] for i in range(len(o2) - d))), None)
        if mm is None: continue
        for BW in (16, 20, 24, 28, 32):
            C.BW = BW
            start = (hist[t][0], hist[t][1] & ((1 << BW) - 1))
            cl = C.closure(w, BW, start, limit=8000)
            if cl is not None and C.consistent(w, cl, start, o2[:mm]):
                res = (t, BW, len(cl), mm); break
        if res: break
    # output periodicity over windows
    outs = [hist[u][1] & 1 for u in range(0, T) if w[hist[u][0]] == '0']
    def per(seq):
        return next((d for d in range(1, len(seq) // 3) if all(seq[i] == seq[i + d] for i in range(len(seq) - d))), None)
    print(fn, "support", len(cfg), "certified absorbed (t, width, closure, outperiod):", res,
          "| output period on [0,500):", per(outs[:375]), "on [500,1000):", per(outs[375:750]), "on [1000,2000):", per(outs[750:1500]))
