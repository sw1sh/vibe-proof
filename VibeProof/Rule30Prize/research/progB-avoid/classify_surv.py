import sys
from collections import Counter, deque
sys.path.insert(0, '.')
from sim import *
import closure as C
w = sys.argv[1]; fn = sys.argv[2]; maxcases = int(sys.argv[3])
P = len(w)
res = Counter()
lines = open(fn).read().split('\n')
done = 0
for line in lines:
    if not line.startswith('SURV'): continue
    parts = line.split()
    cfg = parts[2]; ph0 = int(parts[4])
    x = 0
    for i, ch in enumerate(cfg):
        if ch == '1': x |= 1 << i
    hist = run(x, w, ph0, 6200)
    outs = [hist[t][1] & 1 for t in range(5000, 6200) if w[hist[t][0]] == '0']
    L = len(outs)
    m = next((d for d in range(1, L // 3) if all(outs[i] == outs[i + d] for i in range(L - d))), None)
    # time-periodic extent with period Q = lcm guess: try periods multiple of P up to 64
    ext = (0, None)
    for Q in range(P, 65, P):
        k = 0
        while k < 200:
            mask = (1 << (k + 1)) - 1
            if all((hist[t][1] & mask) == (hist[t + Q][1] & mask) for t in range(5000, 6200 - Q)): k += 1
            else: break
        if k > ext[0]: ext = (k, Q)
    # certified trap width
    cert = None
    for BW in range(max(ext[0], 16), min(ext[0] + 12, 40)):
        C.BW = BW
        start = (hist[6000][0], hist[6000][1] & ((1 << BW) - 1))
        cl = C.closure(w, BW, start, limit=150000)
        if cl is None: continue
        outword = outs[:m] if m else None
        # recompute output word aligned at t=6000
        o2 = [hist[t][1] & 1 for t in range(6000, 6200) if w[hist[t][0]] == '0']
        mm = next((d for d in range(1, len(o2) // 3) if all(o2[i] == o2[i + d] for i in range(len(o2) - d))), None)
        if mm is None: break
        if C.consistent(w, cl, start, o2[:mm]):
            cert = (BW, len(cl)); break
    key = (m, ext, cert)
    res[(m, ext[0], ext[1], cert)] += 1
    done += 1
    if done >= maxcases: break
for k, v in sorted(res.items(), key=lambda kv: -kv[1]):
    print(f"output period {k[0]}, periodic columns 1..{k[1]} (time period {k[2]}), certified trap (width, size) {k[3]}: {v} cases")
