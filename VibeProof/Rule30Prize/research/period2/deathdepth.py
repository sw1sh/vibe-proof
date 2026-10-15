import sys
src = open('search2.py').read().split('maxd = int')[0]
exec(src)
import time
for a in (0, 1):
    out = []
    t0 = time.time()
    for W in range(0, 40):
        cnt = run(a, W, W + 60, cap=2_000_000)
        dead = (cnt[-1] == 0)
        out.append((W, len(cnt) if dead else None, max(cnt)))
        if time.time() - t0 > 25: break
    print(f"a={a}: (W, death depth, max survivors):", out)
    print(f"   death depth - W:", [d - W for (W, d, m) in out if d is not None])
