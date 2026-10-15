exec(open('search2_free.py').read().split('maxd = int')[0])
import time
for a in (0, 1):
    out = []; t0 = time.time()
    for W in range(0, 30):
        cnt = run(a, W, W + 80, cap=3_000_000)
        out.append((W, len(cnt) if cnt[-1] == 0 else ('alive', cnt[-1])))
        if time.time() - t0 > 25: break
    print(f"a={a}, x completely free: (W, death depth):", out)
