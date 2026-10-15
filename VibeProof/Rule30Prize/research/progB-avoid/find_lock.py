import sys, random
sys.path.insert(0, '.')
from sim import *
w = sys.argv[1]; n = int(sys.argv[2]); seed = int(sys.argv[3]); b = int(sys.argv[4])
random.seed(seed)
P = len(w)
found = 0
for trial in range(400):
    x = random.getrandbits(n) | (1 << (n - 1)); ph = random.randrange(P)
    hist = run(x, w, ph, 3000)
    strips = [(h[0], h[1] & ((1 << b) - 1)) for h in hist]
    # period of strip over last 1000
    per = next((d for d in range(1, 300) if all(strips[t] == strips[t + d] for t in range(2000, 3000 - d))), None)
    if per is not None and per > 4:
        found += 1
        print("trial", trial, "strip period", per, "initial", bin(x), "phase", ph)
        # determine the extent of the periodic region: largest k with columns 1..k periodic with period per over last 1000
        k = 0
        while k < 200:
            mask = (1 << (k + 1)) - 1
            if all((hist[t][1] & mask) == (hist[t + per][1] & mask) for t in range(2000, 3000 - per)): k += 1
            else: break
        print("  columns 1..%d periodic with period %d over t in [2000,3000)" % (k, per))
        for t in range(2960, 2990):
            print("  ", hist[t][0], w[hist[t][0]], cols(hist[t][1], 1, 70))
        if found >= 2: break
