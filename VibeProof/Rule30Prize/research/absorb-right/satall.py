# SAT uniform absorption scan over a word list: find N0 with x(n,1)=x(n+Q,1) forced for n in [N0,N0+P), Q=2P.
import sys, time
sys.path.insert(0, '.')
from satper import forced_period
budget = float(sys.argv[1]); start = int(sys.argv[2]); count = int(sys.argv[3]); listfile = sys.argv[4]; outfile = sys.argv[5]
words = [l.strip() for l in open(listfile) if l.strip()][start:start + count]
t0 = time.time()
with open(outfile, 'a') as out:
    for w in words:
        if time.time() - t0 > budget: print("stopped before", w); break
        P = len(w); Q = 2 * P; nmax = 4 * P + 24
        run = 0; n = 0; N0 = None
        while n <= nmax:
            if forced_period(w, n, Q):
                run += 1
                if run == P: N0 = n - P + 1; break
            else: run = 0
            n += 1
        line = f"{w} Q={Q} N0={N0}"
        print(line, flush=True); out.write(line + "\n"); out.flush()
