import sys, time
sys.path.insert(0, '.')
from satper import forced_period
# args: nmax, then word:Q pairs
nmax = int(sys.argv[1]); budget = float(sys.argv[2])
t_start = time.time()
for arg in sys.argv[3:]:
    w, Q = arg.split(':'); Q = int(Q); P = len(w)
    run = 0; n = 0; N0 = None; lastfail = None
    while n <= nmax and time.time() - t_start < budget:
        if forced_period(w, n, Q):
            run += 1
            if run == P: N0 = n - P + 1; break
        else:
            run = 0; lastfail = n
        n += 1
    print(f"{w} Q={Q}: N0={N0} (scanned to n={n}, last non-forced n={lastfail})", flush=True)
