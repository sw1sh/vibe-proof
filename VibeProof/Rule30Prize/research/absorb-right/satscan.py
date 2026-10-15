import sys, time
sys.path.insert(0, '.')
from satper import forced_period
w = sys.argv[1]; Q = int(sys.argv[2]); ns = [int(x) for x in sys.argv[3].split(',')]
for n in ns:
    t0 = time.time(); r = forced_period(w, n, Q); print(w, Q, n, "forced" if r else "not forced", "%.2fs" % (time.time() - t0), flush=True)
