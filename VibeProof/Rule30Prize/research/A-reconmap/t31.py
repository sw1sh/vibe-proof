import sys, time
sys.path.insert(0, '.')
from t8 import window_profile
for a in (42, 44, 46):
    t0 = time.time()
    b, prof = window_profile(a, 4 * a + 40, cap=10_000_000)
    print('python BFS: a=%d B(a)=%s states at depth a-1: %d (%.1fs)' % (a, b, prof[a - 2], time.time() - t0), flush=True)
