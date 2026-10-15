# Exact light-cone forcing: col1 at time n after driver block u (length n) as a function of cols 1..n+1 at time 0.
# Vectorized over all 2^(n+1) initial states with numpy (bit i <-> col i+1). Also reports col2 values.
import sys, numpy as np
def cone(u):
    n = len(u); K = n + 1
    s = np.arange(1 << K, dtype=np.uint64)
    for c in u:
        s = (((s << np.uint64(1)) | np.uint64(c)) ^ (s | (s >> np.uint64(1))))
        # bits beyond the cone become garbage, but col1/col2 at the end only need the cone
    col1 = (s & np.uint64(1)).astype(np.int8)
    col2 = ((s >> np.uint64(1)) & np.uint64(1)).astype(np.int8)
    return col1, col2
for u in sys.argv[1:]:
    ub = [int(ch) for ch in u]
    if len(ub) > 25: print(u, 'too long'); continue
    c1, c2 = cone(ub)
    v1 = sorted(set(c1.tolist())); 
    # col2 at time n depends on cols up to n+2: not fully determined by K=n+1 bits; report col1 only
    print(u, 'n=', len(ub), 'col1 values', v1, 'count1', int(c1.sum()), 'of', len(c1), flush=True)
