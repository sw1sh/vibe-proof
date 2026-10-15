# Exact light-cone: values of (col1, col2, col3,...) at time n after driver block u, over all states of cols 1..n+m at time 0
import sys, numpy as np
def cone_cols(u, m):
    n = len(u); K = n + m
    s = np.arange(1 << K, dtype=np.uint64)
    for c in u:
        s = (((s << np.uint64(1)) | np.uint64(c)) ^ (s | (s >> np.uint64(1))))
    return [((s >> np.uint64(j)) & np.uint64(1)).astype(np.int8) for j in range(m)]
m = int(sys.argv[1])
for u in sys.argv[2:]:
    ub = [int(ch) for ch in u]
    cols = cone_cols(ub, m)
    desc = []
    for j, cj in enumerate(cols):
        v = sorted(set(cj.tolist()))
        desc.append(f"col{j+1}:{''.join(map(str,v))}")
    print(u, ' '.join(desc), flush=True)
