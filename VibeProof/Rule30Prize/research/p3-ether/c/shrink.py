# Try smaller widths: closures (all inputs) of the projections of the t001 states to width bb, with a cap.
import sys
from collections import deque
w = "001"; P = 3
rows = [tuple(map(int, l.split())) for l in open(sys.argv[1]).read().split('\n')[1:] if l.strip()]
cap = int(sys.argv[2])
for bb in range(46, 37, -1):
    MASK = (1 << bb) - 1
    def stp(a, z, r):
        full = a | (r << 1) | (z << (bb + 1))
        return (full ^ ((full >> 1) | (full >> 2))) & MASK
    seeds = sorted(set(((r & MASK), l) for (r, l) in rows))
    best = None; tried = 0
    for (r0, l0) in seeds[:40]:
        tried += 1
        seen = {(r0, l0 % 3)}; dq = deque([(r0, l0 % 3)]); over = False
        while dq:
            r, ph = dq.popleft()
            for z in (0, 1):
                v = (stp(int(w[ph]), z, r), (ph + 1) % 3)
                if v not in seen:
                    seen.add(v); dq.append(v)
                    if len(seen) > cap: over = True; break
            if over: break
        if not over and (best is None or len(seen) < best): best = len(seen)
    print(f"width {bb}: tried {tried} projected seeds; smallest closure {'> cap' if best is None else best} (cap {cap})")
