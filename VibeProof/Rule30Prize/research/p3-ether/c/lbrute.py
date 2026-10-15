# Independent brute force: every left start of width <= W (L(1..W) arbitrary), driven by the periodic
# boundary E (phase ph0 at t = 0), run forward; first time t where column -1 violates K.  Max over starts.
import sys
E, K, ph0, W = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]); P = len(E)
T = 6 * W + 40
best = 0
for L in range(1 << W):
    # row: bit (i-1) = depth i ; depth 0 is the boundary
    row = L; t = 0
    while True:
        ph = (ph0 + t) % P
        x1 = row & 1
        if K[ph] != '*' and x1 != int(K[ph]): break
        c = int(E[ph])
        # new depth i = depth(i+1) xor (depth i or depth(i-1)); depth 0 = c
        full = (row << 1) | c          # bit i = depth i
        new = ((full >> 2) ^ ((full >> 1) | full))   # bit (i-1): depth i+1 xor (depth i or depth i-1)
        row = new & ((1 << (W + t + 2)) - 1)
        t += 1
        if t > T: print("horizon exceeded"); sys.exit(1)
    best = max(best, t)
print(f"E={E} K={K} ph0={ph0} W={W}: brute max survival {best}")
