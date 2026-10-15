# First time the center trace of delta_0 + delta_k differs from that of delta_0 (k > 0), and where
# the left front of the difference pattern is over time.
import sys
N = int(sys.argv[1]); K = int(sys.argv[2])
def run(cells, N):
    off = N + 50
    row = 0
    for p in cells: row |= 1 << (p + off)
    tr = []; rows = []
    for t in range(N):
        tr.append((row >> off) & 1); rows.append(row)
        row = (row << 1) ^ (row | (row >> 1))
    return tr, rows, off
base, brows, off = run([0], N)
for k in range(1, K + 1):
    tr, rows, _ = run([0, k], N)
    first = next((t for t in range(N) if tr[t] != base[t]), None)
    # leftmost difference position at a few times
    fronts = []
    for t in (N // 8, N // 4, N // 2, N - 1):
        d = rows[t] ^ brows[t]
        if d == 0: fronts.append(None); continue
        low = (d & -d).bit_length() - 1
        fronts.append(low - off)
    print(f"k={k}: first trace divergence t={first}; leftmost diff pos at t={N//8},{N//4},{N//2},{N-1}: {fronts}")
