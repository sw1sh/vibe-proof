# Independent simulation: rule 30 (new = left xor (center or right), left = p-1) on positions p <= -1,
# positions p >= 0 forced white. Start: black exactly at p = -k, k odd, 1 <= k <= n.
import sys

def run(n, T):
    # positions p in [-(n + T + 3), 0]; index i = -p (depth); depth 0 = wall
    size = n + T + 5
    row = [0] * (size + 2)
    for k in range(1, n + 1):
        if k % 2 == 1:
            row[k] = 1
    hist = [row[1]]
    for t in range(T):
        new = [0] * (size + 2)
        for k in range(1, size + 1):
            left = row[k + 1]      # p-1 is depth k+1
            center = row[k]
            right = row[k - 1]     # p+1 is depth k-1 (depth 0 = wall, always 0)
            new[k] = left ^ (center | right)
        new[0] = 0
        row = new
        hist.append(row[1])
    return hist

bad = []
summary = {}
for n in range(1, 402, 2):
    h = run(n, n + 12)
    ok = all(h[t] == 1 for t in range(n + 1)) and h[n + 1] == 0
    if not ok:
        bad.append(n)
    # even-phase death: first even t with h[t] == 0 ; odd-phase death: first odd t with h[t] == 0
    ev = next((t for t in range(0, len(h), 2) if h[t] == 0), None)
    od = next((t for t in range(1, len(h), 2) if h[t] == 0), None)
    summary[n] = (ev, od)
print("odd n in 1..401 violating (black for t<=n, white at n+1):", bad)
for n in (1, 3, 5, 11, 21, 41, 81):
    ev, od = summary[n]
    print(f"n={n}: first white even time={ev} (n+1={n+1}); first white odd time={od} (n+2={n+2})")
print("odd-phase first death - n over all odd n<=401:", sorted(set(summary[n][1] - n for n in summary if summary[n][1] is not None)))
