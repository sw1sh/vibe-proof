# Single-seed center columns of the left-permutive ECAs (new = l xor f(c,r)) with quiescent 0.
import sys
def run(rule, N):
    W = 2*N + 3; row = 1 << (N+1); cols = {d: [] for d in range(-3, 4)}
    rows = []
    for t in range(N):
        for d in cols: cols[d].append((row >> (N+1+d)) & 1)
        nxt = 0
        # bit i: position i-(N+1); neighbours l = bit i+1? choose: bit index increases with position
        for i in range(1, W-1):
            l = (row >> (i-1)) & 1; c = (row >> i) & 1; r = (row >> (i+1)) & 1
            if (rule >> (4*l + 2*c + r)) & 1: nxt |= 1 << i
        row = nxt
    return cols
def eventual_period(seq, maxP=256):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
N = int(sys.argv[1]) if len(sys.argv) > 1 else 600
for rule in [30, 90, 150, 210, 120, 180, 60, 240]:
    cols = run(rule, N)
    print(rule, {d: eventual_period(cols[d]) for d in cols}, ''.join(map(str, cols[0][:40])))
