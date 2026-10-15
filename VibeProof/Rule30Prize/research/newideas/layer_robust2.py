# More extensive robustness test: keep strip 1..k-1 of an absorbed state, replace positions >= k by
# random configurations of various densities / structured patterns, evolve, test layer cols 1..L.
import sys, random
w = sys.argv[1]; k = int(sys.argv[2]); trials = int(sys.argv[3]); L = int(sys.argv[4]); horizon = int(sys.argv[5]); seed0 = int(sys.argv[6])
P = len(w)
random.seed(seed0)
def evolve(row, t0, n, record=0):
    W = row.bit_length() + n + 4; mask = (1 << W) - 1
    cols = []
    for t in range(t0, t0 + n):
        if record: cols.append(row & ((1 << record) - 1))
        ct = int(w[t % P])
        row = ((((row << 1) | ct) & mask) ^ (row | (row >> 1))) & mask
    return row, cols
row = random.getrandbits(300)
row, _ = evolve(row, 0, 3000)
t0 = 3000
_, ref = evolve(row, t0, 256, record=L)
per = None
for Q in range(P, 257, P):
    if all(ref[i] == ref[i + Q] for i in range(256 - Q)): per = Q; break
print("layer period", per)
broke = 0; fb = []
for tr in range(trials):
    width = 400
    mode = tr % 5
    if mode == 0: tail = random.getrandbits(width)
    elif mode == 1: tail = sum(1 << i for i in range(width) if random.random() < 0.1)
    elif mode == 2: tail = sum(1 << i for i in range(width) if random.random() < 0.9)
    elif mode == 3:
        pat = [random.getrandbits(1) for _ in range(random.randint(1, 8))]
        tail = sum(1 << i for i in range(width) if pat[i % len(pat)])
    else:
        tail = random.getrandbits(random.randint(1, 30))
    keep = row & ((1 << (k - 1)) - 1)
    newrow = keep | (tail << (k - 1))
    _, cols = evolve(newrow, t0, horizon, record=L)
    bad = None
    for i in range(horizon):
        if cols[i] != ref[i % per]: bad = i; break
    if bad is not None: broke += 1; fb.append((bad, mode))
print(f"w={w} k={k}: broken {broke}/{trials}; samples {sorted(fb)[:12]}")
