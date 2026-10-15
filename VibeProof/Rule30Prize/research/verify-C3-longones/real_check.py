# Sanity checks on the real rule-30 pattern (single black cell), N steps.
# Row stored as a Python int; bit (p + OFF) is cell(t,p).
N = 6000
OFF = N + 5
row = 1 << OFF
cols = {p: [] for p in (-1, 0, 1, 2)}
for t in range(N + 2):
    for p in cols:
        cols[p].append((row >> (p + OFF)) & 1)
    # new(p) = old(p-1) xor (old(p) or old(p+1)); old(p-1) at bit p means shift left by 1
    row = (row << 1) ^ (row | (row >> 1))
    row &= (1 << (2 * OFF + 1)) - 1
c, a, b, m = cols[0], cols[1], cols[2], cols[-1]
assert c[:20] == [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1], c[:20]
# 1. absorption on real data
hits = 0
for t in range(N - 9):
    if all(c[t + i] for i in range(9)):
        hits += 1
        assert a[t + 9] == 0 and b[t + 9] == 1, t
print("windows of 9 ones in c(0..N):", hits, "- absorption held on all")
# 2. cell_left at 0
for t in range(N):
    assert m[t] == c[t + 1] ^ (c[t] | a[t])
print("cell_left at 0 verified for t <", N)
# 3. key identity for white cells whose white run is preceded by >= 9 ones
cnt = 0
for t in range(10, N):
    if c[t] == 0:
        s = t
        while s > 0 and c[s - 1] == 0:
            s -= 1
        if s >= 9 and all(c[s - 1 - i] for i in range(9)):
            cnt += 1
            assert a[t] == 1 - c[t - 1], t
print("white cells after a >=9 run of ones:", cnt, "- key identity held on all")
# longest 1-run in c(0..N)
best = cur = 0
for x in c[:N]:
    cur = cur + 1 if x else 0
    best = max(best, cur)
print("longest run of ones in c(0..N):", best)
