# Check the local lemmas of the C3 proof on the actual rule-30 pattern from a single black cell.
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
off = N + 2
row = 1 << off   # position p <-> bit off+p
cols = {p: [] for p in range(-3, 4)}
for t in range(N + 2):
    for p in cols:
        cols[p].append((row >> (off + p)) & 1)
    # new(p) = old(p-1) xor (old(p) or old(p+1)); bit i of (row<<1) is old bit i-1 = old(p-1)
    row = (row << 1) ^ (row | (row >> 1))
c = cols[0]
A051023 = [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1]
print("prefix matches brief:", c[:20] == A051023)

# cross-check against the read-only data file (first value in the high bit)
path = "/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin"
with open(path, "rb") as f:
    data = f.read((N + 7) // 8 + 1)
ref = []
for byte in data:
    for k in range(7, -1, -1):
        ref.append((byte >> k) & 1)
print("matches center-1e7.bin on first", N, "values:", ref[:N] == c[:N])

bad = 0
# (b) cell_left at column 0
for t in range(N):
    if cols[-1][t] != (c[t+1] ^ (c[t] | cols[1][t])):
        bad += 1
print("cell_left(0) violations:", bad)

# (c) absorb: c(t-9..t-1) = 1  =>  (cell(t,1), cell(t,2)) = (0,1)
cnt = viol = 0
for t in range(9, N):
    if all(c[t-1-i] for i in range(9)):
        cnt += 1
        if (cols[1][t], cols[2][t]) != (0, 1):
            viol += 1
print(f"absorb: {cnt} instances, {viol} violations")
# with only 8 ones, how often does absorb fail on the real pattern?
cnt8 = viol8 = 0
for t in range(9, N):
    if all(c[t-1-i] for i in range(8)) and c[t-9] == 0:
        cnt8 += 1
        if (cols[1][t], cols[2][t]) != (0, 1):
            viol8 += 1
print(f"exactly-8-ones-before: {cnt8} instances, (col1,col2)!=(0,1) in {viol8}")

# (d) key + (e) formula for column -1
cnt_key = viol_key = viol_form = 0
s = None
for t in range(1, N):
    if c[t] == 1:
        s = None
        if cols[-1][t] != 1 - c[t+1]:
            viol_form += 1
        continue
    if c[t-1] == 1:
        s = t
    if s is None or s < 9:
        continue
    if all(c[s-1-i] for i in range(9)):
        cnt_key += 1
        if cols[1][t] != 1 - c[t-1]:
            viol_key += 1
        if cols[-1][t] != (c[t+1] ^ (c[t] | (1 - c[t-1]))):
            viol_form += 1
print(f"key (white t whose run start follows >=9 ones): {cnt_key} instances, {viol_key} violations")
print(f"column -1 formula violations: {viol_form}")

# white_run: c(t)=0 and (col1 or col2)=1  =>  col1(t+1)=1
viol_wr = cnt_wr = 0
for t in range(N):
    if c[t] == 0 and (cols[1][t] | cols[2][t]):
        cnt_wr += 1
        if cols[1][t+1] != 1:
            viol_wr += 1
print(f"white_run: {cnt_wr} instances, {viol_wr} violations")
# longest 1-run in the prefix
best = run = 0
for x in c[:N]:
    run = run + 1 if x else 0
    best = max(best, run)
print("longest run of ones in c(0..N-1):", best)
