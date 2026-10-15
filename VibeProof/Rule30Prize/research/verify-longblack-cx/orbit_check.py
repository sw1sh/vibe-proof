import sys
from collections import Counter
cols = open(sys.argv[1], 'rb').read()
N = len(cols)
c  = [b & 1 for b in cols]
m1 = [(b >> 1) & 1 for b in cols]
p1 = [(b >> 2) & 1 for b in cols]
p2 = [(b >> 3) & 1 for b in cols]

# (0) cross-check centre column against the Ruliology data file (read-only)
raw = open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin', 'rb').read()
ref = [(raw[i >> 3] >> (7 - (i & 7))) & 1 for i in range(min(N, 8 * len(raw)))]
print("first 20 c:", ''.join(map(str, c[:20])))
print("(0) centre column mismatches vs center-1e7.bin:", sum(1 for i in range(len(ref)) if ref[i] != c[i]))

# (1),(2) left-permutivity identities
bad1 = sum(1 for t in range(N - 1) if m1[t] != (c[t + 1] ^ (c[t] | p1[t])))
bad2 = sum(1 for t in range(N - 1) if c[t] != (p1[t + 1] ^ (p1[t] | p2[t])))
print("(1) cell(t,-1) = c(t+1) xor (c(t) or cell(t,1)) failures:", bad1)
print("(2) c(t) = cell(t+1,1) xor (cell(t,1) or cell(t,2)) failures:", bad2)

# (3) black-run forcing on the actual orbit
occ = bad3 = 0
for t in range(N - 9):
    if all(c[t + j] for j in range(9)):
        occ += 1
        if not (p1[t + 9] == 0 and p2[t + 9] == 1):
            bad3 += 1
print(f"(3) 9 consecutive blacks: {occ} occurrences, forcing failures: {bad3}")

# black run lengths and white runs preceded by black runs
runs = []   # (start, length, colour)
s = 0
for t in range(1, N + 1):
    if t == N or c[t] != c[s]:
        runs.append((s, t - s, c[s])); s = t
blk = Counter(L for (_, L, col) in runs if col == 1)
print("max black run:", max(blk), " black-run length histogram >= 9:", sorted((L, n) for L, n in blk.items() if L >= 9))

# (4),(5) after a white run start z preceded by >= 9 blacks
nz = bad4 = bad5 = cells4 = 0
fail_by_pre = Counter(); tot_by_pre = Counter()
for idx in range(1, len(runs)):
    z, L, col = runs[idx]
    if col != 0 or z + L >= N: continue
    pre = runs[idx - 1][1]           # length of preceding black run
    for k in range(L):
        t = z + k
        ok_key = (p1[t] == 1 - c[t - 1])
        tot_by_pre[min(pre, 9)] += 1
        if not ok_key: fail_by_pre[min(pre, 9)] += 1
    if pre >= 9:
        nz += 1
        for k in range(L):
            cells4 += 1
            if p1[z + k] != (1 if k > 0 else 0): bad4 += 1
            if p1[z + k] != 1 - c[z + k - 1]: bad5 += 1
        if p2[z] != 1: bad4 += 1
print(f"(4) white runs preceded by >=9 blacks: {nz} runs, {cells4} white cells; col1/col2 pattern failures: {bad4}")
print(f"(5) key identity cell(t,1) = not c(t-1) failures on those cells: {bad5}")
print("    key identity failure rate on white cells, by preceding black-run length (9 means >=9):")
for pre in sorted(tot_by_pre):
    print(f"      pre={pre}: {fail_by_pre[pre]}/{tot_by_pre[pre]}")
