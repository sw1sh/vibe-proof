# Sanity check on the actual rule 30 evolution from a single black cell.
N = 4000
W = N + 5
row = [0]*(2*W+1); row[W] = 1   # index W <-> position 0
C, C1, C2, Cm1 = [], [], [], []
for t in range(N):
    C.append(row[W]); C1.append(row[W+1]); C2.append(row[W+2]); Cm1.append(row[W-1])
    row = [0] + [row[i-1] ^ (row[i] | row[i+1]) for i in range(1, 2*W)] + [0]
print("c(0..19) =", "".join(map(str, C[:20])))
# 1) forcing on actual data: 9 blacks at z-9..z-1 => (cell(z,1),cell(z,2)) = (0,1)
hits = bad = 0
for z in range(9, N):
    if all(C[z-9+j] for j in range(9)):
        hits += 1
        if (C1[z], C2[z]) != (0, 1): bad += 1
print("times z with c(z-9..z-1) all black:", hits, " violations:", bad)
# 2) white t in a run preceded by >= 9 blacks => cell(t,1) = not c(t-1)
cnt = bad2 = 0
for t in range(10, N):
    if C[t] == 0:
        z = t
        while z > 0 and C[z-1] == 0: z -= 1
        if z >= 9 and all(C[z-9+j] for j in range(9)):
            cnt += 1
            if C1[t] != 1 - C[t-1]: bad2 += 1
print("white times in runs after >=9 blacks:", cnt, " violations:", bad2)
# 3) left-permutivity identity for column -1
bad3 = sum(1 for t in range(N-1) if Cm1[t] != C[t+1] ^ (C[t] | C1[t]))
print("cell_left identity violations:", bad3)
# longest black run in c(0..N-1)
best = cur = 0
for x in C:
    cur = cur + 1 if x else 0; best = max(best, cur)
print("longest black run up to", N, ":", best)
