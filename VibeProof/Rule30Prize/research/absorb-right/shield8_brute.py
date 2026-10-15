# Brute-force check of the sigma_8 shield: column m follows (1^7 0) phase-aligned so that the white
# cell is at time t; if column m equals sigma at times t-12..t-1, then x(t, m+1) = 0.
# Times t-12..t-1 have phases (t-12..t-1) mod 8 = 3,4,5,6,7,0,1,2,3,4,5,6 relative to t = 7 (mod 8):
# sigma at phase 7 is white -> column m at time t-8 is white; all other 11 times black.
K = 12
bound = [1] * K
bound[K - 8] = 0          # time t-8 is the previous white cell
# cone: x(t, m+1) depends on x(t-12, m+1 .. m+13): 13 cells
bad = 0
for X in range(1 << 13):
    row = X
    for s in range(K):
        row = (((row << 1) | bound[s]) ^ (row | (row >> 1))) & ((1 << 13) - 1)
    if row & 1: bad += 1
print("sigma_8 shield, depth 12: configurations giving x(t,m+1)=1:", bad, "of", 1 << 13)
# depth 11 is not enough:
K = 11; bound = [1] * K; bound[K - 8] = 0; bad = 0
for X in range(1 << 12):
    row = X
    for s in range(K):
        row = (((row << 1) | bound[s]) ^ (row | (row >> 1))) & ((1 << 12) - 1)
    if row & 1: bad += 1
print("depth 11: bad =", bad)
