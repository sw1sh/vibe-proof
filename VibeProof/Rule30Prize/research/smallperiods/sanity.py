# Sanity checks on the true rule 30 pattern:
# (1) effective boundary: cell(t,-1) or c(t) == cell(t,-1) or (c(t) and c(t+1))
# (2) c(t)=1 -> cell(t,-1) = not c(t+1)
N = 4000
row = 1 << N  # bit N <-> position 0
ok1 = ok2 = True
cs = []; am = []
for t in range(N):
    cs.append((row >> N) & 1); am.append((row >> (N - 1)) & 1)
    row = (row << 1) ^ (row | (row >> 1))
    row &= (1 << (2 * N + 2)) - 1
for t in range(N - 1):
    if (am[t] | cs[t]) != (am[t] | (cs[t] & cs[t+1])): ok1 = False
    if cs[t] == 1 and am[t] != 1 - cs[t+1]: ok2 = False
print('effective boundary identity holds:', ok1, '| c=1 -> a = not c(t+1):', ok2)
