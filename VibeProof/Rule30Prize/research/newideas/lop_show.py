# Show best LOP configurations for w (python, small M), with their horizon.
import sys
w = sys.argv[1]; P = len(w); M = int(sys.argv[2]); HMAX = 300
cv = lambda t: int(w[t % P])
def step(row, c, width):
    # bit i <-> p=-(i+1)
    mask = (1 << width) - 1
    right = ((row << 1) | c) & mask
    return ((row >> 1) ^ (row | right)) & mask
def horizon(cfg):
    row = cfg
    for t in range(HMAX):
        if cv(t) == 1 and (row & 1) != 1 - cv(t + 1): return t
        row = step(row, cv(t), M + t + 3)
    return HMAX
def colm1(cfg, k):
    row = cfg
    for t in range(k): row = step(row, cv(t), M + t + 3)
    return row & 1
res = []
def dfs(cfg, k):
    if k == M:
        res.append((horizon(cfg), cfg)); return
    if cv(k) == 1:
        v0 = colm1(cfg, k)
        bitv = 0 if v0 == 1 - cv(k + 1) else 1
        dfs(cfg | (bitv << k), k + 1)
    else:
        dfs(cfg, k + 1); dfs(cfg | (1 << k), k + 1)
dfs(0, 0)
res.sort(reverse=True)
for h, cfg in res[:8]:
    s = ''.join('#' if (cfg >> i) & 1 else '.' for i in range(M))[::-1]  # leftmost = p=-M
    print(h, s)
