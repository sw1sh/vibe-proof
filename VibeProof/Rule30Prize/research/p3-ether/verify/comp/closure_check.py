# Verifier: forward closure (both right inputs) of the strip state reached by the empty right half driven by
# 001 (phase 0) at time 1270, at widths 46..49; compare width 47 with t001 (as (strip, phase) pairs).
import sys
w = [0, 0, 1]
row = 0
for t in range(1270):
    c = w[t % 3]; full = c | (row << 1); row = full ^ ((full >> 1) | (full >> 2))
ph = 1270 % 3
t001 = set()
with open(sys.argv[1]) as f:
    f.readline()
    for line in f:
        s, l = map(int, line.split()); t001.add((s, l % 3))
def closure(b, cap):
    mask = (1 << b) - 1; start = (row & mask, ph); seen = {start}; stack = [start]
    while stack:
        r, f = stack.pop(); a = w[f]
        for z in (0, 1):
            n = (((r << 1) | a) ^ (r | (r >> 1) | (z << (b - 1)))) & mask
            nx = (n, (f + 1) % 3)
            if nx not in seen:
                seen.add(nx); stack.append(nx)
                if len(seen) > cap: return seen, False
    return seen, True
for b in (47, 48, 49, 46):
    S, done = closure(b, 400000)
    print("b=%d closure size %s%d" % (b, "" if done else "> ", len(S)), "| equals t001:" if b == 47 else "", (S == t001) if b == 47 else "")
