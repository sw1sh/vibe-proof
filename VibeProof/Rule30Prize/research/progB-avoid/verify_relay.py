# Rigorous check that a finite configuration's 0001-driven orbit never enters the trap S_w (width-16, 109 states):
# at time t its width-B strip state has a forward closure (under all inputs at column B+1) that is
# (a) closed by construction, (b) consistently labelled by a periodic output word, and (c) disjoint from S_w
# after projection to columns 1..16.  Since S_w is itself closed under all inputs, the orbit never visits S_w.
import sys
from collections import deque
sys.path.insert(0, '.')
from sim import run
w = '0001'; P = 4
def succ2(b, ph, s):
    c = int(w[ph]); bit = lambda p: c if p == 0 else (s >> (p - 1)) & 1
    base = 0
    for p in range(1, b): base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
    nph = (ph + 1) % P
    return sorted(set((nph, base | ((bit(b - 1) ^ (bit(b) | x)) << (b - 1))) for x in (0, 1)))
def closure(b, start):
    seen = {start}; dq = deque([start])
    while dq:
        v = dq.popleft()
        for u in succ2(b, *v):
            if u not in seen: seen.add(u); dq.append(u)
    return seen
def consistent(b, S, start, word):
    m = len(word); pos = {start: 0}; dq = deque([start])
    while dq:
        v = dq.popleft(); ph, s = v
        if w[ph] == '0':
            if (s & 1) != word[pos[v] % m]: return False
            np_ = (pos[v] + 1) % m
        else: np_ = pos[v]
        for u in succ2(b, ph, s):
            assert u in S
            if u in pos:
                if pos[u] != np_: return False
            else: pos[u] = np_; dq.append(u)
    return True
# load S_w and check that it is closed and consistent
lines = open('../newideas/trap_0001_16.txt').read().strip().split('\n')
Sw = set(tuple(map(int, l.split()[:2])) for l in lines[1:])
assert all(u in Sw for v in Sw for u in succ2(16, *v)), "S_w not closed"
cfg = sys.argv[1]; ph0 = int(sys.argv[2]); t0 = int(sys.argv[3]); B = int(sys.argv[4])
x = sum(1 << i for i, ch in enumerate(cfg) if ch == '1')
hist = run(x, w, ph0, t0 + 400)
outs = [hist[t][1] & 1 for t in range(t0, t0 + 400) if w[hist[t][0]] == '0']
m = next(d for d in range(1, len(outs) // 3) if all(outs[i] == outs[i + d] for i in range(len(outs) - d)))
start = (hist[t0][0], hist[t0][1] & ((1 << B) - 1))
C = closure(B, start)
ok = consistent(B, C, start, outs[:m])
proj = set((ph, s & 0xFFFF) for (ph, s) in C)
print(f"cfg={cfg} phase0={ph0}: at t={t0} width {B}: closure {len(C)} states, consistent={ok}, "
      f"output word {''.join(map(str, outs[:m]))}, projection to width 16 meets S_w: {bool(proj & Sw)}")
# also: did the simulated orbit visit S_w before t0?
print("  visited S_w before t0:", any((h[0], h[1] & 0xFFFF) in Sw for h in hist[:t0 + 1]))
# periodic columns at the end
for p in range(1, 26):
    seq = [(hist[t][1] >> (p - 1)) & 1 for t in range(t0, t0 + 400)]
    per = next((d for d in range(1, 100) if all(seq[i] == seq[i + d] for i in range(len(seq) - d))), None)
    print(f"  col {p}: period {per}", end=';')
print()
