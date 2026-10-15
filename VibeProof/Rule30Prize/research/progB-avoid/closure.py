# forward closure under arbitrary input of a strip state at width b; check output consistency (good trap)
import sys
from collections import deque
sys.path.insert(0, '.')
from sim import *
def succ2(w, b, ph, s):
    P = len(w); c = int(w[ph]); bit = lambda p: c if p == 0 else (s >> (p - 1)) & 1
    base = 0
    for p in range(1, b): base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
    nph = (ph + 1) % P
    if bit(b):
        return [(nph, base | ((1 ^ bit(b - 1)) << (b - 1)))]
    return [(nph, base | (bit(b - 1) << (b - 1))), (nph, base | ((1 ^ bit(b - 1)) << (b - 1)))]
def closure(w, b, start, limit=2_000_000):
    seen = {start}; dq = deque([start])
    while dq:
        v = dq.popleft()
        for u in succ2(w, b, *v):
            if u not in seen:
                seen.add(u); dq.append(u)
                if len(seen) > limit: return None
    return seen
def consistent(w, seen, start, outword):
    # label positions along the output word (column 1 at white phases), BFS
    m = len(outword); pos = {start: 0}; dq = deque([start]); b = None
    while dq:
        v = dq.popleft(); ph, s = v
        if w[ph] == '0':
            if (s & 1) != outword[pos[v] % m]: return False
            np = (pos[v] + 1) % m
        else: np = pos[v]
        for u in succ2(w, BW, ph, s):
            if u in pos:
                if pos[u] != np: return False
            else: pos[u] = np; dq.append(u)
    return True
if __name__ == '__main__':
    w = sys.argv[1]; x = int(sys.argv[2], 2); ph0 = int(sys.argv[3]); T0 = int(sys.argv[4])
    hist = run(x, w, ph0, T0 + 200)
    outs = [hist[t][1] & 1 for t in range(T0, T0 + 200) if w[hist[t][0]] == '0']
    L = len(outs)
    m = next(d for d in range(1, L) if all(outs[i] == outs[i + d] for i in range(L - d)))
    outword = outs[:m]
    print("output period word", ''.join(map(str, outword)))
    for BW in map(int, sys.argv[5:]):
        start = (hist[T0][0], hist[T0][1] & ((1 << BW) - 1))
        cl = closure(w, BW, start)
        if cl is None: print("b=%d closure too large" % BW); continue
        print("b=%d closure size %d consistent %s" % (BW, len(cl), consistent(w, cl, start, outword)))
