# Period-2 left search with the right half's empirical block law imposed:
# y = column 1 at white times is in {A=10000, B=100}* with B isolated (any starting phase).
import sys, time
exec(open('search2_free.py').read().split('maxd = int')[0])   # step(), suffix_xor
A, B = '10000', '100'
# DFA states: (block, pos, lastWasB). Emitting y bit = block[pos]; after the last bit, choose next block.
def nexts(state):
    blk, pos, lastB = state
    w = A if blk == 'A' else B
    if pos + 1 < len(w): return [(blk, pos + 1, lastB)]
    isB = (blk == 'B')
    out = [('A', 0, False)]
    if not isB: out.append(('B', 0, True))
    return out
def bit(state):
    blk, pos, _ = state
    return int((A if blk == 'A' else B)[pos])
starts = [('A', p, False) for p in range(5)] + [('A', p, True) for p in range(5)] + [('B', p, True) for p in range(3)]
def run(a, W, maxdepth, cap=3_000_000):
    c = lambda t: (a + t) & 1
    states = set()
    for s0 in starts: states.add((0, 0, s0, True))   # (Dkm1, Dk, dfa state, need_emit_next)
    counts = []
    for k in range(0, maxdepth):
        new = set()
        for (Dkm1, Dk, q, fresh) in states:
            if c(k) == 0:      # white time: x(k) must equal the next y bit
                qs = [q] if fresh else nexts(q)
                for q2 in qs:
                    Dn = step(Dkm1, Dk, k, bit(q2), c)
                    if k + 1 > W and (Dn & 1): continue
                    new.add((Dk, Dn, q2, False))
            else:              # black time: x(k) does not affect the left half
                Dn = step(Dkm1, Dk, k, 0, c)
                if k + 1 > W and (Dn & 1): continue
                new.add((Dk, Dn, q, fresh))
        states = new
        counts.append(len(states))
        if not states or len(states) > cap: break
    return counts
t0 = time.time()
for a in (0, 1):
    res = []
    for W in range(0, 200, 4):
        cnt = run(a, W, W + 300)
        d = len(cnt) if cnt[-1] == 0 else None
        res.append((W, d, max(cnt)))
        if time.time() - t0 > 25 * (a + 1): break
    print(f"a={a}: (W, death depth, max survivors):", res)
    print("    death - W:", [d - W for (W, d, m) in res if d is not None])
