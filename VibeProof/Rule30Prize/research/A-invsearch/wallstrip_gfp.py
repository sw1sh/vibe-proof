# Wall-frame strip abstraction of width w (depths 1..w), free input at depth w+1 each step.
# Abstract double step at even times; constraint: depth-1 cell black at even times.
# Compute the greatest fixed point S = states with an infinite constrained abstract run, compare with Pref_w(Phi(Y)).
import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import reconstruct
def step_w(u, v, w):
    # u: bits 0..w-1 <-> depths 1..w ; v = input at depth w+1
    full = u | (v << w)
    new = (full >> 1) ^ (full | (full << 1))
    return new & ((1 << w) - 1)
def gfp(w):
    S = {u for u in range(1 << w) if u & 1}
    succ = {}
    for u in S:
        out = set()
        for v1 in (0, 1):
            m = step_w(u, v1, w)
            for v2 in (0, 1):
                out.add(step_w(m, v2, w))
        succ[u] = out
    changed = True
    while changed:
        changed = False
        for u in list(S):
            if not (succ[u] & S):
                S.discard(u); changed = True
    return S
def prefixes(w):
    P = set()
    m = (w + 1) // 2 + 2
    for fb in range(1 << m):
        y = []
        for t in range(2 * m + 2):
            y.append(1 if t % 2 == 0 else (fb >> (t // 2)) & 1)
        L = reconstruct(y, w)
        P.add(sum(b << i for i, b in enumerate(L)))
    return P
for w in range(1, 15):
    S = gfp(w); P = prefixes(w)
    print(f'w={w:2d}: |gfp| = {len(S):5d}, 2^floor(w/2) = {1 << (w // 2):5d}, gfp == Pref_w(Phi(Y)): {S == P}')
