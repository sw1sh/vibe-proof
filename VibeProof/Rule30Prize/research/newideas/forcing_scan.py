# Forcing criterion: rotate w to start right after its longest black run (length K); S0 = states reachable
# after K black steps from any strip state (width b, free column b+1); simulate one period with the subset
# construction; criterion holds if col_1 is constant on S_j at every white position j.
import sys, itertools
def step_set(S, cval, b):
    out = set()
    for s in S:
        bit = lambda p: cval if p == 0 else (s >> (p - 1)) & 1
        base = 0
        for p in range(1, b):
            base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
        if bit(b): out.add(base | ((1 ^ bit(b - 1)) << (b - 1)))
        else: out.add(base); out.add(base | (1 << (b - 1)))
    return frozenset(out)
b = int(sys.argv[1]); Pmax = int(sys.argv[2])
R = {0: frozenset(range(1 << b))}
for K in range(1, 64): R[K] = step_set(R[K - 1], 1, b)
def criterion(w):
    P = len(w)
    if '0' not in w or '1' not in w: return False
    # longest cyclic black run and rotation
    best = (0, 0)
    for i in range(P):
        if w[i] == '1' and w[i - 1] == '0':
            L = 0
            while w[(i + L) % P] == '1': L += 1
            best = max(best, (L, i))
    K, i = best
    rot = w[(i + K) % P:] + w[:(i + K) % P]   # starts right after the run; ends with the run
    S = R[K]
    for ch in rot[:P - K]:
        if ch == '0' and len(set(s & 1 for s in S)) != 1: return False
        S = step_set(S, int(ch), b)
    return True
tot = {}; ok = {}
for P in range(2, Pmax + 1):
    for bits in itertools.product('01', repeat=P):
        w = ''.join(bits)
        if any(w == w[k:] + w[:k] for k in range(1, P) if P % k == 0): continue
        if w != min(w[k:] + w[:k] for k in range(P)): continue
        tot[P] = tot.get(P, 0) + 1
        if criterion(w): ok[P] = ok.get(P, 0) + 1
print("P: forced-excluded / primitive words")
for P in sorted(tot): print(P, ok.get(P, 0), tot[P])
