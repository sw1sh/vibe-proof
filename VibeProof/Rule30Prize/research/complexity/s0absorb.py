# Right half driven by w^inf from random finite right-half states (cone edge: rightmost cell black).
# Compare: is column 1 eventually periodic? Is column 1 restricted to the phases where w = 0
# (the only phases that feed column -1 through the center) eventually periodic?
import random, sys, itertools
def run_right(w, init, W0, steps):
    row = init; width = W0; col = []
    wb = [int(ch) for ch in w]
    for t in range(steps):
        col.append(row & 1)
        width += 1; mask = (1 << width) - 1
        row = ((((row << 1) | wb[t % len(w)]) & mask) ^ (row | (row >> 1))) & mask
    return col
def eventual_period(seq, maxP=1024):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
def primitive_words(maxlen):
    seen = set()
    for L in range(2, maxlen + 1):
        for bits in itertools.product('01', repeat=L):
            w = ''.join(bits)
            if '1' not in w or '0' not in w: continue
            if any(L % d == 0 and w == w[:d] * (L // d) for d in range(1, L)): continue
            canon = min(w[i:] + w[:i] for i in range(L))
            if canon in seen: continue
            seen.add(canon); yield canon
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 5
steps = 4000
for w in primitive_words(maxlen):
    full, s0 = [], []
    for trial in range(4):
        W0 = random.choice([16, 128, 700])
        init = random.getrandbits(W0) | (1 << (W0 - 1))
        col = run_right(w, init, W0, steps)
        masked = [col[t] if w[t % len(w)] == '0' else 0 for t in range(steps)]
        full.append(eventual_period(col) is not None); s0.append(eventual_period(masked) is not None)
    tag = 'ABSORB(all phases)' if all(full) else ('ABSORB(S0 phases only)' if all(s0) else ('mixed' if any(s0) else '-'))
    print(f"{w:8s} col1 periodic: {full}  col1|S0 periodic: {s0}  {tag}")
