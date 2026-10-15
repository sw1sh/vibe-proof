# Enumerate spatio-temporally periodic rule-30 patterns: configurations on a ring Z/q lying on a cycle of
# length r (r <= RMAX). Record the primitive column words (up to rotation) that occur.
import sys
QMAX = int(sys.argv[1]); RMAX = int(sys.argv[2])
def step(x, q):
    m = (1 << q) - 1
    left = ((x << 1) | (x >> (q - 1))) & m   # bit p <- bit p-1
    right = ((x >> 1) | (x << (q - 1))) & m  # bit p <- bit p+1
    return (left ^ (x | right)) & m
def prim(word):
    n = len(word)
    for d in range(1, n + 1):
        if n % d == 0 and word == word[:d] * (n // d): return word[:d]
def canon(word):
    return min(word[i:] + word[:i] for i in range(len(word)))
found = {}
for q in range(1, QMAX + 1):
    for x in range(1 << q):
        y = x; ok = False
        for r in range(1, RMAX + 1):
            y = step(y, q)
            if y == x: ok = True; break
        if not ok: continue
        # columns
        rows = [x]
        for _ in range(r - 1): rows.append(step(rows[-1], q))
        for p in range(q):
            col = ''.join(str((rw >> p) & 1) for rw in rows)
            cw = canon(prim(col))
            found.setdefault(cw, set()).add((q, r))
for w in sorted(found, key=lambda s: (len(s), s)):
    print(w, sorted(found[w])[:6])
