"""Validate the bitset driven-right-half simulator against a naive list implementation."""
import random, sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-theoremB-cx')
import theoremB_driven as M

def naive(row0_bits, driver, steps, width):
    # row as list over columns 1..width (+ growth); cells beyond given width are 0 initially
    Wtot = width + steps + 2
    row = row0_bits + [0] * (Wtot - len(row0_bits))
    out = [row[:]]
    for t in range(steps):
        new = []
        for i in range(Wtot):
            left = driver[t] if i == 0 else row[i - 1]
            right = row[i + 1] if i + 1 < Wtot else 0
            new.append(left ^ (row[i] | right))
        row = new
        out.append(row[:])
    return out

rng = random.Random(99)
mism = 0
for trial in range(200):
    W = rng.randrange(1, 40)
    steps = rng.randrange(1, 120)
    bits = [rng.randrange(2) for _ in range(W)]
    drv = [rng.randrange(2) for _ in range(steps + 1)]
    x0 = sum(b << i for i, b in enumerate(bits))
    rows = M.simulate(x0, drv, steps)
    nv = naive(bits, drv, steps, W)
    for t in range(steps + 1):
        for p in range(1, W + steps + 1):
            # naive valid where right boundary effect hasn't reached: cell index p-1 < Wtot - (steps)
            if M.bit(rows[t], p) != nv[t][p - 1]:
                mism += 1
print('mismatches:', mism)

# Also: full-line real rule 30 right half equals driven right half with the real center column
steps = 800
W = 2 * steps + 5
mid = steps + 2
from real_pattern_check import evolve_full_int
full = evolve_full_int(1 << mid, W, steps)
c = [(full[t] >> mid) & 1 for t in range(steps + 1)]
rows = M.simulate(0, c, steps)
bad = 0
for t in range(steps + 1):
    for p in range(1, steps + 2):
        if M.bit(rows[t], p) != (full[t] >> (mid + p)) & 1:
            bad += 1
print('driven right half vs real full pattern mismatches:', bad)
