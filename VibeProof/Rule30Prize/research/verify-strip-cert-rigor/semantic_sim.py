# Semantic sanity check: drive the right half of rule 30 with column 0 = w^inf (random right half),
# and report column 1 at white times in the late part of the run (should be periodic per the certificate words).
import random, sys
def sim(w, width=1500, steps=1200, seed=0):
    rnd = random.Random(seed)
    P = len(w)
    row = [rnd.randint(0, 1) for _ in range(width)]  # columns 1..width
    hist = []
    for t in range(steps):
        c0 = int(w[t % P])
        if c0 == 0: hist.append((t % P, row[0]))
        ext = [c0] + row + [rnd.randint(0, 1)]
        row = [ext[i] ^ (ext[i+1] | ext[i+2]) for i in range(width)]
    return hist
for w in sys.argv[1:]:
    res = set()
    for seed in range(6):
        h = sim(w, seed=seed)
        tail = h[-60:]
        res.add(''.join(str(x) for _, x in tail[:30]))
    print(w, 'late col1-at-white-times samples:', sorted(res))
