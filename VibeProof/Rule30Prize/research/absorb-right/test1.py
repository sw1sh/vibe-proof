import sys, random
sys.path.insert(0, '.')
from sim import *
random.seed(1)
steps = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 6
for n in range(1, maxlen + 1):
    for w in lyndon_words(n):
        res = []
        for phase in range(n):
            for trial in range(3):
                width = random.choice([0, 1, 5, 20, 200, 1000])
                row = random.getrandbits(width) if width > 0 else 0
                col, _ = run(w, phase, row, steps)
                ep = eventual_period(col, maxP=steps//4)
                res.append(ep)
        nper = sum(1 for e in res if e is not None)
        print(w, f"{nper}/{len(res)} periodic", sorted(set(e[1] for e in res if e)), "maxT", max([e[0] for e in res if e] or [None]))
