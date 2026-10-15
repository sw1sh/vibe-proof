import random
def step_right(r, c0, width):
    left = (r << 1) | c0
    right = r >> 1
    return (left ^ (r | right)) & ((1 << width) - 1)
random.seed(2)
first_bad = []
gaps_all = {}
for trial in range(2000):
    w = random.randint(1, 60)
    r = random.getrandbits(w) | (1 << (w - 1))
    a = random.getrandbits(1)
    T = 600
    width = w + T + 2
    ones_white = []
    for t in range(T):
        c0 = (a + t) % 2
        if c0 == 0 and (r & 1): ones_white.append(t)
        r = step_right(r, c0, width)
    gaps = [(y - x, x) for x, y in zip(ones_white, ones_white[1:])]
    for g, x in gaps:
        gaps_all[g] = gaps_all.get(g, 0) + 1
        if g not in (4, 6, 10): first_bad.append((g, x, w))
print(sorted(gaps_all.items())[:40])
print("max time of a gap not in {4,6,10}:", max((x for g, x, w in first_bad), default=None))
import collections
print(collections.Counter((g) for g, x, w in first_bad).most_common(20))
