import random
def columns(f, K):
    T = 2 * len(f)
    a = 0
    for s, b in enumerate(f):
        a |= 1 << (2 * s)
        if b: a |= 1 << (2 * s + 1)
    cols = [0, a]
    prev, cur = 0, a
    for k in range(2, K + 1):
        nxt = ((cur >> 1) ^ (cur | prev)) & ((1 << (T - k)) - 1)
        prev, cur = cur, nxt
        cols.append(cur)
    return cols
random.seed(5)
stats = {}
for trial in range(4000):
    n = 40
    # bias toward long leading structure: use f with many 1s at start sometimes
    f = [random.getrandbits(1) for _ in range(n)]
    cols = columns(f, 30)
    for k in range(2, 30):
        c = cols[k]
        if c == 0: continue
        z = (c & -c).bit_length() - 1
        if z >= 1:
            key = (k, z % 2)
            stats[key] = stats.get(key, 0) + 1
for k in range(2, 30):
    print(k, stats.get((k, 0), 0), stats.get((k, 1), 0))
