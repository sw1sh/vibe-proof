# Independent explicit-array check of the non-sufficiency witnesses (different code path from shieldk.c).
# Column index q = p - m (q = 0 is column m, black for all K steps). Initial row q = 1..W from the witness
# (bit i = column m+1+i), then random padding to the right (outside the backward cone of the read cells).
import random
def run(K, W, word, n, pad_seed):
    rng = random.Random(pad_seed)
    row = {q: (word >> (q - 1)) & 1 for q in range(1, W + 1)}
    for q in range(W + 1, W + K + 5): row[q] = rng.randint(0, 1)   # junk outside the cone
    hi = W + K + 4
    for t in range(K):
        new = {}
        for q in range(1, hi):
            left = 1 if q == 1 else row[q - 1]      # column m black at time t
            new[q] = left ^ (row[q] | row[q + 1])
        row = new; hi -= 1
    return ''.join(str(row[q]) for q in range(1, n + 1))
for (K, n, word) in [(8, 2, 0x13), (17, 4, 0x45), (26, 6, 0xe6f1b2f3)]:
    outs = {run(K, K + n, word, n, s) for s in range(20)}
    print(f"K={K}: cells m+1..m+{n} after K black steps from witness {hex(word)}: {outs}  target {'01'*(n//2)}")
# also: random rows with K = 9j always give (01)^j (sanity, small sample)
rng = random.Random(7)
for j in (1, 2, 3):
    K = 9 * j; n = 2 * j; ok = True
    for _ in range(3000):
        w = rng.getrandbits(K + n)
        if run(K, K + n, w, n, rng.random()) != '01' * j: ok = False; break
    print(f"K={K}: 3000 random rows all give {'01'*j}: {ok}")
