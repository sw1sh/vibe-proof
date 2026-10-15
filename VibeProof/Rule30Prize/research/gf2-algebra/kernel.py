# 2-kernel of the center column: number of distinct sequences n -> c(2^k n + r), 0 <= r < 2^k, k <= K,
# compared on n in [0, L).  For a 2-automatic sequence this count stays bounded as K grows.
d = open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin', 'rb').read()
c = [(d[i >> 3] >> (7 - (i & 7))) & 1 for i in range(len(d) * 8)]
L = 64
for K in range(0, 14):
    seen = set()
    for k in range(K + 1):
        for r in range(1 << k):
            seen.add(tuple(c[(n << k) + r] for n in range(L)))
    print("K=%d distinct kernel words (length %d): %d of %d" % (K, L, len(seen), (1 << (K + 1)) - 1))
