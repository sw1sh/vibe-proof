# ZBL: x_t(k), k>=1, x_t(0)=0. bit (k-1) of int x is x(k).
# x' = (x>>1) ^ (x | (x<<1))
def step(x):
    return (x >> 1) ^ (x | (x << 1))
def survive(x, phase=0, maxt=10**6):
    """first t>=0 with t%2==phase and bit0==0; returns t (death time) or None"""
    t = 0
    while t < maxt:
        if t % 2 == phase and (x & 1) == 0:
            return t
        x = step(x); t += 1
    return None
if __name__ == "__main__":
    import sys
    W = int(sys.argv[1])
    best = {}
    hist = {}
    for x in range(1, 1 << W):
        d = survive(x, 0, 10*W+100)
        K = x.bit_length()
        best[K] = max(best.get(K, -1), d)
    print([(K, best[K]) for K in sorted(best)])
