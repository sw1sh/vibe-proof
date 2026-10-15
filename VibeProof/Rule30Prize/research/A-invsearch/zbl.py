# Reference implementation of the zero-boundary left half (ZBL) and the period-2 constraint.
# Config: python int, bit (k-1) <-> cell p = -k (k >= 1).  Wall: cell p = 0 is always 0.
# ZBL step: new(-k) = old(-(k+1)) xor (old(-k) or old(-(k-1))), old(0) = 0.
# Constraint (phase 0): column -1 is black at every even time t = 0, 2, 4, ...
# Death time D(x) = first even t with column -1 white (None if > horizon).

def step(x):
    # bit i <-> p = -(i+1); left neighbour p-1 is bit i+1; right neighbour p+1 is bit i-1 (bit -1 = wall = 0)
    return (x >> 1) ^ (x | (x << 1))  # (x<<1) has bit0 = 0 (wall); support grows by one bit on the left

def width(x):
    return x.bit_length()

def death(x, horizon=10**6, phase=0):
    t = 0
    while t < horizon:
        if (t - phase) % 2 == 0 and not (x & 1):
            return t
        x = step(x)
        t += 1
    return None

def col_m1(x, T):
    out = []
    for t in range(T):
        out.append(x & 1); x = step(x)
    return out

def stripe(n):
    # cells -1,-3,-5,... black up to depth n
    return sum(1 << (k - 1) for k in range(1, n + 1, 2))

def reconstruct(y, K):
    """Given column -1 values y[0..], reconstruct initial cells x_0(-k) for k=1..K (needs len(y) >= K).
    Uses left-permutivity: x_t(p-1) = x_{t+1}(p) xor (x_t(p) or x_t(p+1)), column 0 = 0."""
    prev = [0] * len(y)        # column 0
    cur = list(y)              # column -1
    L = [cur[0]]
    for k in range(2, K + 1):
        nxt = [cur[t + 1] ^ (cur[t] | prev[t]) for t in range(len(cur) - 1)]
        prev, cur = cur, nxt
        L.append(cur[0])
    return L

if __name__ == '__main__':
    import random
    # stripe is a fixed point (on its support, away from the truncation)
    s = stripe(41)
    print('stripe(41) death:', death(s, 200))
    for n in (11, 21, 41, 81):
        print('truncated stripe width', n, 'death', death(stripe(n), 10000))
    # reconstruction consistency
    random.seed(1)
    for _ in range(100):
        x = random.getrandbits(30)
        y = col_m1(x, 40)
        L = reconstruct(y, 40)
        xx = sum(b << i for i, b in enumerate(L))
        assert xx == x, (x, xx)
    print('reconstruction ok')
