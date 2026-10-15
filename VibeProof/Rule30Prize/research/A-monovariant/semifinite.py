import random, sys
# Build the semi-finite member of S: free bits chosen so that L(2i) = 0 for 2i > W; print odd tail.
def build(Lprefix_even, W, K):
    # Lprefix_even: dict of desired L(2i) for 2i <= W (others 0). We construct column-1 bits a_t greedily:
    # a_t forced 1 for even t; for odd t, choose a_t so that L(t+1) (even) equals target.
    # Anti-diagonal method: A_{m+1}(t) = A_{m+1}(t+1) ^ (A_m(t) | A_{m-1}(t)), A_{m+1}(m) = a_m.
    Am1 = [0]          # A_0 = [x_0(0)] = [0]  (length 1)
    Am = [0]           # placeholder A_0 ; we start with m=0: A_{-1} = A_0 = zeros
    A = {0: [0]}
    A[-1] = [0]
    L = {}
    a = []
    for m in range(0, K):
        prev, prev2 = A[m], A[m - 1]
        def make(x):
            An = [0] * (m + 2)
            An[m] = x; An[m + 1] = 0
            for t in range(m - 1, -1, -1):
                pm = prev[t] if t < len(prev) else 0
                pm2 = prev2[t] if t < len(prev2) else 0
                An[t] = An[t + 1] ^ (pm | pm2)
            return An
        if m % 2 == 0:
            x = 1; An = make(1)
        else:
            target = Lprefix_even.get(m + 1, 0) if m + 1 <= W else 0
            An = make(0)
            if An[0] != target: An = make(1); x = 1
            else: x = 0
        a.append(x)
        A[m + 1] = An
        L[m + 1] = An[0]
    return [L[k] for k in range(1, K + 1)], a
W = int(sys.argv[1]); K = int(sys.argv[2]); trials = int(sys.argv[3])
random.seed(5)
for tr in range(trials):
    g = {2 * i: random.getrandbits(1) for i in range(1, W // 2 + 1)}
    L, a = build(g, W, K)
    odd_tail = ''.join(str(L[k - 1]) for k in range(W + 1, K + 1) if k % 2 == 1)
    even_tail = ''.join(str(L[k - 1]) for k in range(W + 1, K + 1) if k % 2 == 0)
    f = ''.join(str(a[t]) for t in range(1, K, 2))
    print('L[1..W]=' + ''.join(map(str, L[:W])), ' odd tail:', odd_tail[:90], ' (even tail all 0:', set(even_tail) <= {'0'}, ')')
