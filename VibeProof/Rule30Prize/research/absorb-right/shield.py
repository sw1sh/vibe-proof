# Shield test for a periodic column sigma (period Q) at position m (left boundary for columns >= m+1).
# For each zero-phase r of sigma, and each b in {0,1}: is "x(t,m+1) = b" reachable at phase r after
# n steps of the column-m pattern?  Backward preimage sets of prefixes (columns m+1, m+2, ...).
import sys
sys.path.insert(0, '.')

def preimages(z, a):
    l = len(z); res = []
    zb = [int(ch) for ch in z]
    def rec(y):
        if len(y) == l + 1:
            res.append(''.join(map(str, y))); return
        for b in (0, 1):
            yy = y + [b]
            if len(yy) >= 2:
                k = len(yy) - 1
                left = a if k == 1 else yy[k - 2]
                if zb[k - 1] != (left ^ (yy[k - 1] | yy[k])): continue
            rec(yy)
    rec([])
    return res

def depth_to_empty(sigma, r, b, maxn=40, cap=300000):
    Q = len(sigma); s = [int(ch) for ch in sigma]
    bad = {str(b)}; ph = r; n = 0
    while bad and n < maxn:
        a = s[(ph - 1) % Q]
        nb = set()
        for z in bad: nb.update(preimages(z, a))
        bad = nb; ph = (ph - 1) % Q; n += 1
        if len(bad) > cap: return None
    return n if not bad else None

def shield(sigma, maxn=40):
    Q = len(sigma); res = {}
    for r in range(Q):
        if sigma[r] == '1': continue
        d0 = depth_to_empty(sigma, r, 0, maxn); d1 = depth_to_empty(sigma, r, 1, maxn)
        if d1 is not None: res[r] = (0, d1)     # value 1 unreachable -> forced 0
        elif d0 is not None: res[r] = (1, d0)   # forced 1
        else: return None
    return res

if __name__ == '__main__':
    for Q in range(2, int(sys.argv[1]) + 1):
        sigma = '1' * (Q - 1) + '0'
        print(Q, sigma, shield(sigma), flush=True)
