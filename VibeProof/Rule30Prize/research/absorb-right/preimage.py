# Lock permanence test via backward preimages of the bad event.
# Locked columns 1..m with per-phase values L[j][r] (j=1..m, r in Z/Q).
# Chaos region = columns m+1, m+2, ...; boundary value at time t (phase r) is a = L[m][r].
# Bad event at phase r (L[m][r] == 0): x(t,m+1) != beta_r where beta_r = L[m][r+1] ^ L[m-1][r].
# B = set of prefixes (strings over '01', starting at column m+1) at phase r that are bad.
# Preimage at phase r-1 with boundary a = L[m][r-1].
import sys
sys.path.insert(0, '.')
from lockinfo import lock_table

def preimages(z, a):
    # all y (len(z)+1) with z1 = a ^ (y1|y2), z_i = y_{i-1} ^ (y_i | y_{i+1})
    l = len(z); res = []
    zb = [int(ch) for ch in z]
    def rec(y):
        i = len(y)  # we have y_1..y_i (0-based y[0..i-1]); next to choose y_{i+1}
        if i == l + 1:
            res.append(''.join(map(str, y))); return
        for b in (0, 1):
            yy = y + [b]
            # check constraint z_{i} (1-based) which involves y_{i-1}, y_i, y_{i+1}: index i-1 in zb, needs len(yy) == i+1 >= 2
            if len(yy) >= 2:
                k = len(yy) - 1  # 1-based index of z constraint = k (needs y_{k-1}, y_k, y_{k+1})
                left = a if k == 1 else yy[k - 2]
                if zb[k - 1] != (left ^ (yy[k - 1] | yy[k])): continue
            rec(yy)
    rec([])
    return res

def test(w, Q, seed=3, maxn=40, cap=200000, verbose=True):
    tab = lock_table(w, 0, 1000, seed, 20000, 40, Q, 6000)
    m = 0
    while m < len(tab) and '*' not in tab[m]: m += 1
    L = {j + 1: [int(ch) for ch in tab[j]] for j in range(m)}
    if verbose:
        print(f"{w}: locked columns 1..{m}, Q={Q}, interface column {m}: {tab[m-1]}")
    ok = True
    for r in range(Q):
        if L[m][r] == 1: continue
        beta = L[m][(r + 1) % Q] ^ (L[m - 1][r] if m >= 2 else int(w[r % len(w)]))
        bad = {str(1 - beta)}
        ph = r; n = 0; sizes = []
        while bad and n < maxn:
            a = L[m][(ph - 1) % Q]
            nb = set()
            for z in bad:
                nb.update(preimages(z, a))
            bad = nb; ph = (ph - 1) % Q; n += 1; sizes.append(len(bad))
            if len(bad) > cap: break
        if verbose: print(f"  bad event phase {r} (need x(m+1)={beta}): preimage sizes {sizes}")
        if bad: ok = False
    return ok

if __name__ == '__main__':
    for w in sys.argv[2:]:
        test(w, int(sys.argv[1]))
