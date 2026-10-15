# Independent check of stripe-tail convergence using the generic forward() on long rows.
import sys, itertools
sys.path.insert(0, '.')
from core import forward
def stripe_tail_row(inner, K, length):
    # inner: cells 1..K-1 ; cells >= K follow the stripe (1 at odd k)
    row = list(inner) + [1 if (k % 2 == 1) else 0 for k in range(K, length + 1)]
    return row
for K in (3, 5, 7, 9, 11, 13):
    maxt = 0
    for inner in itertools.product((0, 1), repeat=K - 1):
        T = 4 * K + 20
        row = stripe_tail_row(inner, K, K + 2 * T + 10)
        rows = forward(row, T)
        # first time the row equals the stripe on [1, K + T]  (cells beyond are affected by the truncated far end only after many steps)
        hit = None
        for t, r in enumerate(rows):
            if all(r[k - 1] == (k % 2) for k in range(1, K + 6)):
                hit = t; break
        if hit is None: print('K', K, 'inner', inner, 'did not converge within', T); break
        maxt = max(maxt, hit)
    print('K=%d max convergence time %d' % (K, maxt))
