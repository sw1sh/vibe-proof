# If step(y) agrees with the stripe from L (L>=1), y(k+1) = s(k) ^ (y(k) | y(k-1)) for k >= L.
# Find, over all (L parity, y(L-1), y(L)), the first m such that y agrees with s from L+m (pair agreement then propagates).
s = lambda k: k % 2
worst = 0
for Lp in (0, 1):
    for a in (0, 1):
        for b in (0, 1):
            L = 10 + Lp
            y = {L - 1: a, L: b}
            for k in range(L, L + 12):
                y[k + 1] = s(k) ^ (y[k] | y[k - 1])
            # first k0 >= L such that y agrees with s on [k0, L+12]
            k0 = min(k for k in range(L - 1, L + 13) if all(y[j] == s(j) for j in range(k, L + 13)))
            worst = max(worst, k0 - L)
            print(f"L parity {Lp}, (y(L-1), y(L)) = ({a},{b}): y agrees with s from L+{k0 - L}")
print("worst offset:", worst)
