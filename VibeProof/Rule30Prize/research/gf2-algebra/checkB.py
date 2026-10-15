# Numerical checks of the identities used in the degree proof, on random inputs:
# (i)  d/dx_t Phi_t = prod_{s<t} (1 + cell(s, t-1-s))
# (ii) d/dx_{-t+1} Phi_t = t + sum_{s<t} cell(s, s-t+2)  (mod 2)
import random
def evolve(x, t):  # x: dict pos->bit on [-t,t]; returns list of rows as dicts
    rows = [dict(x)]
    for s in range(1, t + 1):
        prev = rows[-1]; cur = {}
        for p in range(-t + s, t - s + 1):
            cur[p] = prev[p - 1] ^ (prev[p] | prev[p + 1])
        rows.append(cur)
    return rows
random.seed(1)
bad = 0
for trial in range(3000):
    t = random.randint(1, 9)
    x = {p: random.randint(0, 1) for p in range(-t, t + 1)}
    r = evolve(x, t)
    for var, formula in ((t, 'i'), (-t + 1, 'ii')):
        y = dict(x); y[var] ^= 1
        d = r[t][0] ^ evolve(y, t)[t][0]
        if formula == 'i':
            pred = 1
            for s in range(t): pred &= 1 ^ r[s][t - 1 - s]
        else:
            pred = t & 1
            for s in range(t): pred ^= r[s][s - t + 2]
        if d != pred: bad += 1
print("identity failures:", bad)
