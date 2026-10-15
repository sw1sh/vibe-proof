# For Jen's class (f(000)=0, left-permutive with f(001)=1 or right-permutive with f(100)=1):
# rules 30, 86, 90, 150, 154, 210. From a single seed, heuristically test which columns in
# [-R, R] look eventually periodic (period <= PMAX holding on the last half of N steps).
# Numerical evidence only.
N = 4000; R = 12; PMAX = 300
def evolve(rule, N):
    width = 2 * N + 3
    row = [0] * width; off = N + 1; row[off] = 1
    cols = {p: [] for p in range(-R, R + 1)}
    for t in range(N):
        for p in cols: cols[p].append(row[off + p])
        new = [0] * width
        for i in range(1, width - 1):
            new[i] = (rule >> (4 * row[i - 1] + 2 * row[i] + row[i + 1])) & 1
        row = new
    return cols
def looks_periodic(seq):
    half = len(seq) // 2
    for P in range(1, PMAX + 1):
        if all(seq[t] == seq[t + P] for t in range(half, len(seq) - P)):
            return P
    return None
for rule in (30, 86, 90, 150, 154, 210):
    cols = evolve(rule, N)
    res = {p: looks_periodic(cols[p]) for p in cols}
    per = {p: P for p, P in res.items() if P is not None}
    print(rule, 'eventually periodic-looking columns (col: period):', per, '| col0 first 16:', cols[0][:16])
