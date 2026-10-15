# Faster: incremental rank with early stop once rank reaches the expected 2^(r-1) (unknowns 2^r - 1, trivial dim 2^(r-1)-1).
import sys, itertools, random
P = 2**61 - 1
def r30(x):
    n = len(x); xx = (0, 0) + x + (0, 0)
    return tuple(xx[i + 1] ^ (xx[i] | xx[i - 1]) for i in range(1, n + 3))
def counts(x, r):
    xx = (0,) * (r - 1) + x + (0,) * (r - 1); c = {}
    for k in range(len(xx) - r + 1):
        p = xx[k:k + r]
        if any(p): c[p] = c.get(p, 0) + 1
    return c
def analyze(r, steps, L, seed=1):
    pats = [p for p in itertools.product((0, 1), repeat=r) if any(p)]
    idx = {p: i for i, p in enumerate(pats)}
    n = len(pats); target = n - (2 ** (r - 1) - 1)
    basis = {}  # pivot col -> row (reduced)
    rng = random.Random(seed)
    tried = 0
    while len(basis) < target and tried < 200000:
        ln = rng.randint(1, L)
        x = tuple([1] + [rng.getrandbits(1) for _ in range(ln - 2)] + ([1] if ln > 1 else []))
        y = x
        for _ in range(steps): y = r30(y)
        row = [0] * n
        for p, v in counts(y, r).items(): row[idx[p]] += v
        for p, v in counts(x, r).items(): row[idx[p]] -= v
        row = [v % P for v in row]
        tried += 1
        # reduce
        for c in sorted(basis):
            if row[c]:
                f = row[c]; b = basis[c]
                row = [(a - f * bb) % P for a, bb in zip(row, b)]
        piv = next((c for c in range(n) if row[c]), None)
        if piv is None: continue
        inv = pow(row[piv], P - 2, P); row = [(v * inv) % P for v in row]
        for c in list(basis):
            if basis[c][piv]:
                f = basis[c][piv]; basis[c] = [(a - f * bb) % P for a, bb in zip(basis[c], row)]
        basis[piv] = row
    return n, len(basis), target, tried
for steps in (1, 2):
    for r in range(1, int(sys.argv[1]) + 1):
        n, rk, target, tried = analyze(r, steps, int(sys.argv[2]))
        print(f"rule30^{steps} r={r}: unknowns {n}, rank found {rk} (max possible {target}) after {tried} random configs -> nontrivial conserved dim {n - rk - (2**(r-1)-1)}")
        sys.stdout.flush()
