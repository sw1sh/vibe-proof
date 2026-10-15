# Additive conserved quantities mod 2 of rule 30 and rule 30^2 (on finite configurations of Z).
import sys, itertools, random
def r30(x):
    n = len(x); xx = (0, 0) + x + (0, 0)
    return tuple(xx[i + 1] ^ (xx[i] | xx[i - 1]) for i in range(1, n + 3))
def counts(x, r):
    xx = (0,) * (r - 1) + x + (0,) * (r - 1); c = {}
    for k in range(len(xx) - r + 1):
        p = xx[k:k + r]
        if any(p): c[p] = c.get(p, 0) ^ 1
    return c
def analyze(r, steps, L, seed=1):
    pats = [p for p in itertools.product((0, 1), repeat=r) if any(p)]
    idx = {p: i for i, p in enumerate(pats)}
    n = len(pats)
    basis = {}  # pivot -> int bitmask row
    rng = random.Random(seed)
    for trial in range(40000):
        ln = rng.randint(1, L)
        x = tuple([1] + [rng.getrandbits(1) for _ in range(ln - 2)] + ([1] if ln > 1 else []))
        y = x
        for _ in range(steps): y = r30(y)
        row = 0
        for p, v in counts(y, r).items():
            if v: row ^= 1 << idx[p]
        for p, v in counts(x, r).items():
            if v: row ^= 1 << idx[p]
        while row:
            piv = row.bit_length() - 1
            if piv in basis: row ^= basis[piv]
            else: basis[piv] = row; break
    return n, len(basis)
for steps in (1, 2):
    for r in range(1, int(sys.argv[1]) + 1):
        n, rk = analyze(r, steps, int(sys.argv[2]))
        triv = 2 ** (r - 1) - 1
        print(f"GF(2): rule30^{steps} r={r}: unknowns {n}, rank {rk}, solutions {n - rk}, coboundaries {triv} -> nontrivial {n - rk - triv}")
        sys.stdout.flush()
