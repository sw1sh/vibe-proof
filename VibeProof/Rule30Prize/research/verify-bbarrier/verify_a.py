# Independent check of consequence (a) of B_barrier.
# Driven left half: cells p = -1, -2, ...; column 0 is the driver c(t).
# Forced constraint (from column-0 consistency c(t+1) = x(t) xor (c(t) or cell(t,1))):
#   if c(t) = 1 then x(t) = cell(t,-1) = not c(t+1).
# Claim (a): #{edge-structured states at time T (cell -T black, white beyond) meeting the forced
# constraints on [T, 2T-2]} = 2^z, z = #{t in [T, 2T-2] : c(t) = 0}.
import random, itertools

def rule(a, b, d):
    return a ^ (b | d)

def x_seq(state, T, c, tmax):
    """state: dict p -> bit for p in [-T, -1] (others 0). Returns {t: cell(t,-1)} for t in [T, tmax]."""
    W = T + (tmax - T) + 3            # enough room on the left
    row = [0] * (W + 1)               # row[i] = cell at position -i, i = 1..W ; row[0] unused
    for p, v in state.items():
        row[-p] = v
    out = {}
    for t in range(T, tmax + 1):
        out[t] = row[1]
        new = [0] * (W + 1)
        for i in range(1, W + 1):
            left = row[i + 1] if i + 1 <= W else 0
            right = row[i - 1] if i - 1 >= 1 else c(t)   # position 0 is the driver
            new[i] = rule(left, row[i], right)
        row = new
    return out

def count_ok(T, c):
    n_ok = 0
    for bits in itertools.product((0, 1), repeat=T - 1):
        st = {-(i + 1): bits[i] for i in range(T - 1)}
        st[-T] = 1
        xs = x_seq(st, T, c, 2 * T - 2)
        ok = all(xs[t] == 1 - c(t + 1) for t in range(T, 2 * T - 1) if c(t) == 1)
        n_ok += ok
    return n_ok

random.seed(12345)
bad = 0
trials = 0
for T in range(1, 12):
    for _ in range(6):
        P = random.randint(1, 6)
        w = [random.randint(0, 1) for _ in range(P)]
        if random.random() < 0.15:
            w = [1] * P                      # include all-ones words
        ph = random.randrange(P)
        c = lambda t, w=w, ph=ph, P=P, T=T: w[(t - T + ph) % P] if t >= T else 1
        z = sum(1 for t in range(T, 2 * T - 1) if c(t) == 0)
        got = count_ok(T, c)
        trials += 1
        if got != 2 ** z:
            bad += 1
            print("MISMATCH", T, w, ph, got, 2 ** z)
print("trials", trials, "mismatches", bad)

# sanity: the forced constraint really holds in the actual rule 30 pattern
def rows(N):
    r = {0: 1}
    out = [dict(r)]
    for t in range(N):
        nr = {}
        for p in range(-t - 1, t + 2):
            nr[p] = rule(r.get(p - 1, 0), r.get(p, 0), r.get(p + 1, 0))
        r = nr
        out.append(r)
    return out
R = rows(600)
viol = sum(1 for t in range(600) if R[t][0] == 1 and R[t].get(-1, 0) != 1 - R[t + 1][0])
print("actual pattern: violations of 'c(t)=1 => cell(t,-1)=not c(t+1)' for t<600:", viol)
