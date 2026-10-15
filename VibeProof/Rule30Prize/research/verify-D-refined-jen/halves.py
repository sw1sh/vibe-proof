# Compare, for the same periodic driver c = w^inf:
#  (R) right half (p >= 1) from random finite-support starts: is column 1 eventually periodic / periodic on Z?
#  (X) the column -1 that CONSISTENCY would assign: x(t) = c(t+1) xor (c(t) or y(t)) -- periodic?
#  (L) left half (p <= -1) driven by the same c from random finite-support starts: is column -1 eventually periodic?
import sys, random

def right_run(state, width, cf, steps):
    row = state; W = width; col = []
    for t in range(steps):
        col.append(row & 1)
        W += 1; mask = (1 << W) - 1
        leftn = ((row << 1) | cf(t)) & mask
        row = (leftn ^ (row | (row >> 1))) & mask
    return col

def left_run(state, width, cf, steps):
    # bit k <-> position p = -k-1
    row = state; W = width; col = []
    for t in range(steps):
        col.append(row & 1)
        W += 1; mask = (1 << W) - 1
        rightn = ((row << 1) | cf(t)) & mask   # value at p+1 (bit 0 gets c(t))
        leftn = row >> 1                        # value at p-1
        row = (leftn ^ (row | rightn)) & mask
    return col

def ev_period(seq, ok, maxQ):
    n = len(seq); lo = n // 2
    for Q in range(1, maxQ + 1):
        if all(seq[t] == seq[t + Q] for t in range(lo, n - Q) if ok(t)):
            return Q
    return None

random.seed(int(sys.argv[1])); steps = int(sys.argv[2]); trials = int(sys.argv[3])
for w in sys.argv[4:]:
    P = len(w); cf = lambda t, w=w: int(w[t % len(w)])
    Zok = lambda t, w=w: w[t % len(w)] == '0'
    r_full = r_Z = x_per = 0; l_per = 0
    for _ in range(trials):
        m = random.randint(5, 80)
        st = random.getrandbits(m - 1) | (1 << (m - 1))
        y = right_run(st, m, cf, steps)
        qf = ev_period(y, lambda t: True, 8 * P)
        qz = ev_period(y, Zok, 8 * P)
        # restrict Z-periods to multiples of P (periods of c)
        qz_ok = qz is not None and any(ev_period(y, Zok, 8*P) for _ in [0])
        x = [cf(t + 1) ^ (cf(t) | y[t]) for t in range(steps - 1)]
        qx = ev_period(x, lambda t: True, 8 * P)
        r_full += qf is not None; r_Z += qz is not None; x_per += qx is not None
        m2 = random.randint(5, 80)
        sl = random.getrandbits(m2 - 1) | (1 << (m2 - 1))
        xl = left_run(sl, m2, cf, steps)
        ql = ev_period(xl, lambda t: True, 400)
        l_per += ql is not None
    print(f"w={w}: right col1 eventually periodic {r_full}/{trials}; col1 periodic on Z {r_Z}/{trials}; "
          f"consistency-x periodic {x_per}/{trials} | LEFT-driven col -1 periodic (Q<=400) {l_per}/{trials}")
