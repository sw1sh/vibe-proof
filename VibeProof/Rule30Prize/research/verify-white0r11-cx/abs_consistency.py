# Check that observed (class, output, next class) triples from simulation lie inside the computed abstraction graph,
# and that for 00000011 column 1 is 16-periodic from time 33 (phase 0) for random/adversarial initial configs.
import sys, random, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-white0r11-cx')
from z3ellabs import analyze

def int_steps(r, R, P, steps, collect):
    w = [0] * r + [1, 1]
    for t in range(steps):
        collect(t, R)
        R = ((R << 1) | w[t % P]) ^ (R | (R >> 1))
    collect(steps, R)
    return R

def cls(R, L):
    if R == 0: return L + 1
    low = (R & -R).bit_length() - 1   # index of first 1 -> column low+1
    return low if low <= L else L + 1

def true_row_right(T):
    # rule 30 single seed, full row as int with offset; returns right half (columns >= 1) as int R (bit p-1 = column p)
    off = T + 1
    row = 1 << off
    for t in range(T):
        row = (row << 1) ^ (row | (row >> 1))
    # orientation: (row << 1) puts column p-1's value at bit position of column p => bit index increases with p? check:
    # with this update, bit b's new value = bit(b-1) ^ (bit b | bit b+1): left neighbour = lower bit => column p <-> bit off+p
    return row >> (off + 1), (row >> off) & 1

rng = random.Random(11)
t0 = time.time()
for r in range(6, 13):
    w = '0' * r + '11'; P = len(w); L = P + 12
    nodes = analyze(w, L)
    viol = 0; obs = 0
    for trial in range(400):
        kind = trial % 4
        if kind == 0:
            T = rng.randint(1, 400); R, c0 = true_row_right(T)
        elif kind == 1:
            n = rng.randint(1, 80); R = rng.getrandbits(n)
        elif kind == 2:
            R = rng.getrandbits(2000)   # wide random ("infinite")
        else:
            R = (rng.getrandbits(60) << (rng.randint(0, 40)))
        hist = []
        int_steps(r, R, P, P * 30, lambda t, RR: hist.append(RR))
        for k in range(30):
            a = k * P
            c = cls(hist[a], L)
            out = tuple((hist[a + i] & 1) for i in range(P))
            nxt = cls(hist[a + P], L)
            obs += 1
            outs, nexts = nodes[c]
            if out not in outs or nxt not in nexts:
                viol += 1
                if viol <= 3: print("VIOLATION r", r, "kind", kind, "k", k, "class", c, "out", out, "next", nxt, "allowed", outs, nexts)
    print(f"r={r}: observed transitions {obs}, violations {viol}", flush=True)
# true_row_right sanity: column 0 sequence equals center prefix
cs = [true_row_right(T)[1] for T in range(12)]
print("center via true_row_right:", cs)

# r = 6 forced 16-periodicity from 33
w = '00000011'; P = 8; bad = 0
for trial in range(3000):
    kind = trial % 4
    if kind == 0:
        T = rng.randint(1, 300); R, _ = true_row_right(T)
    elif kind == 1:
        R = rng.getrandbits(rng.randint(1, 100))
    elif kind == 2:
        R = rng.getrandbits(400)
    else:
        R = rng.getrandbits(30) << rng.randint(0, 60)
    col = []
    int_steps(6, R, P, 33 + 16 + 200, lambda t, RR: col.append(RR & 1))
    if any(col[n] != col[n + 16] for n in range(33, 33 + 200)):
        bad += 1
print("r=6: random inits violating 16-periodicity from n=33:", bad, " time", round(time.time() - t0, 1))
