# "Equivalently": for c = (arbitrary prefix of length T) + w^infty (any phase), the Lean hypothesis
#   hruns: for all t >= T+9, c(t)=0 and c(t-1)=1  =>  c(t-1..t-9) = 1
# holds  <=>  w has no 1->0 cyclic transition (w constant) or every cyclic maximal 1-run of w has length >= 9.
import random, itertools

def cyc_min_run(w):
    if all(w) or not any(w):
        return None
    k = w.index(0); r = w[k:] + w[:k]
    runs, cur = [], 0
    for x in r + [0]:
        if x: cur += 1
        else:
            if cur: runs.append(cur)
            cur = 0
    return min(runs)

def hruns(c, T, horizon):
    for t in range(T + 9, horizon):
        if c[t] == 0 and c[t-1] == 1:
            if not all(c[t-1-i] for i in range(9)):
                return False
    return True

rng = random.Random(3)
mismatch = 0; tot = 0
# exhaustive over all words of length <= 14, random prefixes/phases; random longer words too
words = [list(w) for P in range(1, 15) for w in itertools.product((0, 1), repeat=P)]
words += [[rng.randint(0, 1) for _ in range(rng.randint(15, 40))] for _ in range(3000)]
for w in words:
    P = len(w)
    m = cyc_min_run(w)
    expected = (m is None) or (m >= 9)
    for _ in range(2):
        T = rng.randint(0, 12)
        phase = rng.randrange(P)
        H = T + 9 + 3 * P + 12
        c = [rng.randint(0, 1) for _ in range(T)] + [w[(t - T + phase) % P] for t in range(T, H + 1)]
        got = hruns(c, T, H)
        tot += 1
        if got != expected:
            mismatch += 1
            if mismatch < 5: print("MISMATCH", "".join(map(str, w)), T, phase, got, expected)
print(f"cases={tot} mismatches={mismatch}")
for s in ["0"*3 + "1"*9, "0"*1 + "1"*9 + "0" + "1"*12, "0"*5 + "1"*10 + "0" + "1"*9]:
    w = [int(x) for x in s]
    print(s, "min cyclic 1-run:", cyc_min_run(w))
