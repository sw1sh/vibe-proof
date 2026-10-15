# Driven diagrams: column 0 is prescribed (random before T, period word w from T on, random phase),
# columns 1..W at time 0 are random; the right half evolves by rule 30 with column 0 as left input;
# column -1 is then forced by cell_left: cell(t,-1) = c(t+1) xor (c(t) or cell(t,1)).
# Check: (i) key: t >= T+9+P, c(t)=0  =>  cell(t,1) = not c(t-1)
#        (ii) column -1 is P-periodic on [T+9+P+1, N-P)
#        (iii) the hypothesis of C3 holds (sanity: words have cyclic 1-runs >= 9)
import random, sys

def rule(a, b, c): return a ^ (b | c)

def cyc_runs(w):
    if all(w): return None
    k = w.index(0); r = w[k:] + w[:k]
    runs, cur = [], 0
    for x in r + [0]:
        if x: cur += 1
        else:
            if cur: runs.append(cur)
            cur = 0
    return runs

def simulate(c, N, rng):
    W = N + 3
    right = [rng.randint(0, 1) for _ in range(W)]   # columns 1..W at time 0
    col1 = []; col2 = []
    for t in range(N + 1):
        col1.append(right[0]); col2.append(right[1] if len(right) > 1 else None)
        left = [c[t]] + right[:-1]
        right = [rule(left[i], right[i], right[i+1]) for i in range(len(right) - 1)]
    colm1 = [c[t+1] ^ (c[t] | col1[t]) for t in range(N)]
    return col1, col2, colm1

def hyp_holds(c, T, N):
    for t in range(T + 9, N):
        if c[t] == 0 and c[t-1] == 1 and not all(c[t-1-i] for i in range(9)):
            return False
    return True

def trial(w, T, phase, rng, extraP=6):
    P = len(w)
    N = T + 9 + P + 1 + extraP * P + 30
    c = [rng.randint(0, 1) for _ in range(T)] + [w[(t - T + phase) % P] for t in range(T, N + 2)]
    col1, col2, colm1 = simulate(c, N, rng)
    key_viol = [t for t in range(T + 9 + P, N) if c[t] == 0 and col1[t] != 1 - c[t-1]]
    per_viol = [t for t in range(T + 9 + P + 1, N - P) if colm1[t + P] != colm1[t]]
    # earliest start of P-periodicity of column -1 (within the computed range)
    t0 = N - P
    while t0 > 0 and colm1[t0 - 1 + P] == colm1[t0 - 1]:
        t0 -= 1
    return hyp_holds(c, T, N), key_viol, per_viol, t0, T + 9 + P + 1

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
words = []
fixed = ["0"+"1"*9, "1"*9+"0", "0"*5+"1"*9, "0"*30+"1"*9, "0"+"1"*9+"0"+"1"*12,
         "0"*5+"1"*10+"0"+"1"*9, "1"*5+"0"+"1"*5, "1"*4+"00"+"1"*5, "0"+"1"*20,
         "00"+"1"*9+"000"+"1"*11+"0"+"1"*9, "1"*9, "0"*3+"1"*40]
words += [[int(ch) for ch in s] for s in fixed]
# random words whose cyclic 1-runs are all >= 9
while len(words) < 400:
    P = rng.randint(1, 60)
    w = [rng.randint(0, 1) for _ in range(P)]
    r = cyc_runs(w)
    if r is None:
        continue
    # lengthen short runs to >= 9 by inserting ones
    out = []
    i = 0
    s = "".join(map(str, w))
    parts = s.split("0")
    s2 = "0".join(p if (len(p) == 0 or len(p) >= 9) else "1" * rng.randint(9, 14) for p in parts)
    w2 = [int(ch) for ch in s2]
    r2 = cyc_runs(w2)
    if not r2 or min(r2) < 9:
        continue
    words.append(w2)

tot = hyp_bad = keyb = perb = 0
worst = 0
for w in words:
    P = len(w)
    r = cyc_runs(w)
    assert r is None or min(r) >= 9, w
    for _ in range(4):
        T = rng.randint(0, 40)
        phase = rng.randrange(P)
        hyp, kv, pv, t0, bound = trial(w, T, phase, rng)
        tot += 1
        if not hyp: hyp_bad += 1
        if kv: keyb += 1; print("KEY VIOLATION", "".join(map(str, w)), T, phase, kv[:5])
        if pv: perb += 1; print("PERIODICITY VIOLATION", "".join(map(str, w)), T, phase, pv[:5])
        worst = max(worst, t0 - (T + P))  # how late periodicity starts relative to T+P
print(f"trials={tot} hypothesis-fails={hyp_bad} key-violations={keyb} periodicity-violations={perb}")
print("max over trials of (observed start of col -1 periodicity) - (T+P):", worst, "(proof bound: 10)")
