# Heavier stress test of every intermediate step of Theorem B' on explicit simulations.
# Right half (columns 1..W) at time 0 = random / real-rule-30 rows; column 0 driven by (1^r u)^inf.
# Checks, for every k with e_k = r + kP inside the horizon:
#  step 1: row at e_k, columns 1..2*j0, equals (01)^j0         (Lemma A*)
#  step 3: column-1 values at e_k..e_k+|u|+9 equal the canonical traceCol1(drv u, wb ++ 0-tail)
#  step 4: column-1 values at e_k+s for |u|+9 <= s < P are 0     (Lemma A)
#  step 5: column 1 is P-periodic from time r                    (conclusion)
import itertools, random, sys, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-bprime-cx')
from det_check import min_j0, traceCol1, drv, wb

def evolve_rows(word, init_cols, N):
    """full rows (as lists) of the right half for times 0..N with shrinking cone."""
    P = len(word)
    rows = [list(init_cols)]
    row = list(init_cols)
    for t in range(N):
        l = word[t % P]
        new = []
        for i in range(len(row) - 1):
            left = l if i == 0 else row[i - 1]
            new.append(left ^ (row[i] | row[i + 1]))
        row = new
        rows.append(row)
    return rows

def real_rule30_rows(T):
    W = 2 * T + 5; off = T + 2
    row = [0] * W; row[off] = 1
    out = [row]
    for t in range(T):
        new = [0] * W
        for p in range(1, W - 1):
            new[p] = row[p - 1] ^ (row[p] | row[p + 1])
        row = new; out.append(row)
    return out, off

def blocks(maxlen=7):
    for n in range(1, maxlen + 1):
        for bits in itertools.product((0, 1), repeat=n):
            if bits[0] == 0 and bits[-1] == 0:
                yield bits

if __name__ == '__main__':
    seed = int(sys.argv[1]); mode = sys.argv[2]; budget = float(sys.argv[3])
    random.seed(seed)
    t0 = time.time()
    real = None
    if mode == 'real':
        real, off = real_rule30_rows(400)
    viol = {'s1': 0, 's3': 0, 's4': 0, 's5': 0}
    runs = 0
    bl = list(blocks())
    while time.time() - t0 < budget:
        u = random.choice(bl)
        j0 = min_j0(u)
        r = max(9, 9 * j0) + random.choice([0, 0, 1, 2, 3, 7, 20])
        word = [1] * r + list(u)
        P = len(word)
        N = 4 * P + 30
        if mode == 'real':
            t1 = random.randrange(0, 400 - N - 2) if 400 - N - 2 > 0 else 0
            if 400 - N - 2 <= 0:
                continue
            init = [real[t1][off + 1 + i] for i in range(N + 1)]
        else:
            init = [random.randint(0, 1) for _ in range(N + 1)]
        rows = evolve_rows(word, init, N)
        col1 = [rows[t][0] for t in range(N + 1)]
        canon = traceCol1(drv(u), wb(j0) + [0] * (len(u) + 10 - 2 * j0))
        k = 0
        while True:
            e = r + k * P
            if e + P > N:
                break
            if rows[e][:2 * j0] != wb(j0):
                viol['s1'] += 1
            if tuple(col1[e:e + len(u) + 10]) != canon:
                viol['s3'] += 1
            for s in range(len(u) + 9, P):
                if col1[e + s] != 0:
                    viol['s4'] += 1; break
            k += 1
        for t in range(r, N - P + 1):
            if col1[t + P] != col1[t]:
                viol['s5'] += 1; break
        runs += 1
    print(f'seed={seed} mode={mode} runs={runs} violations={viol}')
