# Sanity checks for the constraint-A reduction claim (a),(b),(c),(e) and the (d) wording.
import sys

def rule(l, m, r):
    return l ^ (m | r)

def simulate(N):
    # rows[t][p+N+2] for p in [-N-2, N+2]
    W = 2 * N + 5
    off = N + 2
    row = [0] * W
    row[off] = 1
    rows = [row]
    for t in range(N):
        new = [0] * W
        for i in range(1, W - 1):
            new[i] = rule(row[i - 1], row[i], row[i + 1])
        rows.append(new)
        row = new
    return rows, off

N = int(sys.argv[1]) if len(sys.argv) > 1 else 700
rows, off = simulate(N)
cell = lambda t, p: rows[t][p + off]
c = [cell(t, 0) for t in range(N + 1)]

# (a), (b), and the identity col_{-1}(t) = c(t+1) xor c(t) xor m(t), m(t) = col_1(t) * [c(t) = 0]
okA = all(cell(t, -1) == 1 - c[t + 1] for t in range(N) if c[t] == 1)
okB = all(cell(t, 1) == c[t + 1] ^ cell(t, -1) for t in range(N) if c[t] == 0)
okI = all(cell(t, -1) == c[t + 1] ^ c[t] ^ (cell(t, 1) & (1 - c[t])) for t in range(N))
print(f"(a) holds on S1 for t<{N}: {okA}; (b) holds on S0: {okB}; identity col-1 = c' ^ c ^ m: {okI}")

def realize_left(Rcol1, target, K):
    """Left half at the start time, positions -1..-K, determined by column 1 (Rcol1[t]) and the
    target column 0 (target[t]) via col_{-1}(t) = target(t+1) ^ (target(t) | col1(t)) and
    col_{-m-1}(t) = col_{-m}(t+1) ^ (col_{-m}(t) | col_{-m+1}(t))."""
    L = len(target) - 1
    colm1 = [target[t + 1] ^ (target[t] | Rcol1[t]) for t in range(L)]
    cols = {0: target[:L], 1: colm1}
    for m in range(1, K):
        a, b = cols[m], cols[m - 1]
        cols[m + 1] = [a[t + 1] ^ (a[t] | b[t]) for t in range(len(a) - 1)]
    return [cols[m][0] for m in range(1, K + 1)]

def driven_right_col1(Rstate, driver, steps, width):
    # right half positions 1..width (index 0 = position 1), driven at position 0 by driver
    row = Rstate[:] + [0] * (steps + 2)
    col1 = []
    for t in range(steps):
        col1.append(row[0])
        new = [0] * len(row)
        for i in range(len(row) - 1):
            l = driver[t] if i == 0 else row[i - 1]
            new[i] = rule(l, row[i], row[i + 1])
        row = new
    return col1

# (e)/uniqueness sanity: from time T, the actual right half driven by the ACTUAL c reproduces the
# actual left half at time T.
T = 200
K = 150
steps = N - T
Ract = [cell(T, p) for p in range(1, T + 2)]
col1_actual = driven_right_col1(Ract, c[T:], steps, T + 1)
assert col1_actual == [cell(T + s, 1) for s in range(steps)], "driven right half != actual right half"
Lreal = realize_left(col1_actual, c[T:T + steps], K)
Lact = [cell(T, -k) for k in range(1, K + 1)]
print(f"T={T}: realizer with actual target equals actual left half on -1..-{K}: {Lreal == Lact}")

# Periodic targets w = c[T,T+P): realizer vs actual left half
for P in (2, 3, 5, 8, 13):
    w = c[T:T + P]
    tgt = [w[s % P] for s in range(steps)]
    col1_w = driven_right_col1(Ract, tgt, steps, T + 1)
    Lw = realize_left(col1_w, tgt, K)
    first_diff = next((k + 1 for k in range(K) if Lw[k] != Lact[k]), None)
    # first t >= T with c(t+P) != c(t)
    wit = next((t for t in range(T, N - P) if c[t + P] != c[t]), None)
    print(f"P={P:2d}: realizer first differs from actual left half at position -{first_diff}; "
          f"first witness c(t+P)!=c(t) at t-T={wit - T}; realizer ones on -1..-{K}: {sum(Lw)}")

# R = 0, w = 0: the unique realizer is the all-white left half (left-finite)
Lz = realize_left([0] * 300, [0] * 300, 100)
print("R=0, w=0: realizer all white:", sum(Lz) == 0)
