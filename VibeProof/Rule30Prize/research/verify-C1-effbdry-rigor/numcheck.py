# Independent numerical check of C1 (array-based, not bit tricks).
# (1) identity a(t) | c(t) == a(t) | (c(t) & c(t+1)) on the true pattern
# (2) the left half driven by c' = c & c(t+1), restarted at several T, reproduces the true left half
# (3) the same identity/driven equivalence on random finite initial rows (identity is local)
import random, sys

def evolve(row0, N, W):
    # row index i <-> position i - W ; positions -W..W
    rows = [row0[:]]
    r = row0
    for _ in range(N):
        n = [0] * len(r)
        for i in range(len(r)):
            l = r[i - 1] if i > 0 else 0
            c = r[i]
            rr = r[i + 1] if i + 1 < len(r) else 0
            n[i] = l ^ (c | rr)
        rows.append(n)
        r = n
    return rows

def check(rows, W, N, Ts):
    col = lambda t, p: rows[t][p + W]
    ok_id = all((col(t, -1) | col(t, 0)) == (col(t, -1) | (col(t, 0) & col(t + 1, 0))) for t in range(N))
    ok_i = all(col(t, -1) == 1 - col(t + 1, 0) for t in range(N) if col(t, 0) == 1)
    ok_drv = True
    for T in Ts:
        # left half state as list over positions -W..-1 (index j <-> position j - W)
        s = [col(T, p) for p in range(-W, 0)]
        for t in range(T, N):
            d = col(t, 0) & col(t + 1, 0)
            n = [0] * W
            for j in range(W):
                p = j - W
                l = s[j - 1] if j > 0 else 0
                c = s[j]
                r = s[j + 1] if j + 1 < W else d
                n[j] = l ^ (c | r)
            s = n
            # compare with true row t+1
            for p in range(-W, 0):
                if s[p + W] != col(t + 1, p):
                    ok_drv = False
                    break
            if not ok_drv:
                break
    return ok_id, ok_i, ok_drv

N = int(sys.argv[1]) if len(sys.argv) > 1 else 600
W = N + 3
row0 = [0] * (2 * W + 1); row0[W] = 1
rows = evolve(row0, N + 1, W)
print('true pattern  N=%d:' % N, check(rows, W, N, [0, 1, 7, N // 3, N // 2]))

random.seed(12345)
for trial in range(5):
    row0 = [0] * (2 * W + 1)
    for p in range(-20, 21):
        row0[p + W] = random.randint(0, 1)
    rows = evolve(row0, N + 1, W)
    # boundary effects: keep the region well inside (pattern grows 1/step; W > N + 20 needed)
    print('random row %d:' % trial, check(rows, W, min(N, W - 25), [0, 5, 50]))
