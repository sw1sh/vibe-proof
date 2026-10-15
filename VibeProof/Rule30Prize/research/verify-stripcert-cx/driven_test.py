# Semantic falsification attempts for the strip-certificate soundness claim.
# (1) rowR_succ identity on true rule 30 (cell(t,p), single black cell).
# (2) what-if: true rule-30 right half at time T0, then column 0 := w^inf (any phase), right half evolves
#     by rule 30 (exact, wide array). Check strip path is a graph path, cert rank non-increasing,
#     and column 1 at white times eventually periodic with period m*P (white-masked).
# (3) random right halves + random/adversarial environment x at column b+1 (pure graph walks).
import sys, random
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-stripcert-cx')
from decode_check import C, parse_inst

def rule30_rows(T, extra=0):
    # rows[t] = dict over positions -t-1..t+1 (list with offset)
    W = T + 2 + extra
    row = [0] * (2 * W + 1); row[W] = 1
    rows = [row[:]]
    for t in range(T):
        new = [0] * (2 * W + 1)
        for p in range(1, 2 * W):
            new[p] = row[p - 1] ^ (row[p] | row[p + 1])
        row = new; rows.append(row[:])
    return rows, W

def lin3(l): return [l[i] ^ (l[i + 1] | l[i + 2]) for i in range(len(l) - 2)]

def test_rowR_succ(T=300, bmax=12):
    rows, W = rule30_rows(T + 1)
    bad = 0
    for t in range(T):
        for b in range(1, bmax + 1):
            strip = [rows[t][W + p] for p in range(1, b + 1)]
            nxt = [rows[t + 1][W + p] for p in range(1, b + 1)]
            if lin3([rows[t][W]] + strip + [rows[t][W + b + 1]]) != nxt: bad += 1
    return bad

def drive(cert, init_right, phase0, steps, env=None, rng=None):
    """init_right: list of columns 1..L at time T0 (L >= b). Column 0 = w[(phase0 + k) % P] at step k.
    If env is None: exact rule 30 on the array (cells beyond L treated as 0 -- still a valid environment).
    If env == 'random': only the strip of width b is kept, column b+1 random each step.
    Returns list of (phi, strip tuple) for k = 0..steps."""
    P = cert.P; b = cert.b; w = cert.w
    path = []
    if env is None:
        row = list(init_right)
        for k in range(steps + 1):
            phi = (phase0 + k) % P
            path.append((phi, tuple(bool(x) for x in row[:b])))
            c = int(w[phi])
            full = [c] + row + [0, 0]
            row = [full[i] ^ (full[i + 1] | full[i + 2]) for i in range(len(row))]
    else:
        row = list(init_right[:b])
        for k in range(steps + 1):
            phi = (phase0 + k) % P
            path.append((phi, tuple(bool(x) for x in row)))
            c = int(w[phi]); x = rng.randrange(2)
            row = lin3([c] + row + [x])
    return path

def check_path(cert, path):
    P = cert.P
    # graph-edge check
    for k in range(len(path) - 1):
        phi, s = path[k]; phi2, s2 = path[k + 1]
        ok = any(lin3([int(cert.w[phi])] + list(map(int, s)) + [x]) == list(map(int, s2)) for x in (0, 1))
        if not ok or phi2 != (phi + 1) % P: return 'not a graph path at %d' % k
    ranks = [cert.rk(phi, list(s)) for phi, s in path]
    for k in range(len(ranks) - 1):
        if ranks[k + 1] > ranks[k]: return 'rank increased at %d' % k
    # last rank change
    last = max([k + 1 for k in range(len(ranks) - 1) if ranks[k + 1] != ranks[k]] + [0])
    r = ranks[-1]; m = cert.m(r); Q = m * P
    # outputs follow u at white times after stabilization
    for k in range(last, len(path)):
        phi, s = path[k]
        if not cert.w[phi]:
            if s[0] != cert.u(r, cert.ps(phi, list(s))): return 'output mismatch at %d' % k
    # masked periodicity with period Q after stabilization
    for k in range(last, len(path) - Q):
        phi, s = path[k]
        if not cert.w[phi] and path[k + Q][1][0] != s[0]: return 'masked period fails at %d' % k
    return ('ok', last, r, m)

if __name__ == '__main__':
    print('rowR_succ mismatches:', test_rowR_succ())
    names = sys.argv[1:]
    rng = random.Random(12345)
    T = 400
    rows, W = rule30_rows(T, extra=2000)
    for name in names:
        cert = C(parse_inst(name))
        stats = {'ok': 0, 'fail': 0}; maxlast = 0; fails = []
        # (2) true rule-30 right halves at times T0, every phase
        for T0 in range(0, T + 1, 20):
            right = [rows[T0][W + p] for p in range(1, W)]
            for phase0 in range(cert.P):
                res = check_path(cert, drive(cert, right[:600], phase0, 500))
                if isinstance(res, tuple): stats['ok'] += 1; maxlast = max(maxlast, res[1])
                else: stats['fail'] += 1; fails.append((T0, phase0, res))
        # random right halves, exact rule 30 driving
        for trial in range(150):
            right = [rng.randrange(2) for _ in range(700)]
            res = check_path(cert, drive(cert, right, rng.randrange(cert.P), 600))
            if isinstance(res, tuple): stats['ok'] += 1; maxlast = max(maxlast, res[1])
            else: stats['fail'] += 1; fails.append(('rand', trial, res))
        # random environment walks in the strip graph
        for trial in range(300):
            right = [rng.randrange(2) for _ in range(cert.b)]
            res = check_path(cert, drive(cert, right, rng.randrange(cert.P), 1500, env='random', rng=rng))
            if isinstance(res, tuple): stats['ok'] += 1; maxlast = max(maxlast, res[1])
            else: stats['fail'] += 1; fails.append(('env', trial, res))
        print(name, stats, 'max stabilization step', maxlast, fails[:3])
