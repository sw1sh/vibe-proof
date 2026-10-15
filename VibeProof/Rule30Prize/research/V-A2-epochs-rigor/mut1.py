"""Independent numerical check of claim A2-epochs (i)-(iv), written from scratch (no reuse of A-monovariant code).

Row representation: list x with x[0] = 0 (the wall) and x[k] = depth k.  A row is given by a finite prefix
x[0..M] plus a tail rule: 'zero' (finitely supported), 'stripe' (x_k = s_k beyond M), or 'unknown'
(a random infinite row: only depths within the light cone of the prefix are trusted).
"""
import random, sys

def s(k):
    return k % 2

def tail_val(tail, k):
    if tail == 'zero':
        return 0
    if tail == 'stripe':
        return s(k)
    raise ValueError

def step(x, tail, valid):
    """One ZBL step.  valid = number of trusted depths (x[0..valid]).  Returns (new_x, new_valid)."""
    M = len(x) - 1
    if tail in ('zero', 'stripe'):
        # extend the prefix by 2 using the tail, then compute depths 1..M+1 exactly
        ext = x + [tail_val(tail, M + 1), tail_val(tail, M + 2)]
        y = [0] + [ext[k + 1] ^ (ext[k] | ext[k + 1]) for k in range(1, M + 2)]
        return y, M + 1
    # unknown tail: depth k needs x[k+1]; trusted only up to valid-1
    y = [0] + [x[k + 1] ^ (x[k] | x[k + 1]) for k in range(1, M)]
    return y, valid - 1

def firstdef(x, tail, valid):
    """First depth k >= 1 with x_k != s_k, searched within trusted depths; None if none found there."""
    for k in range(1, valid + 1):
        if x[k] != s(k):
            return k
    if tail == 'zero':
        # beyond the prefix every cell is 0; the first odd depth > valid deviates
        k = valid + 1
        return k if k % 2 == 1 else k + 1
    return None   # stripe tail with no deviation, or unknown beyond the trusted range

def history(x0, tail, N):
    rows, valids = [x0], [len(x0) - 1]
    x, v = x0, len(x0) - 1
    for _ in range(N):
        x, v = step(x, tail, v)
        rows.append(x); valids.append(v)
    return rows, valids

stats = dict(i=0, ii=0, iii_free=0, iii_epoch=0, iv=0, epochs=0, deaths=0)
bad = []

def check_history(x0, tail, N):
    rows, valids = history(x0, tail, N)
    T = len(rows)
    fd = [firstdef(rows[t], tail, valids[t]) for t in range(T)]
    col1 = [rows[t][1] if valids[t] >= 1 else None for t in range(T)]
    # death D: first even time with depth 1 white (phase-0 constraint violated)
    D = None
    for t in range(0, T, 2):
        if col1[t] is None:
            break
        if col1[t] == 0:
            D = t; break
    horizon = D if D is not None else T   # constrained at all even times < horizon (as far as known)
    known_until = max((t for t in range(T) if col1[t] is not None), default=-1)
    # (i): fd(t) = d >= 2  =>  fd(t+1) = d-1 (any row, no constraint)
    for t in range(T - 1):
        d = fd[t]
        if d is not None and d >= 2 and fd[t + 1] is not None:
            stats['i'] += 1
            if fd[t + 1] != d - 1:
                bad.append(('i', t, d, fd[t + 1]))
        if d is not None and d >= 1 and t + d - 1 < T and col1[t + d - 1] is not None:
            if col1[t + d - 1] != 0:
                bad.append(('i-hits', t, d))
    # (ii): survival to time t+d-1 => t+d even
    for t in range(T):
        d = fd[t]
        if d is None:
            continue
        if t + d - 1 < horizon and t + d - 1 <= known_until:
            stats['ii'] += 1
            if (t + d) % 2 != 0:
                bad.append(('ii', t, d))
    # (iii) free bits: for even times 2s < horizon with 2s+1 known
    for t in range(0, min(horizon, T - 1), 2):
        if col1[t + 1] is None or fd[t] is None:
            continue
        stats['iii_free'] += 1
        if (col1[t + 1] == 0) != (fd[t] == 2):
            bad.append(('iii-free', t, col1[t + 1], fd[t]))
    # (iii)/(iv): resets at odd tau inside the surviving range
    for tau in range(1, min(horizon, T - 1), 2):
        if col1[tau] != 0:
            continue
        d = fd[tau + 1]
        if d is None:
            continue
        x = rows[tau]
        # (iv): needs only d >= 2 (true when tau+1 < horizon, since tau+1 is even and constrained)
        if tau + 1 < horizon:
            if d < 2:
                bad.append(('iv-d<2', tau, d))
            elif d + 1 <= valids[tau]:
                stats['iv'] += 1
                ok = x[1] == 0 and x[2] == 1 and all(x[k] == s(k) for k in range(3, d + 1)) and x[d + 1] != s(d + 1)
                if not ok:
                    bad.append(('iv', tau, d, x[:d + 2]))
        # (iii) epoch: if the history survives to tau+d, d is even, the free bits are 1^(d/2-1) 0, and the
        # triangle {t >= tau+1, 1 <= k, k+t < tau+1+d} is stripe
        if tau + d < horizon and tau + d < T:
            stats['iii_epoch'] += 1
            if d % 2 != 0:
                bad.append(('iii-even', tau, d))
            fb = [col1[u] for u in range(tau + 2, tau + d + 1, 2)]
            if fb != [1] * (d // 2 - 1) + [0]:
                bad.append(('iii-freebits', tau, d, fb))
            for t in range(tau + 1, tau + d + 1):
                for k in range(1, tau + 1 + d - t):
                    if k <= valids[t] and rows[t][k] != s(k):
                        bad.append(('iii-triangle', tau, d, t, k))
    # epochs: a0 = 0, a_{i+1} = a_i + fd(a_i); death (if any) equals the end of the first odd epoch
    a = 0
    while a < T and fd[a] is not None:
        d = fd[a]
        end = a + d - 1
        if end >= T or col1[end] is None:
            break
        stats['epochs'] += 1
        # depth 1 is black on [a, end-1] and white at end
        if any(col1[u] != 1 for u in range(a, end)) or col1[end] != 0:
            bad.append(('epoch-col1', a, d))
        if d % 2 == 1:
            stats['deaths'] += 1
            if D != end:
                bad.append(('epoch-death', a, d, D))
            break
        else:
            if D is not None and D <= end:
                bad.append(('epoch-even-but-dead', a, d, D))
        a = end + 1

def main():
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    # finite rows (Q_01 setting), wall x0 = 0
    for trial in range(6000):
        W = random.randint(1, 26)
        x0 = [0] + [random.getrandbits(1) for _ in range(W)]
        check_history(x0, 'zero', 3 * W + 10)
    # stripe-prefixed finite rows: long stripe prefix then random block (long surviving histories)
    for trial in range(3000):
        P = random.randint(2, 40)
        W = random.randint(1, 16)
        x0 = [0] + [s(k) for k in range(1, P + 1)] + [random.getrandbits(1) for _ in range(W)]
        check_history(x0, 'zero', 2 * (P + W) + 10)
    # infinite rows: stripe-tailed (random prefix, then stripe forever)
    for trial in range(3000):
        W = random.randint(1, 20)
        x0 = [0] + [random.getrandbits(1) for _ in range(W)]
        check_history(x0, 'stripe', 60)
    # infinite rows: random (unknown tail), only light-cone-trusted depths are used
    for trial in range(1500):
        M = 120
        x0 = [0] + [random.getrandbits(1) for _ in range(M)]
        check_history(x0, 'unknown', 100)
    print(stats)
    print('violations:', len(bad))
    for b in bad[:20]:
        print(b)

main()
