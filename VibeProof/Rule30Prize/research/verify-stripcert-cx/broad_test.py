# Broader test of the generic soundness content: for every primitive word (up to rotation) of length <= Lmax
# for which the exhaustive SCC analysis says "every infinite strip path has eventually periodic masked col 1"
# at some b <= bmax, simulate exact rule-30 right halves driven by w^inf (random starts, all phases) and
# random-environment strip walks, and check masked column 1 becomes periodic with period g*P
# (g = gcd of SCC white-cycle weights; we just test period lcm(g's)*P).
import sys, random, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-stripcert-cx')
from scc_semantic import analyze
from math import gcd

def lcm(a, b): return a * b // gcd(a, b) if a and b else max(a, b)

def necklaces(L):
    seen = set()
    for v in range(1 << L):
        s = format(v, '0%db' % L)
        rots = [s[i:] + s[:i] for i in range(L)]
        if min(rots) != s: continue
        if any(L % d == 0 and s == s[:d] * (L // d) for d in range(1, L)): continue
        if '0' not in s: continue
        yield s

def masked_tail_periodic(w, col1, Q, start):
    P = len(w)
    for k in range(start, len(col1) - Q):
        if w[k % P] == '0' and col1[k] != col1[k + Q]: return False
    return True

def run(Lmax, bmax, budget):
    rng = random.Random(7)
    t0 = time.time(); tested = 0; fails = []
    for L in range(1, Lmax + 1):
        for w in necklaces(L):
            for b in range(1, bmax + 1):
                ok, summ, nc = analyze(w, b)
                if ok: break
            if not ok: continue
            G = 1
            for (_, g, cons, u) in summ: G = lcm(G, g)
            Q = G * len(w)
            for trial in range(20):
                steps = 400 + 4 * Q
                # exact driven right half (finite array, zero beyond)
                row = [rng.randrange(2) for _ in range(steps + b + 5)]
                ph = rng.randrange(len(w)); col1 = []
                ww = w[ph:] + w[:ph]
                for k in range(steps):
                    col1.append(row[0])
                    full = [int(ww[k % len(w)])] + row + [0, 0]
                    row = [full[i] ^ (full[i + 1] | full[i + 2]) for i in range(len(row))]
                if not masked_tail_periodic(ww, col1, Q, steps // 2): fails.append((w, b, 'driven', trial))
                # random environment strip walk
                s = [rng.randrange(2) for _ in range(b)]; col1 = []
                for k in range(steps):
                    col1.append(s[0])
                    full = [int(ww[k % len(w)])] + s + [rng.randrange(2)]
                    s = [full[i] ^ (full[i + 1] | full[i + 2]) for i in range(b)]
                if not masked_tail_periodic(ww, col1, Q, steps // 2): fails.append((w, b, 'env', trial))
            tested += 1
            if time.time() - t0 > budget: return tested, fails, 'budget hit at L=%d' % L
    return tested, fails, 'complete'

if __name__ == '__main__':
    Lmax, bmax, budget = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    tested, fails, status = run(Lmax, bmax, budget)
    print('certified words tested:', tested, 'failures:', len(fails), fails[:5], status)
