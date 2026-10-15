# Faster uniform-in-r family test for 0^r u: per boundary case compute max next class by witness iteration.
import sys, time
sys.path.insert(0, '.')
from ellabs import solve
from satper import cone_cnf
from family0 import apply_u

def max_next_class(w, c, L, far=False):
    P = len(w)
    cnt, clauses, v = cone_cnf(w, P, L + 1, 0)
    if far: base = [[-v(0, p)] for p in range(1, c + 2)]
    else: base = [[-v(0, p)] for p in range(1, c + 1)] + [[v(0, c + 1)]]
    B = -1
    while True:
        cons = [[-v(P, p)] for p in range(1, B + 2)]   # zeros at 1..B+1 => next class > B
        sol = solve(cnt[0], clauses, base + cons)
        if sol is None: return B
        # witness's actual class
        cl = None
        for p in range(1, L + 2):
            if sol.get(v(P, p), False): cl = p - 1; break
        if cl is None: return None  # > L
        B = cl

def verify_fast(u, j=None, Z=None, r0=None, L=None):
    k = len(u)
    if j is None:
        for jj in range((k + 1) // 2, k + 10):
            after = apply_u([1] + [0, 1] * jj, [int(ch) for ch in u])
            if 1 in after: j = jj; break
    if j is None: return None, "no ell*"
    after = apply_u([1] + [0, 1] * j, [int(ch) for ch in u])
    ell_star = after.index(1)
    S = 9 * j
    if Z is None: Z = k + 4
    if r0 is None: r0 = Z
    if L is None: L = 3 * k + 16
    B = ell_star
    for d in range(-Z, S):
        if r0 + d < 0: continue
        m = max_next_class('0' * (r0 + d) + u, r0, L)
        if m is None: return None, f"unbounded at d={d}"
        B = max(B, m)
    m = max_next_class('0' * r0 + u, r0 + Z, L, far=True)
    if m is None: return None, "unbounded far"
    B = max(B, m)
    return max(r0 + S, B + S), f"j={j} S={S} ell*={ell_star} B={B}"

if __name__ == '__main__':
    budget = float(sys.argv[1]); us = sys.argv[2:]
    t0 = time.time()
    for u in us:
        if time.time() - t0 > budget: print(u, "SKIP", flush=True); continue
        t1 = time.time()
        R, info = verify_fast(u)
        print(f"{u}: R={R} {info} ({time.time()-t1:.1f}s)", flush=True)
