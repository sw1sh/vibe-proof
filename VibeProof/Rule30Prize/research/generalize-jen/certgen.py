# Mirror of the Lean `stripCert` (Rule30JenWindow.lean); find minimal (K, k) for words, emit Lean theorems.
import sys
def step(K, a, z, r):
    return (((r << 1) | a) ^ (r | (r >> 1) | (z << (K - 1)))) % (1 << K)
def image(K, a, S):
    out = set()
    for r in S:
        out.add(step(K, a, 0, r)); out.add(step(K, a, 1, r))
    return out
def apply_word(K, u, S):
    for a in u: S = image(K, a, S)
    return S
def cert(w, K, k):
    S = set(range(1 << K))
    for _ in range(k): S = apply_word(K, w, S)
    S0 = S
    if not apply_word(K, w, S0) <= S0: return False
    for phi in range(len(w)):
        if w[phi] == 0:
            Sp = apply_word(K, w[:phi], S0)
            if len({r & 1 for r in Sp}) > 1: return False
    return True
def find(w, Kmax=12, kmax=60):
    for K in range(1, Kmax + 1):
        # the iteration converges; find the smallest k
        S = set(range(1 << K)); prev = None
        for k in range(kmax + 1):
            if cert(w, K, k): return (K, k)
            S2 = apply_word(K, w, S)
            if S2 == S: break      # converged; larger k gives the same S0
            S = S2
    return None
if __name__ == '__main__':
    for ws in sys.argv[1:]:
        w = [int(ch) for ch in ws]
        print(ws, find(w))
