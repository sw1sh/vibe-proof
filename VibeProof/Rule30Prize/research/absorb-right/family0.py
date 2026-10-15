# Uniform-in-r absorption proof for the family w_r = 0^r u (u starts with 1), all r >= R(u).
# Finite verification (see notes): Lemma A* lock outcome ell*, and SAT next-class sets O_d for the
# boundary cases d in [-Z, S), and O_inf for the far-front case.
import sys, time
sys.path.insert(0, '.')
from ellabs import solve
from satper import cone_cnf

def next_classes(w, c, L, far=False):
    """Possible next classes (0..L or L+1 meaning '>L') of the period map of w (phase 0 start)
    from configurations in class c (zeros at 1..c, 1 at c+1), or if far: zeros at 1..c+1 (class > c)."""
    P = len(w)
    cnt, clauses, v = cone_cnf(w, P, L + 1, 0)
    # make sure initial cells up to needed columns exist in the cone: cone covers (0, p) for p <= L+1+P
    need = c + 1
    assert need <= L + 1 + P, "cone too small for class constraint"
    if far: base = [[-v(0, p)] for p in range(1, c + 2)]
    else: base = [[-v(0, p)] for p in range(1, c + 1)] + [[v(0, c + 1)]]
    res = set()
    for c2 in range(L + 2):
        if c2 <= L: cons = [[-v(P, p)] for p in range(1, c2 + 1)] + [[v(P, c2 + 1)]]
        else: cons = [[-v(P, p)] for p in range(1, L + 2)]
        if solve(cnt[0], clauses, base + cons) is not None: res.add(c2)
    return res

def apply_u(prefix, u):
    """Apply driver steps u to a configuration with known prefix (list of bits for columns 1..n);
    returns known prefix after |u| steps (length n - |u|)."""
    x = list(prefix)
    for c in u:
        n = len(x)
        new = []
        for p in range(n - 1):  # column p+1 known if p+2 <= n
            left = c if p == 0 else x[p - 1]
            new.append(left ^ (x[p] | x[p + 1]))
        x = new
    return x

def verify(u, j, Z, r0, L, verbose=True):
    t0 = time.time()
    S = 9 * j
    pre = [1] + [0, 1] * j   # columns 1..2j+1 at the start of u (Lemma A*)
    after = apply_u(pre, [int(ch) for ch in u])
    if 1 not in after:
        print(u, "lock prefix after u has no 1 in determined region", after); return None
    ell_star = after.index(1)
    if verbose: print(f"u={u}: j={j} S={S} determined prefix after u: {''.join(map(str,after))} -> ell*={ell_star}")
    B = ell_star; table = {}
    for d in range(-Z, S):
        if r0 + d < 0: continue
        w = '0' * (r0 + d) + u
        O = next_classes(w, r0, L)
        table[d] = O
        if L + 1 in O:
            print(f"  d={d}: unbounded outcome (> {L})"); return None
        B = max(B, max(O))
    w = '0' * r0 + u
    Oinf = next_classes(w, r0 + Z, L, far=True)
    if L + 1 in Oinf: print("  far case unbounded"); return None
    B = max(B, max(Oinf))
    R = max(r0 + S, B + S)
    if verbose:
        print(f"  boundary outcomes: " + ' '.join(f"{d}:{sorted(O)}" for d, O in table.items()))
        print(f"  far outcome: {sorted(Oinf)}; B={B}; R = max(r0+S, B+S) = {R}  ({time.time()-t0:.1f}s)")
    return R

if __name__ == '__main__':
    u = sys.argv[1]; j = int(sys.argv[2]); Z = int(sys.argv[3]); r0 = int(sys.argv[4]); L = int(sys.argv[5])
    verify(u, j, Z, r0, L)
