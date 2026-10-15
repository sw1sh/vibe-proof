"""Theorem D mechanism, tested on the right half driven by a periodic center column.

Right half p >= 1 as a big int: bit (p-1) = cell(t, p). Column 0 = driver d(t).
cell(t+1,p) = cell(t,p-1) xor (cell(t,p) or cell(t,p+1)), cell(t,0) = d(t).

Word w = 1^s 0^r u (|u| = k), P = s + r + k; driver d(t) = w[t mod P], t >= 0 (t1 = 0).
Theorem D's proof says: for EVERY initial right half at time 0, column 1 on
[e_k, e_k + P) (e_k = s + kP) is the same for all k -- in fact a fixed function of w.
"""
import random, sys, math, itertools

def jmin(k):
    return (k + 9) // 2          # = ceil((k+8)/2)

def rmin(k):
    return 1 + 9 * jmin(k)

def col1_trace(word, init, steps):
    """column 1 at times 0..steps-1; init = big int of the right half at time 0."""
    P = len(word)
    W = steps + 4
    mask = (1 << W) - 1
    X = init & mask
    out = []
    for t in range(steps):
        out.append(X & 1)
        d = word[t % P]
        X = (((X << 1) | d) ^ (X | (X >> 1))) & mask
    return out

def inits(W, nrand, rng):
    res = [("zeros", 0), ("ones", (1 << W) - 1),
           ("01", int("01" * (W // 2 + 1), 2)), ("10", int("10" * (W // 2 + 1), 2))]
    for i in range(nrand):
        res.append((f"rand{i}", rng.getrandbits(W)))
    # sparse and dense random
    for i in range(2):
        x = 0
        for b in range(W):
            if rng.random() < 0.1:
                x |= 1 << b
        res.append((f"sparse{i}", x))
        res.append((f"dense{i}", ((1 << W) - 1) ^ x))
    return res

def check_word(word, s, nrand, rng, K=5, verbose=False):
    P = len(word)
    steps = s + K * P
    fixed = None
    nper_fail = 0
    ndet_fail = 0
    for name, x in inits(steps + 4, nrand, rng):
        tr = col1_trace(word, x, steps)
        wins = [tuple(tr[s + k * P: s + (k + 1) * P]) for k in range(K - 1)]
        if any(wv != wins[0] for wv in wins):
            nper_fail += 1
            if verbose:
                print("   non-periodic col 1 for init", name)
        if fixed is None:
            fixed = wins[0]
        elif wins[0] != fixed:
            ndet_fail += 1
    return nper_fail, ndet_fail, fixed

NRAND = int(sys.argv[3]) if len(sys.argv) > 3 else 6
KPER = int(sys.argv[4]) if len(sys.argv) > 4 else 5
def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    mode = sys.argv[2] if len(sys.argv) > 2 else "main"
    if mode == "main":
        total = 0
        bad = 0
        for s in (9, 10, 12, 17, 30):
            for k in range(0, 9):
                if k <= 3:
                    us = [list(u) for u in itertools.product([0, 1], repeat=k)]
                else:
                    us = [[rng.getrandbits(1) for _ in range(k)] for _ in range(4)]
                for u in us:
                    for r in (rmin(k), rmin(k) + 1, rmin(k) + 9):
                        word = [1] * s + [0] * r + u
                        npf, ndf, fixed = check_word(word, s, NRAND, rng, K=KPER)
                        total += 1
                        # structural prediction of the fixed window
                        P = len(word)
                        ok_struct = fixed[0] == 0 and all(fixed[i] == 1 for i in range(1, r + 1)) \
                            and all(fixed[i] == 0 for i in range(P - s + 9, P))
                        if npf or ndf or not ok_struct:
                            bad += 1
                            print("FAIL", s, r, u, npf, ndf, ok_struct)
        print(f"main sweep: {total} words, failures = {bad}")
    elif mode == "below":
        # negative controls: r = 9j (one below the bound) and s = 8
        for s, k_list in ((9, range(0, 6)), (8, range(0, 4))):
            for k in k_list:
                for r in (rmin(k) - 1, rmin(k) - 5, rmin(k) - 9, rmin(k)):
                    cnt_p = cnt_d = n = 0
                    for _ in range(6):
                        u = [rng.getrandbits(1) for _ in range(k)]
                        word = [1] * s + [0] * r + u
                        npf, ndf, _ = check_word(word, s, 6, rng)
                        cnt_p += npf > 0
                        cnt_d += ndf > 0
                        n += 1
                    print(f"s={s} k={k} r={r} (rmin={rmin(k)}): words with non-periodic col1 "
                          f"{cnt_p}/{n}, with init-dependent window {cnt_d}/{n}")
    elif mode == "evidence":
        for wstr in ("1" * 9 + "0" * 37, "1" * 30 + "0" * 37, "1" * 9 + "0" * 47 + "110"):
            word = [int(ch) for ch in wstr]
            P = len(word)
            s = wstr.index("0")
            K = 6
            steps = s + K * P
            starts = []
            for i in range(200):
                x = rng.getrandbits(steps + 4)
                tr = col1_trace(word, x, steps)
                # earliest T0 such that tr is P-periodic on [T0, steps)
                T0 = steps - P
                while T0 > 0 and tr[T0 - 1] == tr[T0 - 1 + P]:
                    T0 -= 1
                starts.append(T0)
            print(f"word {wstr} (P={P}): column-1 period-P start times over 200 random inits: "
                  f"max {max(starts)}, min {min(starts)}, all <= s ({s})? {all(t <= s for t in starts)}")

main()
