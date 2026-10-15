# Randomized adversarial soundness test: random initial strips + random column-(W+1) inputs (several input
# distributions, including biased and "sticky" ones), checking that column 1 at zero phases equals the claimed
# value b_phi at all times k >= stab - p.  Also a "true driven right half" test: take the real rule-30 right half
# at time T0 and from then on force the center column to w^infinity.
import sys
import numpy as np

CLAIMS = [  # word, W, stab, claimed col-1 pattern per phase
    ("00000011", 14, 71, "11111110"),
    ("01111111", 14, 48, "0*******"),
    ("01111111", 12, 42, "0*******"),
    ("0000000011", 14, 57, None),
    ("0011111111", 14, 70, None),
    ("0111111111", 14, 40, None),
    ("00000000001", 14, 50, None),
    ("00000000011", 14, 63, None),
    ("00000001111", 14, 70, None),
    ("00111111111", 14, 78, None),
    ("01011111111", 14, 63, None),
    ("01111111111", 14, 46, None),
    ("000000000001", 14, 61, None),
    ("000000000011", 12, 51, None),
    ("000000000101", 12, 52, None),
    ("000111111111", 12, 50, None),
    ("001111111111", 12, 50, None),
    ("010111111111", 12, 38, None),
    ("011111111111", 12, 40, None),
]
# forced values from the SAT check (zero phases only), phase -> value
SAT = {
    "00000011": {0: 1, 1: 1, 2: 1, 3: 1, 4: 1, 5: 1},
    "01111111": {0: 0},
    "0000000011": {i: 1 for i in range(8)},
    "0011111111": {0: 0, 1: 1},
    "0111111111": {0: 0},
    "00000000001": {0: 0, 1: 0, **{i: 1 for i in range(2, 10)}},
    "00000000011": {i: 1 for i in range(9)},
    "00000001111": {i: 1 for i in range(7)},
    "00111111111": {0: 0, 1: 1},
    "01011111111": {0: 0, 2: 0},
    "01111111111": {0: 0},
    "000000000001": {0: 0, 1: 0, **{i: 1 for i in range(2, 11)}},
    "000000000011": {i: 1 for i in range(10)},
    "000000000101": {0: 0, **{i: 1 for i in range(1, 9)}, 10: 0},
    "000111111111": {0: 0, 1: 1, 2: 1},
    "001111111111": {0: 0, 1: 1},
    "010111111111": {0: 0, 2: 0},
    "011111111111": {0: 0},
}

def strip_run(w, W, stab, N, rng, mode):
    p = len(w)
    s = rng.integers(0, 2, size=(N, W), dtype=np.uint8)
    if mode == "sparse":
        s = (rng.random((N, W)) < 0.1).astype(np.uint8)
    elif mode == "dense":
        s = (rng.random((N, W)) < 0.9).astype(np.uint8)
    bias = rng.random(N)  # per-trajectory input bias
    sticky = rng.integers(0, 2, size=N, dtype=np.uint8)
    viol = 0
    for k in range(stab + 3 * p):
        ph = k % p
        if k >= stab - p and w[ph] == '0':
            b = SAT[w][ph]
            viol += int(np.count_nonzero(s[:, 0] != b))
        d = np.uint8(int(w[ph]))
        if mode == "uniform":
            x = rng.integers(0, 2, size=N, dtype=np.uint8)
        elif mode == "biased" or mode == "sparse" or mode == "dense":
            x = (rng.random(N) < bias).astype(np.uint8)
        else:  # sticky: flip rarely
            flip = (rng.random(N) < 0.05).astype(np.uint8)
            sticky = sticky ^ flip
            x = sticky
        left = np.empty_like(s); left[:, 0] = d; left[:, 1:] = s[:, :-1]
        right = np.empty_like(s); right[:, -1] = x; right[:, :-1] = s[:, 1:]
        s = left ^ (s | right)
    return viol

def driven_true(w, W, stab, T0s):
    # real rule 30 up to T0, then center forced to w^inf; right half evolves by the rule (unbounded to the right)
    p = len(w)
    viol = 0
    for T0 in T0s:
        n = 2 * (T0 + stab + 4 * p) + 10
        off = n // 2
        a = np.zeros(n, dtype=np.uint8); a[off] = 1
        for t in range(T0):
            a[1:-1] = a[:-2] ^ (a[1:-1] | a[2:])
        # now right half columns off+1.. evolve with column off forced
        r = a[off:].copy()  # r[0] = center, r[1..] right half
        for k in range(stab + 3 * p):
            ph = k % p
            r[0] = int(w[ph])
            if k >= stab - p and w[ph] == '0':
                if r[1] != SAT[w][ph]:
                    viol += 1
            nr = r.copy()
            nr[1:-1] = r[:-2] ^ (r[1:-1] | r[2:])
            r = nr
    return viol

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    rng = np.random.default_rng(12345)
    for (w, W, stab, pat) in CLAIMS:
        if which != "all" and which != w:
            continue
        tot = 0
        for mode in ("uniform", "biased", "sparse", "dense", "sticky"):
            tot += strip_run(w, W, stab, 40000, rng, mode)
        dv = driven_true(w, W, stab, [0, 1, 2, 3, 5, 8, 13, 50, 101, 257, 600])
        print(w, f"W={W}", "strip-violations", tot, "true-driven-violations", dv, flush=True)
