# SAT-based independent check of the adversarial strip certificate.
# For word w (phase 0 at time 0), strip width W, and a time K with w[K mod p] == '0':
#   ask z3 whether some initial strip state (2^W choices) and some input sequence x_0..x_{K-1} at column W+1
#   make column 1 at time K take the value v.  If exactly one v is satisfiable, column 1 is forced at time K.
# Monotonicity R_{k+p} subset R_k (proved separately) then forces it at all K + m p.
import sys
import z3

def forced_value(w, W, K):
    p = len(w)
    res = {}
    for v in (False, True):
        s = z3.Solver()
        cells = [[z3.Bool(f"c_{t}_{i}") for i in range(W + 2)] for t in range(K + 1)]
        # index i = 1..W are strip columns; i = 0 is the driver, i = W+1 the free input
        for t in range(K + 1):
            s.add(cells[t][0] == (w[t % p] == '1'))
        for t in range(K):
            for i in range(1, W + 1):
                L, C, R = cells[t][i - 1], cells[t][i], cells[t][i + 1]
                s.add(cells[t + 1][i] == z3.Xor(L, z3.Or(C, R)))
        s.add(cells[K][1] == v)
        r = s.check()
        res[v] = (r == z3.sat)
    return res

if __name__ == "__main__":
    W = int(sys.argv[1]); w = sys.argv[2]; K0 = int(sys.argv[3])  # check K in [K0, K0 + p)
    p = len(w)
    out = []
    for K in range(K0, K0 + p):
        ph = K % p
        if w[ph] != '0':
            continue
        r = forced_value(w, W, K)
        if r[False] and r[True]:
            out.append(f"ph{ph}:FREE")
        elif r[False]:
            out.append(f"ph{ph}:0")
        elif r[True]:
            out.append(f"ph{ph}:1")
        else:
            out.append(f"ph{ph}:EMPTY?!")
    print(w, f"W={W} K0={K0}", " ".join(out))
