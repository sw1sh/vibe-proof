#!/usr/bin/env python3
"""Check the evidence claim p_c(n) = 2^n for n <= 20 in the 10^7 prefix of the
Rule 30 center column, after validating the data file against a direct simulation."""
import math
import sys

import numpy as np

DATA = "/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin"


def simulate_center(T):
    # Rule 30 on a Python int: bit (p + T) holds cell p, p in [-T, T].
    row = 1 << T
    out = []
    mask = (1 << (2 * T + 1)) - 1
    for _ in range(T):
        out.append((row >> T) & 1)
        left = row << 1   # new cell p gets old cell p-1 -> shift towards higher index
        right = row >> 1  # new cell p gets old cell p+1
        row = (left ^ (row | right)) & mask
    return out


def main():
    raw = np.fromfile(DATA, dtype=np.uint8)
    bits = np.unpackbits(raw)  # high bit first, matching the file format
    N = bits.size
    print("N bits:", N)
    T = 20000
    sim = simulate_center(T)
    agree = all(int(bits[i]) == sim[i] for i in range(T))
    print("first 20 from file:", "".join(str(int(b)) for b in bits[:20]))
    print("file agrees with direct simulation on first", T, ":", agree)
    if not agree:
        sys.exit(1)

    b = bits.astype(np.uint64)
    for n in range(1, 31):
        L = N - n + 1
        w = np.zeros(L, dtype=np.uint64)
        for k in range(n):
            w = (w << np.uint64(1)) | b[k:k + L]
        if n <= 27:
            seen = np.zeros(1 << n, dtype=bool)
            seen[w] = True
            p = int(seen.sum())
        else:
            p = int(np.unique(w).size)
        full = 2 ** n
        lam = L / full
        exp_missing = full * math.exp(-lam) if lam < 700 else 0.0
        # expected distinct count for L uniform random draws (Poisson approx)
        exp_distinct = full * (1 - math.exp(-lam))
        print(f"n={n:2d} p={p:9d} 2^n={full:11d} missing={full - p:10d} "
              f"random-model expected missing={exp_missing:12.3f} expected distinct={exp_distinct:14.1f}")


if __name__ == "__main__":
    main()
