# Independent full-light-cone brute force for the black-run lemma (no driven-half decomposition).
# Rule 30: new(p) = old(p-1) xor (old(p) or old(p+1)).
# For K steps and target columns 1,2 at time t+K, the light cone at time t is positions [1-K, 2+K].
# We enumerate ALL 2^N assignments of that window (N = 2K+2) at once via bit-slicing:
# column p at time s is a big integer whose bit n is the cell value in configuration n.
import sys

def column_masks(N):
    """X[k] has bit n set iff bit k of n is set, for n in [0, 2^N)."""
    nbytes = (1 << N) // 8
    X = []
    for k in range(N):
        if k == 0:
            b = bytes([0xAA]) * nbytes
        elif k == 1:
            b = bytes([0xCC]) * nbytes
        elif k == 2:
            b = bytes([0xF0]) * nbytes
        else:
            blk = 1 << (k - 3)
            b = (bytes(blk) + b'\xff' * blk) * (nbytes // (2 * blk))
        X.append(int.from_bytes(b, 'little'))
    return X

def popcount(x):
    return bin(x).count('1')

def run(K, extra_right=0):
    lo, hi = 1 - K, 2 + K + extra_right
    N = hi - lo + 1
    FULL = (1 << (1 << N)) - 1
    X = column_masks(N)
    row = {lo + i: X[i] for i in range(N)}   # time t
    H = FULL                                  # configs with column 0 black at times t..t+K-1
    for s in range(K):
        H &= row[0]
        new = {}
        for p in range(min(row) + 1, max(row)):
            new[p] = row[p - 1] ^ (row[p] | row[p + 1])
        row = new
    c1, c2 = row[1], row[2]
    nH = popcount(H)
    n_c1_black = popcount(H & c1)
    n_c2_white = popcount(H & (FULL ^ c2))
    n_both_white = popcount(H & (FULL ^ (c1 | c2)))
    print(f"K={K} window=[{lo},{hi}] N={N}: configs with col0 black at t..t+{K-1}: {nH} (=2^{nH.bit_length()-1}); "
          f"col1(t+{K})=1 in {n_c1_black}; col2(t+{K})=0 in {n_c2_white}; col1|col2=0 in {n_both_white}")
    return nH, n_c1_black, n_c2_white

if __name__ == '__main__':
    for K in (7, 8, 9, 10):
        run(K)
    # K=8 with the right window extended to cell 11, so the free right cells are exactly 1..11 (2048 rows)
    run(8, extra_right=1)
