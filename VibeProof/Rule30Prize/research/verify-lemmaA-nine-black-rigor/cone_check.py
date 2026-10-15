# Independent check of Lemma A over the FULL two-sided light cone, no driven-system modelling.
# Time-t row on columns m-L .. m+R (relative offsets -L..R) ranges over ALL 2^(L+R+1) configurations,
# evaluated in parallel: each cell is a big int whose bit i is that cell's value in configuration i.
# rule 30: new = left xor (center or right).  Cells outside the cone are never read: at step s we keep
# only offsets -L+s .. R-s.
import sys
def run(k, L, R):
    N = L + R + 1
    M = 1 << N                      # number of configurations
    full = (1 << M) - 1
    # bit-sliced variable masks: variable j is 1 in configuration i iff bit j of i is 1
    def varmask(j):
        # pattern: blocks of 2^j zeros then 2^j ones, repeated
        blk = ((1 << (1 << j)) - 1) << (1 << j)       # 2^(j+1)-bit block: high half ones
        period = 1 << (j + 1)
        reps = M // period
        # repeat block reps times
        x = blk
        width = period
        # doubling repeat
        res, rw, cnt = 0, 0, 0
        cur, cw, n = blk, period, reps
        while n:
            if n & 1:
                res |= cur << rw; rw += cw
            cur |= cur << cw; cw *= 2; n >>= 1
        return res
    row = {off: varmask(off + L) for off in range(-L, R + 1)}
    lo, hi = -L, R
    colm = [row[0]]                 # column m (offset 0) at times t, t+1, ...
    rows = [row]
    for s in range(k):
        new = {}
        for off in range(lo + 1, hi):
            l, c, r = row[off - 1], row[off], row[off + 1]
            new[off] = l ^ (c | r)
        row = new; lo += 1; hi -= 1
        rows.append(row)
        if 0 in row and s + 1 < k: colm.append(row[0])
    return M, full, colm, rows

for k, L, R in [(9, 8, 11), (8, 7, 10)]:
    M, full, colm, rows = run(k, L, R)
    assert len(colm) == k, (len(colm), k)
    hyp = full
    for c in colm: hyp &= c          # column m black at times t .. t+k-1
    c1, c2 = rows[k][1], rows[k][2]  # cells (t+k, m+1), (t+k, m+2)
    nhyp = bin(hyp).count("1")
    bad1 = bin(hyp & c1).count("1")              # cell(t+k,m+1)=1 although hypothesis holds
    bad2 = bin(hyp & (full ^ c2)).count("1")     # cell(t+k,m+2)=0 although hypothesis holds
    print(f"k={k}: cone cols m-{L}..m+{R} ({M} configs); configs with column m black at t..t+{k-1}: {nhyp}"
          f" (expected {M >> k}); violations: (t+{k},m+1)=1: {bad1}, (t+{k},m+2)=0: {bad2}")
