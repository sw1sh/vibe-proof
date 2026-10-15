"""Independent exhaustive checks of Lemma A and Lemma A* (j = 1, 2) by bit-slicing.

Setting: column m is black at times t .. t+L-1 (L = 9j). The right half (columns > m) evolves by
rule 30 with column m as left boundary:  new(p) = old(p-1) xor (old(p) or old(p+1)).
After L steps, columns m+1 .. m+2j depend only on columns m+1 .. m+2j+L at time t.
We enumerate ALL 2^n initial rows (n = 2j + L) at once: bit c of the big int X_i is the value of
column m+1+i in case c.

Claim (Lemma A*): at time t+L, columns m+1..m+2j read (0,1)^j, i.e. white, black, white, black...
Sanity: also show that with L = 9j - 1 black steps the claim FAILS for some row (so the checker
can detect failures), and record which pairs fail.
"""
import sys


def column_patterns(n):
    N = 1 << n
    ALL = (1 << N) - 1
    cols = []
    for i in range(n):
        half = 1 << i
        period = half << 1
        block = ((1 << half) - 1) << half  # bit c set iff bit i of c is 1, within one period
        reps = N // period
        # repeat block 'reps' times: multiply by sum_{k<reps} 2^(k*period)
        rep = ((1 << (period * reps)) - 1) // ((1 << period) - 1)
        cols.append(block * rep)
    # verify a few random cases directly
    import random
    for _ in range(50):
        c = random.randrange(N)
        for i in range(n):
            assert ((cols[i] >> c) & 1) == ((c >> i) & 1)
    return cols, ALL


def evolve_black(cols, ALL, L, driver_black=True):
    row = list(cols)
    for _ in range(L):
        d = ALL if driver_black else 0
        new = []
        for p in range(len(row) - 1):
            left = d if p == 0 else row[p - 1]
            new.append(left ^ (row[p] | row[p + 1]))
        row = new
    return row


def check(j, L):
    n = 2 * j + L
    cols, ALL = column_patterns(n)
    row = evolve_black(cols, ALL, L)
    assert len(row) == 2 * j
    ok = True
    bad = []
    for i in range(2 * j):
        want_black = (i % 2 == 1)  # column m+1+i: i even -> m+1,m+3.. white ; i odd -> black
        want = ALL if want_black else 0
        if row[i] != want:
            ok = False
            # count failing cases
            nfail = bin(row[i] ^ want).count('1')
            bad.append((i + 1, nfail))
    return ok, bad, n


if __name__ == '__main__':
    for (j, L) in [(1, 9), (1, 8), (1, 10), (1, 11), (2, 18), (2, 17)]:
        ok, bad, n = check(j, L)
        print(f"j={j} L={L} (n={n} input cells, {1<<n} rows): claim (0,1)^{j} holds for all rows: {ok}; failing columns (offset, #rows): {bad}")
        sys.stdout.flush()
