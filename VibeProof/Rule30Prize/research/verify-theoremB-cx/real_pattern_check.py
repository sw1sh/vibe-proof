"""Check Lemma A and Lemma A* on the REAL rule 30 pattern (single black cell) and on random
full-line rule 30 evolutions (no half-plane reasoning involved): every time a column is black for
L = 9j consecutive steps, the row right after must read (0,1)^j in the next 2j columns.

Also verify the center column against the known prefix of OEIS A051023.
"""
import random
import sys


def evolve_full(row0, steps):
    """row0: list of bits on a ring of width W (wide enough to avoid wrap effects for the
    single-cell start). Returns list of rows."""
    W = len(row0)
    rows = [row0]
    cur = row0
    for _ in range(steps):
        nxt = [cur[(p - 1) % W] ^ (cur[p] | cur[(p + 1) % W]) for p in range(W)]
        rows.append(nxt)
        cur = nxt
    return rows


def evolve_full_int(x, W, steps):
    """Bitset version on a ring of width W: bit p = column p. Returns list of ints."""
    mask = (1 << W) - 1
    out = [x]
    for _ in range(steps):
        left = ((x << 1) | (x >> (W - 1))) & mask   # bit p gets old bit p-1
        right = ((x >> 1) | ((x & 1) << (W - 1))) & mask  # bit p gets old bit p+1
        x = (left ^ (x | right)) & mask
        out.append(x)
    return out


def scan(rows_int, W, max_j, tag, col_range=None):
    """For every column and every maximal-or-not run of >= 9j black cells ending at time e-1,
    check the (0,1)^j pattern at time e in columns p+1..p+2j (ring indices)."""
    nT = len(rows_int)
    stats = {j: [0, 0] for j in range(1, max_j + 1)}  # j -> [checked, failed]
    cols = range(W) if col_range is None else col_range
    for p in cols:
        run = 0
        for t in range(nT):
            b = (rows_int[t] >> p) & 1
            if t > 0 and run >= 9:
                # time t is right after a run of 'run' blacks at times t-run..t-1
                for j in range(1, min(max_j, run // 9) + 1):
                    ok = True
                    for i in range(1, j + 1):
                        cw = (rows_int[t] >> ((p + 2 * i - 1) % W)) & 1
                        cb = (rows_int[t] >> ((p + 2 * i) % W)) & 1
                        if cw != 0 or cb != 1:
                            ok = False
                    stats[j][0] += 1
                    if not ok:
                        stats[j][1] += 1
                        print(f"  FAIL {tag}: col {p} t {t} j {j}")
            run = run + 1 if b else 0
    return stats


if __name__ == '__main__':
    # Real pattern: single black cell, ring wide enough (W > 2*steps+2)
    steps = 1500
    W = 2 * steps + 5
    mid = steps + 2
    x0 = 1 << mid
    rows = evolve_full_int(x0, W, steps)
    center = [(rows[t] >> mid) & 1 for t in range(steps + 1)]
    a051023 = [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1,0,0,1,1,1,0,0,0,1,1,0,1,0,1,1,1,1,1,1,0,0,1,0,1,1,1,1,0,0,1,0,1,0,0,0,0,1,1,1,0,0,1,0,0,1,1,1,1,0,1,0,1,0,0,0,1,0,0,1,1,1,0,0,1,1,1,1,1,0,1,1,0,0,0,0,1,0,1,0,0,1,1,0,1,0]
    print("center prefix matches A051023 (first", len(a051023), "):", center[:len(a051023)] == a051023)
    # sanity on cone: cells outside |p|<=t are 0
    for t in range(0, steps + 1, 97):
        for p in range(W):
            if abs(p - mid) > t:
                assert ((rows[t] >> p) & 1) == 0
    st = scan(rows, W, 6, "real")
    print("real pattern, steps", steps, ": (j -> [occurrences checked, failures])", st)
    sys.stdout.flush()

    # Random full-line evolutions on a ring (Lemma A is local, ring is fine away from nothing:
    # on a ring every cell has true rule-30 neighbours, so the lemma must hold everywhere).
    rnd = random.Random(12345)
    tot = {}
    for trial in range(40):
        Wr = 400
        dens = rnd.choice([0.5, 0.5, 0.7, 0.85, 0.3])
        x = 0
        for p in range(Wr):
            if rnd.random() < dens:
                x |= 1 << p
        rr = evolve_full_int(x, Wr, 600)
        st = scan(rr, Wr, 4, f"rand{trial}")
        for j, (a, b) in st.items():
            tot.setdefault(j, [0, 0])
            tot[j][0] += a
            tot[j][1] += b
    print("random ring evolutions: (j -> [occurrences, failures])", tot)
