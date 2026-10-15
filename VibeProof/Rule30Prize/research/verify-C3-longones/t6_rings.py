# Rule 30 on rings Z/n (n >= 12): every column is eventually periodic. The local part of the C3 proof
# predicts: if on an attractor cycle column j has (cyclic) word w with both colors and every cyclic
# maximal 1-run >= 9, then column j-1 has period dividing |w|'s least period.
import sys, random
def step(x, n, mask):
    # position i <-> bit i; new(i) = old(i-1) xor (old(i) or old(i+1))
    left = ((x << 1) | (x >> (n - 1))) & mask      # bit i holds old(i-1)
    right = ((x >> 1) | ((x & 1) << (n - 1))) & mask  # bit i holds old(i+1)
    return left ^ (x | right)

def least_period(w):
    P = len(w)
    for d in range(1, P + 1):
        if P % d == 0 and all(w[i] == w[(i + d) % P] for i in range(P)):
            return d
    return P

def min_cyc_run(w):
    if all(w) or not any(w): return None
    k = w.index(0); r = w[k:] + w[:k]
    runs, cur = [], 0
    for x in r + [0]:
        if x: cur += 1
        else:
            if cur: runs.append(cur)
            cur = 0
    return min(runs)

stats = {}
found = viol = 0
examples = []
for n in range(12, 23):
    mask = (1 << n) - 1
    seen_cycles = set()
    rng = random.Random(n)
    starts = range(1 << n) if n <= 16 else (rng.getrandbits(n) for _ in range(40000))
    visited_global = {}
    cycles = []
    for s0 in starts:
        # walk until we hit a state with known status
        path = []
        x = s0
        local = {}
        while x not in visited_global and x not in local:
            local[x] = len(path); path.append(x); x = step(x, n, mask)
        if x in local:  # new cycle found
            cyc = path[local[x]:]
            cycles.append(cyc)
        for y in path:
            visited_global[y] = 1
    for cyc in cycles:
        L = len(cyc)
        for j in range(n):
            w = [(cyc[k] >> j) & 1 for k in range(L)]
            m = min_cyc_run(w)
            if m is None or m < 9:
                continue
            found += 1
            P = least_period(w)
            wl = [(cyc[k] >> ((j - 1) % n)) & 1 for k in range(L)]
            Pl = least_period(wl)
            if P % Pl != 0:
                viol += 1
                print("VIOLATION n=%d j=%d P=%d Pl=%d" % (n, j, P, Pl))
            elif len(examples) < 6:
                examples.append((n, j, "".join(map(str, w[:P])), Pl))
    print(f"n={n}: cycles={len(cycles)} lengths(sample)={sorted(set(len(c) for c in cycles))[:12]}", flush=True)
print(f"columns with long-ones cycle words: {found}; violations: {viol}")
for e in examples: print("example (n, j, center word, period of left column):", e)
