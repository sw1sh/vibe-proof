# Own simulation (not the B-edge-trap scripts): right half driven by column 0 = prefix d (n bits) then w^inf.
# Over the window [S/2, S) report each column's value per phase (t - n) mod 4, '*' if it varies,
# and name columns that equal an ether column at the aligned phase (0001: E(j, phase), j0 = 6).
import random, sys
cols = {0: "0011", 1: "0110", 2: "1101", 3: "0101", 4: "0011", 5: "0001", 6: "0001"}
name = {"0011": "B1/B5", "0110": "B2", "1101": "B3", "0101": "B4", "0001": "c"}
def run(w, n, dbits, S, K):
    P = len(w)
    drv = lambda t: dbits[t] if t < n else int(w[(t - n) % P])
    row = drv(0)  # bit k = column k
    vals = {}
    for t in range(n + S):
        if t >= n + S // 2:
            r = (t - n) % 4
            for k in range(K + 1):
                v = (row >> k) & 1
                vals[(k, r)] = v if vals.get((k, r), v) == v else '*'
        Wd = row.bit_length() + 2
        row = ((((row << 1) ^ (row | (row >> 1))) & ((1 << Wd) - 1)) & ~1) | drv(t + 1)
    words = [''.join(str(vals[(k, r)]) for r in range(4)) for k in range(K + 1)]
    return words
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
for trial in range(6):
    n = 0 if trial == 0 else random.randint(5, 40)
    d = [random.randint(0, 1) for _ in range(n)]
    words = run("0001", n, d, 3000, 30)
    # expected pure ether to the right of a c column with j0 = 6: column k is ether column (6 + k) mod 7
    match = []
    for k, wd in enumerate(words):
        match.append('E' if wd == cols[(6 + k) % 7] else ('e' if wd == cols[(5 + k) % 7] else '.'))
    print(f"trial {trial} n={n}:")
    print("   words:", ' '.join(words[:16]))
    print("   ether(j0=6) match:", ''.join(match))
