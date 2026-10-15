"""Simulation cross-check of the ether+wall trap in the driven right half (any right material).

For each alignment (word w, ether column j0, time shift s) and k in the residue class
(j0 + k) % 7 == 2 (smallest two values), start with columns 1..k = ether at phase s, columns
k+1..k+13 = a random wall state of phase s, and random bits in columns k+14..k+13+R (R random),
white beyond. Drive column 0 by w^inf (column 0 at time t = w[t % 4] = ether(j0, t + s)).
Check for N steps: columns 1..k stay ether, the wall stays in W, and column 1 at the white times
of column 0 equals ether(j0+1, t+s).
"""
import random
import re
import sys

lean_path = sys.argv[1]
src = open(lean_path).read()
body = re.search(r"def wallStates : List \(Nat × List Bool\) := \[(.*?)\n\]", src, re.S).group(1)
W = set()
for ph, bits in re.findall(r"\((\d+), \[([a-z, ]+)\]\)", body):
    W.add((int(ph), tuple(1 if b.strip() == "true" else 0 for b in bits.split(","))))
byphase = {p: [s for (q, s) in W if q == p] for p in range(4)}

E = [[0, 0, 1, 1], [0, 1, 1, 0], [1, 1, 0, 1], [0, 1, 0, 1], [0, 0, 1, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
def ether(j, ph):
    return E[j % 7][ph % 4]

words = {"0001": [0, 0, 0, 1], "0011": [0, 0, 1, 1], "0111": [0, 1, 1, 1], "0101": [0, 1, 0, 1]}
aligns = [("0001", 5, 0), ("0001", 6, 0), ("0011", 0, 0), ("0011", 1, 3), ("0011", 4, 0),
          ("0111", 2, 2), ("0101", 3, 0)]

rng = random.Random(12345)
N = 600
fails = 0
runs = 0
for (wn, j0, s) in aligns:
    w = words[wn]
    # check alignment
    assert all(ether(j0, psi + s) == w[psi % 4] for psi in range(4)), (wn, j0, s)
    k0 = (2 - j0) % 7
    for k in (k0, k0 + 7):
        for trial in range(15):
            R = rng.randrange(0, 40)
            ws = rng.choice(byphase[s % 4])
            width = k + 13 + R + N + 3  # room for the light cone
            row = [0] * (width + 1)
            row[0] = w[0]
            for p in range(1, k + 1):
                row[p] = ether(j0 + p, s)
            for i in range(13):
                row[k + 1 + i] = ws[i]
            for p in range(k + 14, k + 14 + R):
                row[p] = rng.randrange(2)
            runs += 1
            for t in range(N):
                ph = (t + s) % 4
                assert row[0] == ether(j0, t + s)
                for p in range(1, k + 1):
                    if row[p] != ether(j0 + p, t + s):
                        fails += 1
                        print("ether broke", wn, j0, s, k, t, p)
                        break
                if (ph, tuple(row[k + 1:k + 14])) not in W:
                    fails += 1
                    print("wall left W", wn, j0, s, k, t)
                    break
                if row[0] == 0 and row[1] != ether(j0 + 1, t + s):
                    fails += 1
                    print("masked col 1 broke", wn, j0, s, k, t)
                    break
                new = [0] * (width + 1)
                new[0] = w[(t + 1) % 4]
                for p in range(1, width):
                    new[p] = row[p - 1] ^ (row[p] | row[p + 1])
                row = new
print("runs:", runs, "failures:", fails)
