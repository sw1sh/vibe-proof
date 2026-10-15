"""Independent re-check of the EtherWall finite data (rigor verification).

Reads (as data only) the Lean source and the wallclosure txt file given as arguments.
"""
import re
import sys

lean_path, txt_path = sys.argv[1], sys.argv[2]
src = open(lean_path).read()

# ---- parse wallStates from Lean ----
m = re.search(r"def wallStates : List \(Nat × List Bool\) := \[(.*?)\n\]", src, re.S)
body = m.group(1)
entries = re.findall(r"\((\d+), \[([a-z, ]+)\]\)", body)
W = []
for ph, bits in entries:
    bl = tuple(1 if b.strip() == "true" else 0 for b in bits.split(","))
    W.append((int(ph), bl))
print("Lean wallStates entries:", len(W), "distinct:", len(set(W)))
assert all(len(s) == 13 for _, s in W)
assert all(0 <= p < 4 for p, _ in W)
Wset = set(W)

# ---- ether ----
ether_table = [
    [0, 0, 1, 1],  # B1
    [0, 1, 1, 0],  # B2
    [1, 1, 0, 1],  # B3
    [0, 1, 0, 1],  # B4
    [0, 0, 1, 1],  # B5
    [0, 0, 0, 1],  # c
    [0, 0, 0, 1],  # c
]
def ether(j, ph):
    return ether_table[j % 7][ph % 4]
def rule(a, b, c):
    return a ^ (b | c)
# independent check of the ether being a spatially-7-periodic rule-30 orbit
for j in range(7):
    for ph in range(4):
        assert ether(j, ph + 1) == rule(ether(j - 1, ph), ether(j, ph), ether(j + 1, ph)), (j, ph)
print("ether rule-30 consistency: OK (7 x 4)")

# ---- parse txt (phase, int with bit i = column k+1+i) ----
T = []
for line in open(txt_path):
    line = line.strip()
    if not line:
        continue
    ph, v = map(int, line.split())
    T.append((ph, tuple((v >> i) & 1 for i in range(13))))
print("txt entries:", len(T), "distinct:", len(set(T)), "txt == Lean set:", set(T) == Wset)

def lin3(row):
    return tuple(rule(row[i], row[i + 1], row[i + 2]) for i in range(len(row) - 2))

def succ(ph, s, x, B3=2):
    return ((ph + 1) % 4, lin3((ether(B3, ph),) + s + (x,)))

# closure + U-property
bad = 0
for ph, s in W:
    if ether(2, ph) == 0 and s[0] != ether(3, ph):
        bad += 1
        print("U fails", ph, s)
    for x in (0, 1):
        if succ(ph, s, x) not in Wset:
            bad += 1
            print("closure fails", ph, s, x)
print("closure + U-property failures:", bad)

# forward closure of each state: is W the closure of a single state?
def fclosure(seed):
    seen = {seed}
    stack = [seed]
    while stack:
        ph, s = stack.pop()
        for x in (0, 1):
            n = succ(ph, s, x)
            if n not in seen:
                seen.add(n)
                stack.append(n)
    return seen
gens = [st for st in W if fclosure(st) == Wset]
print("states whose forward closure is exactly W:", len(gens), "first txt state generates W:", fclosure(T[0]) == Wset)

# per-phase counts
from collections import Counter
print("per-phase counts:", sorted(Counter(p for p, _ in W).items()))

# ---- maximal closed U-set per width (greatest fixed point) ----
def max_closed_U(b):
    states = set()
    for ph in range(4):
        for v in range(1 << b):
            s = tuple((v >> i) & 1 for i in range(b))
            if ether(2, ph) == 0 and s[0] != ether(3, ph):
                continue
            states.add((ph, s))
    changed = True
    while changed:
        changed = False
        rem = []
        for st in states:
            ph, s = st
            for x in (0, 1):
                if succ(ph, s, x) not in states:
                    rem.append(st)
                    break
        if rem:
            changed = True
            for st in rem:
                states.discard(st)
    return states

for b in range(1, 14):
    S = max_closed_U(b)
    line = f"width {b}: maximal closed U-set size {len(S)}"
    if b == 13:
        line += f"; contains W: {Wset <= S}"
    print(line)
