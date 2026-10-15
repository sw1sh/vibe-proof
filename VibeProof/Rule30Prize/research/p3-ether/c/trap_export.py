# Independent Python construction of the all-input closure of a seed strip state (width b) for a
# 3-periodic driver w, with time labels mod m.  Seed: right half driven by c(0)=1 then w^inf, at time T0.
# Checks label consistency and that column 1 at white phases is a function of the label; exports
# Lean data: keys r*m + l (l = label, l % 3 = driver phase) and the output table u (bit l).
import sys
from collections import deque
w = sys.argv[1]; b = int(sys.argv[2]); T0 = int(sys.argv[3]); m = int(sys.argv[4]); name = sys.argv[5]
out = sys.argv[6] if len(sys.argv) > 6 else None
P = len(w); MASK = (1 << b) - 1
def stp(a, z, r):
    full = a | (r << 1) | (z << (b + 1))
    return (full ^ ((full >> 1) | (full >> 2))) & MASK
# simulate the driven right half up to time T0 (exact on columns 1..b)
L = b + T0 + 4
row = 0  # bit i = column i+1, i < L
for t in range(T0):
    c = 1 if t == 0 else int(w[(t - 1) % P])
    full = c | (row << 1)
    row = (full ^ ((full >> 1) | (full >> 2))) & ((1 << L) - 1)
phi0 = (T0 - 1) % P           # c(T0) = w[phi0]
r0 = row & MASK
lab = {}
l0 = phi0 % 3                 # choose label with l % 3 == phase (m is a multiple of 3)
assert m % P == 0
lab[r0 * m + l0] = True
dq = deque([(r0, l0)]); keys = [r0 * m + l0]; seen = {(r0, l0)}; bad = False
byr = {}
while dq:
    r, l = dq.popleft()
    phi = l % P
    for z in (0, 1):
        r2 = stp(int(w[phi]), z, r); l2 = (l + 1) % m
        if (r2, l2) not in seen:
            seen.add((r2, l2)); keys.append(r2 * m + l2); dq.append((r2, l2))
# label consistency: each strip state r appears with a single label per phase class
from collections import defaultdict
labs = defaultdict(set)
for (r, l) in seen: labs[(r, l % P)].add(l)
multi = sum(1 for v in labs.values() if len(v) > 1)
u = [None] * m; outbad = False
for (r, l) in seen:
    if w[l % P] == '0':
        v = r & 1
        if u[l] is None: u[l] = v
        elif u[l] != v: outbad = True
print(f"w={w} b={b} T0={T0} m={m}: closure {len(seen)} (label,state) pairs; states with several labels: {multi}; "
      f"col1 at white phases a function of the label: {not outbad}")
print("  u =", ''.join('.' if x is None else str(x) for x in u))
# fixed columns: first column not determined by the label
firstfree = None
for p in range(b):
    val = {}
    for (r, l) in seen:
        v = (r >> p) & 1
        if val.setdefault(l, v) != v: firstfree = p + 1; break
    if firstfree: break
print("  columns 1..%d are functions of the label" % ((firstfree - 1) if firstfree else b))
if out:
    sys.set_int_max_str_digits(0)
    uP = sum((1 << l) for l in range(m) if u[l] == 1)
    st = sorted(seen, key=lambda x: (x[0], x[1]))
    idx = {v: i for i, v in enumerate(st)}
    n = len(st); lb = max(1, (m - 1).bit_length()); ib = max(1, (n - 1).bit_length())
    R = sum(r << (b * i) for i, (r, l) in enumerate(st))
    Lp = sum(l << (lb * i) for i, (r, l) in enumerate(st))
    S = 0
    for i, (r, l) in enumerate(st):
        for z in (0, 1):
            j = idx[(stp(int(w[l % P]), z, r), (l + 1) % m)]
            S |= j << (ib * (2 * i + z))
    with open(out, 'w') as f:
        f.write(f"-- trap for w = {w}: closure of the seed at T0 = {T0} (driver c(0)=1 then w), width {b}, labels mod {m}\n")
        f.write(f"-- {n} states; fields: strip {b} bits, label {lb} bits, successor index {ib} bits (index 2i+z)\n")
        f.write(f"def {name}_n : Nat := {n}\n")
        f.write(f"def {name}_lb : Nat := {lb}\n")
        f.write(f"def {name}_ib : Nat := {ib}\n")
        f.write(f"def {name}_u : Nat := {uP}\n")
        f.write(f"def {name}_R : Nat := {R}\n")
        f.write(f"def {name}_L : Nat := {Lp}\n")
        f.write(f"def {name}_S : Nat := {S}\n")
    print("written", out, n, "states", "digits R/L/S:", len(str(R)), len(str(Lp)), len(str(S)))
    with open(out.replace('.lean', '.txt'), 'w') as f:
        f.write(f"{w} {b} {m} {n}\n")
        for (r, l) in st: f.write(f"{r} {l}\n")
