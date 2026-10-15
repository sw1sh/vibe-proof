import sys
w = sys.argv[1]; b = int(sys.argv[2]); fn = sys.argv[3]
P = len(w)
B = set()
for line in open(fn):
    ph, s, c = map(int, line.split()); B.add((ph, s))
def succ2(ph, s):
    c = int(w[ph]); bit = lambda p: c if p == 0 else (s >> (p - 1)) & 1
    base = 0
    for p in range(1, b): base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
    nph = (ph + 1) % P
    if bit(b):
        v = base | ((1 ^ bit(b - 1)) << (b - 1)); return [(nph, v), (nph, v)]
    return [(nph, base | (bit(b - 1) << (b - 1))), (nph, base | ((1 ^ bit(b - 1)) << (b - 1)))]
rows = []
for v in sorted(B):
    a, c = succ2(*v)
    if a != c and ((a in B) != (c in B)):
        f = 0 if a in B else 1
        ph, s = v
        cols = ''.join(str((s >> (p - 1)) & 1) for p in range(1, b + 1))
        rows.append((ph, cols, f))
for ph, cols, f in sorted(rows, key=lambda r: (r[0], r[1][::-1])):
    print(ph, w[ph], cols, '| forced x =', f)
