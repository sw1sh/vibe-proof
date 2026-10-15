import sys
# Independent check of "no trap of width b contains the pure-ether strip" certificates.
E = ['0011', '0110', '1101', '0101', '0011', '0001', '0001']
w = sys.argv[1]; b = int(sys.argv[2]); fn = sys.argv[3]
def step(ph, s, choice):
    bit = lambda p: int(w[ph]) if p == 0 else (s >> (p - 1)) & 1
    new = 0
    for p in range(1, b):
        new |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
    nb = (1 - bit(b - 1)) if bit(b) else choice   # column b black: forced; white: free (= choice)
    new |= nb << (b - 1)
    return (ph + 1) % 4, new
def out(ph, s): return (s & 1) if w[ph] == '0' else None
def walk(node, bits):
    outs = []
    for ch in bits:
        o = out(*node)
        if o is not None: outs.append(o)
        node = step(node[0], node[1], int(ch))
    return node, outs
al = [(j, s) for j in range(7) for s in range(4) if all(E[j][ph] == w[(ph - s) % 4] for ph in range(4))]
pure = set()
for (j0, s) in al:
    for psi in range(4):
        phi = (psi + s) % 4
        pure.add((psi, sum(int(E[(j0 + p) % 7][phi]) << (p - 1) for p in range(1, b + 1))))
ok_all = True; n = 0
for line in open(fn):
    parts = line.split()
    x0 = (int(parts[1]), int(parts[2])); assert x0 in pure, 'start is not a pure-ether strip'
    path = '' if parts[4] == '-' else parts[4]; c1 = parts[6]; c2 = parts[7]
    y, _ = walk(x0, path)
    y1, u1 = walk(y, c1); y2, u2 = walk(y, c2)
    good = (y1 == y and y2 == y and u1 + u2 != u2 + u1 and len(c1) % 4 == 0 and len(c2) % 4 == 0)
    ok_all &= good; n += 1
    print('start', x0, 'path len', len(path), 'cycle lens', len(c1), len(c2), 'OK' if good else 'FAIL')
print(w, 'b=%d' % b, 'all %d certificates verified:' % n, ok_all, '; pure-ether nodes covered:', n == len(pure))
