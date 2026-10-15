import sys
E = ['0011', '0110', '1101', '0101', '0011', '0001', '0001']
w = sys.argv[1]; b = int(sys.argv[2]); fn = sys.argv[3]; idx = int(sys.argv[4]); which = int(sys.argv[5])
lines = open(fn).read().split('\n')
parts = lines[idx].split()
x0 = (int(parts[1]), int(parts[2])); path = '' if parts[4] == '-' else parts[4]; cyc = parts[6 + which]
def step(ph, s, choice):
    bit = lambda p: int(w[ph]) if p == 0 else (s >> (p - 1)) & 1
    new = 0
    for p in range(1, b):
        new |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
    nb = (1 - bit(b - 1)) if bit(b) else choice
    return (ph + 1) % 4, new | (nb << (b - 1))
al = [(j, s) for j in range(7) for s in range(4) if all(E[j][ph] == w[(ph - s) % 4] for ph in range(4))]
node = x0
for ch in path: node = step(node[0], node[1], int(ch))
# find alignment of start
def ether_strip(j0, s, ph):
    phi = (ph + s) % 4
    return sum(int(E[(j0 + p) % 7][phi]) << (p - 1) for p in range(1, b + 1))
al0 = [a for a in al if ether_strip(a[0], a[1], x0[0]) == x0[1]][0]
print('alignment', al0, 'path', len(path), 'cycle', len(cyc))
for t, ch in enumerate(cyc):
    ph, s = node; e = ether_strip(al0[0], al0[1], ph)
    row = ''.join(('#' if (s >> (p - 1)) & 1 else '.') if ((s ^ e) >> (p - 1)) & 1 == 0 else ('X' if (s >> (p - 1)) & 1 else 'o') for p in range(1, b + 1))
    print('%3d %s|%s' % (t, w[ph], row))
    node = step(ph, s, int(ch))
