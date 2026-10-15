import sys
E = ['0011', '0110', '1101', '0101', '0011', '0001', '0001']
w = sys.argv[1]; b = int(sys.argv[2]); safe = open(sys.argv[3], 'rb').read()
al = [(j, s) for j in range(7) for s in range(4) if all(E[j][ph] == w[(ph - s) % 4] for ph in range(4))]
for (j0, s) in al:
    for psi in range(4):
        phi = (psi + s) % 4
        strip = sum(int(E[(j0 + p) % 7][phi]) << (p - 1) for p in range(1, b + 1))
        print(w, 'align', (j0, s), 'driver phase', psi, 'pure-ether strip safe?', safe[(psi << b) | strip])
