# Semantic sanity check (not part of the proof): exact simulation of the right half p >= 1 driven by
# c(t) = w[t mod p], from a fully random initial row of length L (random out to the light-cone edge,
# so columns 1..k at time t are exactly those of an infinite random right half for t <= L - k).
# After time K = stab - p, column 1 at each phase must equal the certified value where it is not '*'.
import sys, random
cases = {
    '00000011': (71, '11111110'), '01111111': (48, '0*******'),
    '0000000011': (57, '1111111110'), '0011111111': (70, '0110000000'), '0111111111': (40, '01010*0*0*'),
    '00000000001': (50, '00111111111'), '00000000011': (63, '11111111110'), '00000001111': (70, '11111111010'),
    '00111111111': (78, '0110*0*0*0*'), '01011111111': (63, '0100*0*0*0*'), '01111111111': (46, '01010*0*0*0'),
    '000000000001': (61, '001111111111'), '000000000011': (51, '111111111110'), '000000000101': (52, '011111111100'),
    '000111111111': (50, '0111010*0*0*'), '001111111111': (50, '0110*0*0*0*0'), '010111111111': (38, '0100*0*0*0*0'),
    '011111111111': (40, '01010*0*0*00'),
}
steps = int(sys.argv[1]); trials = int(sys.argv[2])
bad = 0
for w, (stab, pat) in cases.items():
    p = len(w); K = stab - p
    for tr in range(trials):
        rnd = random.Random(hash((w, tr)) & 0xffffffff)
        L = steps + 2
        row = [rnd.randint(0, 1) for _ in range(L)]  # row[i] = column i+1
        for t in range(steps):
            if t >= K and pat[t % p] != '*' and row[0] != int(pat[t % p]):
                bad += 1
                print('VIOLATION', w, tr, t)
                break
            d = int(w[t % p])
            # new row has one fewer valid cell on the right (light cone)
            row = [(d if i == 0 else row[i - 1]) ^ (row[i] | row[i + 1]) for i in range(len(row) - 1)]
print('violations:', bad)
