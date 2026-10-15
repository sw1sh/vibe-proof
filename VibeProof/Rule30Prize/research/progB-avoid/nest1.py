import sys
w = sys.argv[1]; bs = list(map(int, sys.argv[2:]))
prev = None
for b in bs:
    B = set()
    for line in open(f'bad_{w}_{b}.txt'):
        ph, s, c = map(int, line.split()); B.add((ph, s))
    if prev:
        pb, PB = prev
        proj = set((ph, s & ((1 << pb) - 1)) for (ph, s) in B)
        print(f"w={w} b={b}: |B|={len(B)} ratio |B_b|/|B_(b-1)|={len(B)/len(PB):.3f}  proj to b-1 covers {len(proj)}/{len(PB)} = {len(proj)/len(PB):.3f}, subset={proj <= PB}")
    prev = (b, B)
