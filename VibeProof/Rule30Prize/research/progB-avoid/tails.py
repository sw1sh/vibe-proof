import sys
w = sys.argv[1]
for b in map(int, sys.argv[2:]):
    B = []
    for line in open(f'bad_{w}_{b}.txt'):
        ph, s, c = map(int, line.split()); B.append((ph, s))
    def tz(s):
        k = 0
        while k < b and not (s >> (b - 1 - k)) & 1: k += 1
        return k
    def lz(s):
        k = 0
        while k < b and not (s >> k) & 1: k += 1
        return k
    def maxrun0(s):
        best = cur = 0
        for p in range(b):
            if (s >> p) & 1: cur = 0
            else: cur += 1; best = max(best, cur)
        return best
    def maxrun1(s):
        best = cur = 0
        for p in range(b):
            if (s >> p) & 1: cur += 1; best = max(best, cur)
            else: cur = 0
        return best
    print(f"w={w} b={b}: max trailing zeros {max(tz(s) for _, s in B)}, max zero run {max(maxrun0(s) for _, s in B)}, max one run {max(maxrun1(s) for _, s in B)}, all-zero state in B: {any(s == 0 for _, s in B)}")
