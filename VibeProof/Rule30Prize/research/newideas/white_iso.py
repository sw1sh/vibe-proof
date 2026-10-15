import sys
def step_set(S, cval, b):
    out = set()
    for s in S:
        bit = lambda p: cval if p == 0 else (s >> (p - 1)) & 1
        base = 0
        for p in range(1, b):
            base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
        if bit(b): out.add(base | ((1 ^ bit(b - 1)) << (b - 1)))
        else: out.add(base); out.add(base | (1 << (b - 1)))
    return out
b = int(sys.argv[1]); m = int(sys.argv[2]); word = sys.argv[3]
S = set(range(1 << b))
for _ in range(m): S = step_set(S, 0, b)
for label, sub in (("col1=1 at end of white run", {s for s in S if s & 1}), ("col1=0 at end of white run", {s for s in S if not s & 1})):
    T = set(sub); line = ''
    for ch in word:
        line += f"[{ch}:{''.join(map(str, sorted(set(x & 1 for x in T))))}]"
        T = step_set(T, int(ch), b)
    print(label, len(sub), line)
