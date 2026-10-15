def rows(rule, T):
    W = 2*T + 5; off = T + 2; mask = (1 << W) - 1
    x = 1 << off; out = []
    for t in range(T):
        out.append(x)
        l = (x << 1) & mask; c = x; r = x >> 1; new = 0
        for k in range(8):
            if (rule >> k) & 1:
                p = (k >> 2) & 1; q = (k >> 1) & 1; s = k & 1
                new |= (l if p else ~l) & (c if q else ~c) & (r if s else ~r) & mask
        x = new & mask
    return out
a = rows(90, 600); b = rows(210, 600)
print('rule 210 seed orbit == rule 90 seed orbit for 600 steps:', a == b)
# adjacent ones never occur in rule 90 seed orbit
print('no adjacent 1s in rule 90 orbit:', all((x & (x >> 1)) == 0 for x in a))
c150 = rows(150, 600)
T = 600; off = T + 2
print('rule 150 center all ones (600 steps):', all((x >> off) & 1 for x in c150))
