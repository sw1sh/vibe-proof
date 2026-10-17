# Readouts t -> bit t of g^t(1) for every g = l . Phi with l in M_1 (finitary, depth 4, |M_1| = 2^12).
def Phi(x): return x ^ ((2 * x) | (4 * x))
D, MASK = 4, 15
phi = [Phi(v) & MASK for v in range(16)]
phinv = [0] * 16
for v in range(16): phinv[phi[v]] = v
sig = [v ^ 1 for v in range(16)]
tau = [v ^ (3 if v % 2 == 0 else 1) for v in range(16)]
comp = lambda p, q: tuple(p[q[v]] for v in range(16))      # p after q
conj = lambda f: comp(phi, comp(f, phinv))                    # Phi f Phi^-1 on the low 4 bits
gens = [tuple(sig), tuple(tau), conj(sig), conj(tau)]
group, frontier = {tuple(range(16))}, [tuple(range(16))]
while frontier:
    nxt = []
    for g in frontier:
        for s in gens:
            h = comp(s, g)
            if h not in group:
                group.add(h); nxt.append(h)
    frontier = nxt
print('|M_1| =', len(group), '= 2^%d' % (len(group).bit_length() - 1))
def eventual_period(seq, maxp=300):
    n = len(seq)
    for p in range(1, maxp + 1):
        t = n - p - 1
        while t >= 0 and seq[t + p] == seq[t]:
            t -= 1
        if t + 1 < n // 2:
            return p, t + 1
    return None
N = 1500
periodic, dens = [], []
for l in group:
    x, r = 1, []
    for t in range(N):
        r.append((x >> t) & 1)
        y = Phi(x)
        x = (y & ~MASK) | l[y & MASK]
    ep = eventual_period(r)
    dens.append(sum(r) / N)
    grows = x.bit_length() >= N  # the row keeps growing (top bit about 2t)
    if ep: periodic.append((l, ep, grows, x.bit_length()))
print('eventually periodic readouts:', len(periodic), ' of which the orbit of 1 keeps growing:', sum(1 for p in periodic if p[2]))
print('bit lengths at t = N among periodic ones:', sorted(set(p[3] for p in periodic))[:20])
for l, ep, g, bl in [p for p in periodic if p[2]][:8]: print(' growing:', l, 'period/start', ep, 'bitlen', bl)
print('density range:', min(dens), max(dens))

