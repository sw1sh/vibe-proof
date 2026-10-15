# Verifier: (1) is t001 strongly connected (so the closure of any of its states is all of it)?
# (2) random-input strip walk: 47-cell strip next to the 001 driver, i.i.d. fair right inputs, from random
#     initial strips and phases; steps until the (strip, phase) pair is in t001.
import sys, random
w = [0, 0, 1]; b = 47; mask = (1 << b) - 1
pairs = []
with open(sys.argv[1]) as f:
    f.readline()
    for line in f:
        s, l = map(int, line.split()); pairs.append((s, l))
idx = {p: i for i, p in enumerate(pairs)}
def step(r, a, z): return (((r << 1) | a) ^ (r | (r >> 1) | (z << (b - 1)))) & mask
adj = [[idx[(step(s, w[l % 3], z), (l + 1) % 21)] for z in (0, 1)] for (s, l) in pairs]
def reach(v, g):
    seen = {v}; st = [v]
    while st:
        u = st.pop()
        for x in g[u]:
            if x not in seen: seen.add(x); st.append(x)
    return seen
radj = [[] for _ in pairs]
for u, vs in enumerate(adj):
    for v in vs: radj[v].append(u)
print("t001 strongly connected:", len(reach(0, adj)) == len(pairs) and len(reach(0, radj)) == len(pairs))
inT = {(s, l % 3) for (s, l) in pairs}
rng = random.Random(int(sys.argv[2])); times = []
for k in range(int(sys.argv[3])):
    r = rng.getrandbits(b); ph = rng.randrange(3); t = 0
    while (r, ph) not in inT and t < 10**6:
        r = step(r, w[ph], rng.getrandbits(1)); ph = (ph + 1) % 3; t += 1
    times.append(t)
ent = [t for t in times if t < 10**6]
print("random-input strip walks: %d/%d entered within 1e6 steps; mean %.0f, max %d" % (len(ent), len(times), sum(ent) / max(1, len(ent)), max(ent)))
