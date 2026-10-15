# Independent check of foundry phase-word-transport.md section 4 (centre word 001)
def R(x, b):
    return (((x << 1) | b) ^ (x | (x >> 1)))
def S2(x):
    return R(R(R(x, 0), 0), 1)
K = {2,4,6,8,10,12,14}
ok = True
succ = {}
for lo in K:
    outs = set()
    for outer in range(8):
        x = lo | (outer << 4)
        y = S2(x) & 15
        outs.add(y)
        if y not in K: ok = False
    succ[lo] = sorted(outs)
print("K closed under S2 (all outer bits):", ok)
print(succ)
# orbit of empty right half (finite) -- note R grows the number
x = 0; seq = []
for j in range(8):
    seq.append(x if x < 1<<20 else ('big', x & 15)); x = S2(x)
print("orbit from 0 (first steps):", seq[:4])
# sampled nearest-right bits s_j along a long orbit from 0
x = 0; s = []
for j in range(200):
    s.append(x & 1); x = S2(x)
print("sampled s:", ''.join(map(str, s[:40])))
