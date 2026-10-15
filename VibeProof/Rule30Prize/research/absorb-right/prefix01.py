# Distribution of the locked-prefix length relative to a shield-orbit lock for driver w.
import sys, random
sys.path.insert(0, '.')
from leftorbit import orbit
sigma = sys.argv[1]; fz = {int(k): int(v) for k, v in (x.split(':') for x in sys.argv[2].split(','))}
d = int(sys.argv[3]); steps = int(sys.argv[4]); seed = int(sys.argv[5])
cols = orbit(sigma, fz, d); Q = len(sigma)
driver = cols[d]; lock = [cols[d - j] for j in range(1, d + 1)]
# driver period
P = next(p for p in range(1, Q + 1) if Q % p == 0 and all(driver[i] == driver[i % p] for i in range(Q)))
random.seed(seed); row = random.getrandbits(2000)
hist = [0] * (d + 2)
for t in range(steps):
    best = 0
    for shift in range(0, Q, P):
        r = (t + shift) % Q
        k = 0
        while k < d and ((row >> k) & 1) == lock[k][r]: k += 1
        best = max(best, k)
    hist[best] += 1
    row = ((row << 1) | driver[t % Q]) ^ (row | (row >> 1))
print("driver", ''.join(map(str, driver[:P])), "lock width", d, "prefix-length histogram:", hist)
