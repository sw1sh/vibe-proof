# Build the lock for driver w from the leftward orbit of a shield, seed it, and test persistence.
import sys, random
sys.path.insert(0, '.')
from leftorbit import orbit
sigma = sys.argv[1]; fz = {int(k): int(v) for k, v in (x.split(':') for x in sys.argv[2].split(','))}
d = int(sys.argv[3]); trials = int(sys.argv[4]); extra = int(sys.argv[5]) if len(sys.argv) > 5 else 0
cols = orbit(sigma, fz, d)
Q = len(sigma)
# column at distance d is the driver (column 0); distance d-1 is column 1, ..., distance 0 is column d
driver = cols[d]
lock = [cols[d - j] for j in range(1, d + 1)]  # lock[j-1] = column j pattern over phases
print("driver pattern:", ''.join(map(str, driver)))
ok = 0
for tr in range(trials):
    random.seed(tr)
    # initial config at phase 0: columns 1..d from lock at phase 0, then random
    row = 0
    for j in range(d):
        if lock[j][0]: row |= 1 << j
    for j in range(d, d + 300):
        if random.random() < 0.5: row |= 1 << j
    N = 4000; col = []
    for t in range(N):
        col.append(row & 1)
        row = ((row << 1) | driver[t % Q]) ^ (row | (row >> 1))
    last = max([t for t in range(N - Q) if col[t] != col[t + Q]] or [-1])
    if last < 0: ok += 1
print(f"lock width {d}: column 1 Q-periodic from t=0 in {ok}/{trials} random completions")
