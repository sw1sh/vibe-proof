# Check the period-2 mirror relations on left-permutive extensions built from random right halves driven by 0101...
import random, subprocess
ok = True
for seed in range(1, 30):
    s = subprocess.run(['./rh', '01', '80', '400', str(seed), '1'], capture_output=True, text=True).stdout.strip()
    b = [int(ch) for ch in s]
    L = len(b)
    c = [t % 2 for t in range(L + 1)]
    a = [c[t+1] ^ (c[t] | b[t]) for t in range(L)]
    cols = {0: c[:L], -1: a}
    for n in range(1, 5):
        xp, xq = cols[-n], cols[-n+1]
        cols[-n-1] = [xp[t+1] ^ (xp[t] | xq[t]) for t in range(len(xp) - 1)]
    for t in range(0, L - 12, 2):  # c(t) = 0
        rel = [cols[-1][t+1] == 1, cols[-1][t] == 1 - b[t], cols[-2][t] == b[t], cols[-2][t+1] == b[t+2],
               cols[-3][t] == 1 - b[t+2], cols[-3][t+1] == 1 - b[t+2], cols[-4][t] == 0, cols[-4][t+1] == b[t+4]]
        if not all(rel): ok = False; print('fail', seed, t, rel); break
print('mirror relations hold:', ok)
