# Check Condrey's zero-trace and one-trace fiber theorems on random right halves (truncated simulation inside light cone).
import random
random.seed(1)
def run(cells, lo, steps):
    # cells: dict pos->bit for pos in [lo, lo+len-1]; outside = 0. returns center column for t<steps
    N = len(cells); off = -lo + steps + 2
    W = N + 2*steps + 6; mask = (1 << W) - 1
    x = 0
    for i, b in enumerate(cells):
        if b: x |= 1 << (i + steps + 2)
    col = []
    for t in range(steps):
        col.append((x >> off) & 1)
        x = (((x << 1) & mask) ^ (x | (x >> 1))) & mask
    return col
bad = 0
for trial in range(300):
    D = 200  # left depth and right width
    m = random.randint(1, 12)
    R = [0] * (D + 1)
    R[m] = 1
    for j in range(m + 1, D + 1): R[j] = random.randint(0, 1)
    L = [0] * (D + 1)
    for j in range(1, D + 1):
        L[j] = 0 if j < m else (1 if j == m else j % 2)
    cells = [L[j] for j in range(D, 0, -1)] + [0] + R[1:]
    col = run(cells, -D, D // 2 - 2)
    if any(col): bad += 1
    # one-fiber: R0=1, L_j = 1 iff j even positive
    R1 = [1] + [random.randint(0, 1) for _ in range(D)]
    L1 = [0] + [1 if j % 2 == 0 else 0 for j in range(1, D + 1)]
    cells = [L1[j] for j in range(D, 0, -1)] + R1
    col = run(cells, -D, D // 2 - 2)
    if not all(col): bad += 1
print('violations:', bad)
