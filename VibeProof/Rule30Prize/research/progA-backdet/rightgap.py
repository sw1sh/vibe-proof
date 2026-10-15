# Right half p>=1 driven by column 0 = c(t) alternating. bit (p-1) of int r = cell(t,p).
# cell(t+1,p) = cell(t,p-1) ^ (cell(t,p) | cell(t,p+1)), cell(t,0)=c(t).
import random
def step_right(r, c0, width):
    left = (r << 1) | c0          # bit (p-1) = cell(t,p-1)
    right = r >> 1                # bit (p-1) = cell(t,p+1)
    return (left ^ (r | right)) & ((1 << width) - 1)
random.seed(1)
gaps_all = {}
for trial in range(300):
    w = random.randint(1, 40)
    r = random.getrandbits(w) | (1 << (w - 1))
    a = random.getrandbits(1)  # c(t) = (a + t) % 2
    T = 3000
    width = w + T + 2
    ones_white = []
    for t in range(T):
        c0 = (a + t) % 2
        if c0 == 0 and (r & 1):
            ones_white.append(t)
        r = step_right(r, c0, width)
    gaps = [y - x for x, y in zip(ones_white, ones_white[1:]) if x > 200]
    for g in gaps: gaps_all[g] = gaps_all.get(g, 0) + 1
print(sorted(gaps_all.items()))
