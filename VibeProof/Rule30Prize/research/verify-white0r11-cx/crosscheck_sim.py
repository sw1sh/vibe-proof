import random
def rule(a, b, c): return a ^ (b | c)
def list_sim(r, init_bits, steps):
    w = [0] * r + [1, 1]; Q = r + 2
    row = list(init_bits) + [0] * (steps + 3)
    out = []
    for t in range(steps):
        out.append(row[0])
        d = w[t % Q]; ext = row + [0]
        row = [rule(d if p == 0 else ext[p - 1], ext[p], ext[p + 1]) for p in range(len(row))]
    return out
def int_sim(r, R, steps):
    w = [0] * r + [1, 1]; Q = r + 2; out = []
    for t in range(steps):
        out.append(R & 1)
        R = ((R << 1) | w[t % Q]) ^ (R | (R >> 1))
    return out
rng = random.Random(5)
for trial in range(30):
    r = rng.randint(5, 14); n = rng.randint(1, 40)
    bits = [rng.randint(0, 1) for _ in range(n)]
    R = sum(b << i for i, b in enumerate(bits))
    a = list_sim(r, bits, 400); b = int_sim(r, R, 400)
    assert a == b, (r, bits)
print("bit-packed simulator agrees with list simulator on 30 random cases x 400 steps")
