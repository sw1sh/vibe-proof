# w-driven right half simulation helpers (python ints as bitsets; bit p-1 = column p)
import random
def step(x, c):
    # x: int, columns 1.. ; c: column 0 value
    l = (x << 1) | c
    return l ^ (x | (x >> 1))
def run(x, w, ph, n):
    out = []
    P = len(w)
    for t in range(n):
        out.append((ph, x))
        x = step(x, int(w[ph])); ph = (ph + 1) % P
    return out
def cols(x, a, b):
    return ''.join('1' if (x >> (p - 1)) & 1 else '.' for p in range(a, b + 1))
