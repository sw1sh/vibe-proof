# Drive the right half (columns 1..W) by the periodic word w from a given start, record column 1.
import sys, random
import numpy as np

def run(w, init, steps):
    P = len(w); wb = np.array([int(ch) for ch in w], dtype=np.uint8)
    W = len(init) + steps + 2
    x = np.zeros(W + 2, dtype=np.uint8)   # index 0 = driver column, 1..W = right half
    x[1:1 + len(init)] = init
    col1 = np.zeros(steps, dtype=np.uint8)
    for t in range(steps):
        x[0] = wb[t % P]
        col1[t] = x[1]
        new = np.zeros_like(x)
        new[1:W + 1] = x[0:W] ^ (x[1:W + 1] | x[2:W + 2])
        x = new
    return col1

def eventual_period(seq, maxp):
    n = len(seq)
    half = n // 2
    tail = seq[half:]
    for p in range(1, maxp + 1):
        if np.array_equal(tail[p:], tail[:-p]): return p
    return None

if __name__ == '__main__':
    r = int(sys.argv[1]); steps = int(sys.argv[2]); trials = int(sys.argv[3])
    w = '0' * r + '11'
    random.seed(1)
    for k in range(trials):
        m = random.randint(5, 60)
        init = [random.randint(0, 1) for _ in range(m)] + [1]
        col1 = run(w, init, steps)
        p = eventual_period(col1, 4 * len(w) * 50)
        print(f"r={r} trial {k}: init width {m+1}, eventual period of column 1 over 2nd half: {p}")
