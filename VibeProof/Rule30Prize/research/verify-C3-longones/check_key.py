# Right half driven by a hypothetical center sequence c (only columns >= 0 matter for columns >= 1).
# Check: after the first white cell s that follows >= 9 ones (and with every later 1->0 transition
# preceded by >= 9 ones), every white t >= s has cell(t,1) = not c(t-1).
import random
def rule(l, c, r): return l ^ (c | r)
random.seed(1)
words = ["0" + "1"*9, "0"*5 + "1"*10 + "0" + "1"*9, "0" + "1"*9 + "0" + "1"*12, "000" + "1"*11, "0"*7 + "1"*9]
for w in words:
    for trial in range(30):
        pre = [random.randint(0, 1) for _ in range(random.randint(0, 40))]   # arbitrary transient
        N = 1500
        c = (pre + [int(x) for x in w] * (N // len(w) + 2))[:N]
        width = N + 20
        right = [random.randint(0, 1) for _ in range(width)]   # columns 1..width, arbitrary
        col1 = []
        for t in range(N):
            col1.append(right[0])
            full = [c[t]] + right
            right = [rule(full[i-1], full[i], full[i+1]) for i in range(1, len(full) - 1)]
        T = len(pre)
        checked = 0
        for t in range(T + 9 + len(w), N):
            if c[t] == 0:
                assert col1[t] == 1 - c[t-1], (w, trial, t)
                checked += 1
    print(w, "ok; white cells checked in last trial:", checked)
