import sys, random
sys.path.insert(0, '.')
from hist import run, firstdef
s = lambda k: k % 2
random.seed(3)
checked = 0; bad = 0
for trial in range(20000):
    W = random.randint(4, 20)
    L = [1] + [random.getrandbits(1) for _ in range(W - 2)] + [1]
    rows, D = run(L, 200)
    for tau in range(1, len(rows) - 1, 2):
        x = rows[tau]
        if x[0] == 0 and rows[tau + 1][0] == 1:
            d = firstdef(rows[tau + 1])
            if D is None or D <= tau + d: continue   # history must survive until the next reset
            # expected: x_1=0, x_2=1, x_k=s_k for 3<=k<=d, x_{d+1} != s_{d+1}
            xx = lambda k: x[k - 1] if k <= len(x) else 0
            ok = xx(2) == 1 and all(xx(k) == s(k) for k in range(3, d + 1)) and xx(d + 1) != s(d + 1) and d % 2 == 0
            checked += 1
            if not ok: bad += 1; print('BAD', L, tau, d, x[:d+3])
print('reset configurations checked:', checked, 'violations:', bad)
