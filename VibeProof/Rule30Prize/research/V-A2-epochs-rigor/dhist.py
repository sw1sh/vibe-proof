import random, collections, sys
sys.argv = ['x', '5']
src = open('epochcheck.py').read().replace('\nmain()\n', '\n')
exec(compile(src, 'epochcheck', 'exec'))
random.seed(11)
H = collections.Counter()
for trial in range(4000):
    P = random.randint(2, 40); W = random.randint(1, 16)
    x0 = [0] + [s(k) for k in range(1, P + 1)] + [random.getrandbits(1) for _ in range(W)]
    rows, valids = history(x0, 'zero', 2 * (P + W) + 10)
    T = len(rows)
    fd = [firstdef(rows[t], 'zero', valids[t]) for t in range(T)]
    D = next((t for t in range(0, T, 2) if rows[t][1] == 0), None)
    hz = D if D is not None else T
    for tau in range(1, min(hz, T - 1), 2):
        if rows[tau][1] == 0 and tau + 1 < hz:
            H[fd[tau + 1]] += 1
print(sorted(H.items())[:20])
